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
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___lam__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_Do_LetOrReassign_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_mutTk_x3f_7_; uint8_t v_erased_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_mutTk_x3f_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_mutTk_x3f_7_);
v_erased_8_ = lean_ctor_get_uint8(v_t_5_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5_, 1);
v___x_9_ = lean_box(v_erased_8_);
v___x_10_ = lean_apply_2(v_k_6_, v_mutTk_x3f_7_, v___x_9_);
return v___x_10_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
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
LEAN_EXPORT uint8_t l_Lean_Elab_Do_LetOrReassign_isErasedDecl(lean_object* v_letOrReassign_52_){
_start:
{
if (lean_obj_tag(v_letOrReassign_52_) == 0)
{
uint8_t v_erased_53_; 
v_erased_53_ = lean_ctor_get_uint8(v_letOrReassign_52_, sizeof(void*)*1);
return v_erased_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_isErasedDecl___boxed(lean_object* v_letOrReassign_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_Elab_Do_LetOrReassign_isErasedDecl(v_letOrReassign_55_);
lean_dec(v_letOrReassign_55_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased___redArg(lean_object* v_letOrReassign_58_, lean_object* v_vars_59_, lean_object* v_a_60_){
_start:
{
switch(lean_obj_tag(v_letOrReassign_58_))
{
case 0:
{
uint8_t v_erased_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_erased_62_ = lean_ctor_get_uint8(v_letOrReassign_58_, sizeof(void*)*1);
v___x_63_ = lean_box(v_erased_62_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
case 2:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_array_get_size(v_vars_59_);
v___x_67_ = lean_nat_dec_lt(v___x_65_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_box(v___x_67_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_array_fget_borrowed(v_vars_59_, v___x_65_);
v___x_71_ = l_Lean_TSyntax_getId(v___x_70_);
v___x_72_ = l_Lean_Elab_Do_findMutVar_x3f___redArg(v___x_71_, v_a_60_);
lean_dec(v___x_71_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_88_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_88_ == 0)
{
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_88_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_88_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
if (lean_obj_tag(v_a_73_) == 1)
{
lean_object* v_val_77_; uint8_t v_erased_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
v_val_77_ = lean_ctor_get(v_a_73_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v_a_73_, 1);
v_erased_78_ = lean_ctor_get_uint8(v_val_77_, sizeof(void*)*2);
lean_dec(v_val_77_);
v___x_79_ = lean_box(v_erased_78_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_79_);
v___x_81_ = v___x_75_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
else
{
uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
lean_dec(v_a_73_);
v___x_83_ = 0;
v___x_84_ = lean_box(v___x_83_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_84_);
v___x_86_ = v___x_75_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_a_89_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_72_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_72_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
default: 
{
uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = 0;
v___x_98_ = lean_box(v___x_97_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased___redArg___boxed(lean_object* v_letOrReassign_100_, lean_object* v_vars_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_100_, v_vars_101_, v_a_102_);
lean_dec_ref(v_a_102_);
lean_dec_ref(v_vars_101_);
lean_dec(v_letOrReassign_100_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased(lean_object* v_letOrReassign_105_, lean_object* v_vars_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_105_, v_vars_106_, v_a_107_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased___boxed(lean_object* v_letOrReassign_116_, lean_object* v_vars_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Elab_Do_isErased(v_letOrReassign_116_, v_vars_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec_ref(v_vars_117_);
lean_dec(v_letOrReassign_116_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(lean_object* v_msgData_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v_env_134_; uint8_t v___x_135_; lean_object* v_env_136_; lean_object* v___x_137_; lean_object* v_toCold_138_; lean_object* v_mctx_139_; lean_object* v_lctx_140_; lean_object* v_options_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_133_ = lean_st_ref_get(v___y_131_);
v_env_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_env_134_);
lean_dec(v___x_133_);
v___x_135_ = 0;
v_env_136_ = l_Lean_Environment_setRecordingDeps(v_env_134_, v___x_135_);
v___x_137_ = lean_st_ref_get(v___y_129_);
v_toCold_138_ = lean_ctor_get(v___y_130_, 0);
v_mctx_139_ = lean_ctor_get(v___x_137_, 0);
lean_inc_ref(v_mctx_139_);
lean_dec(v___x_137_);
v_lctx_140_ = lean_ctor_get(v___y_128_, 2);
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
lean_ctor_set(v___x_143_, 1, v_msgData_127_);
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
lean_object* v_toCold_186_; lean_object* v_currRecDepth_187_; lean_object* v_ref_188_; uint16_t v_optionFlags_189_; uint8_t v_suppressElabErrors_190_; uint8_t v_isRecordingDeps_191_; lean_object* v_ref_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_toCold_186_ = lean_ctor_get(v___y_183_, 0);
v_currRecDepth_187_ = lean_ctor_get(v___y_183_, 1);
v_ref_188_ = lean_ctor_get(v___y_183_, 2);
v_optionFlags_189_ = lean_ctor_get_uint16(v___y_183_, sizeof(void*)*3);
v_suppressElabErrors_190_ = lean_ctor_get_uint8(v___y_183_, sizeof(void*)*3 + 2);
v_isRecordingDeps_191_ = lean_ctor_get_uint8(v___y_183_, sizeof(void*)*3 + 3);
v_ref_192_ = l_Lean_replaceRef(v_ref_176_, v_ref_188_);
lean_inc(v_currRecDepth_187_);
lean_inc_ref(v_toCold_186_);
v___x_193_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_193_, 0, v_toCold_186_);
lean_ctor_set(v___x_193_, 1, v_currRecDepth_187_);
lean_ctor_set(v___x_193_, 2, v_ref_192_);
lean_ctor_set_uint16(v___x_193_, sizeof(void*)*3, v_optionFlags_189_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*3 + 2, v_suppressElabErrors_190_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*3 + 3, v_isRecordingDeps_191_);
v___x_194_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v_msg_177_, v___y_181_, v___y_182_, v___x_193_, v___y_184_);
lean_dec_ref_known(v___x_193_, 3);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg___boxed(lean_object* v_ref_195_, lean_object* v_msg_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_ref_195_, v_msg_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v_ref_195_);
return v_res_205_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__0));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__2));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(lean_object* v_as_212_, size_t v_sz_213_, size_t v_i_214_, lean_object* v_b_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_a_225_; uint8_t v___x_229_; 
v___x_229_ = lean_usize_dec_lt(v_i_214_, v_sz_213_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v_b_215_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = lean_box(0);
v_a_232_ = lean_array_uget_borrowed(v_as_212_, v_i_214_);
v___x_233_ = l_Lean_TSyntax_getId(v_a_232_);
v___x_234_ = l_Lean_Elab_Do_findMutVar_x3f___redArg(v___x_233_, v___y_216_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
if (lean_obj_tag(v_a_235_) == 0)
{
lean_dec(v___x_233_);
v_a_225_ = v___x_231_;
goto v___jp_224_;
}
else
{
lean_object* v_val_236_; uint8_t v_erased_237_; 
v_val_236_ = lean_ctor_get(v_a_235_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v_a_235_, 1);
v_erased_237_ = lean_ctor_get_uint8(v_val_236_, sizeof(void*)*2);
lean_dec(v_val_236_);
if (v_erased_237_ == 0)
{
lean_dec(v___x_233_);
v_a_225_ = v___x_231_;
goto v___jp_224_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_238_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1);
v___x_239_ = l_Lean_MessageData_ofName(v___x_233_);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_a_232_, v___x_242_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_dec_ref_known(v___x_243_, 1);
v_a_225_ = v___x_231_;
goto v___jp_224_;
}
else
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v___x_233_);
v_a_244_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_234_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_234_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
v___jp_224_:
{
size_t v___x_226_; size_t v___x_227_; 
v___x_226_ = ((size_t)1ULL);
v___x_227_ = lean_usize_add(v_i_214_, v___x_226_);
v_i_214_ = v___x_227_;
v_b_215_ = v_a_225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___boxed(lean_object* v_as_252_, lean_object* v_sz_253_, lean_object* v_i_254_, lean_object* v_b_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
size_t v_sz_boxed_264_; size_t v_i_boxed_265_; lean_object* v_res_266_; 
v_sz_boxed_264_ = lean_unbox_usize(v_sz_253_);
lean_dec(v_sz_253_);
v_i_boxed_265_ = lean_unbox_usize(v_i_254_);
lean_dec(v_i_254_);
v_res_266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(v_as_252_, v_sz_boxed_264_, v_i_boxed_265_, v_b_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec_ref(v_as_252_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars(lean_object* v_letOrReassign_267_, lean_object* v_vars_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
if (lean_obj_tag(v_letOrReassign_267_) == 2)
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Elab_Do_throwUnlessMutVarsDeclared(v_vars_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_300_; 
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___x_277_, 0);
lean_dec(v_unused_301_);
v___x_279_ = v___x_277_;
v_isShared_280_ = v_isSharedCheck_300_;
goto v_resetjp_278_;
}
else
{
lean_dec(v___x_277_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_300_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_array_get_size(v_vars_268_);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_dec_eq(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; size_t v_sz_285_; size_t v___x_286_; lean_object* v___x_287_; 
lean_del_object(v___x_279_);
v___x_284_ = lean_box(0);
v_sz_285_ = lean_array_size(v_vars_268_);
v___x_286_ = ((size_t)0ULL);
v___x_287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(v_vars_268_, v_sz_285_, v___x_286_, v___x_284_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v___x_287_, 0);
lean_dec(v_unused_295_);
v___x_289_ = v___x_287_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_dec(v___x_287_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_284_);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_284_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
return v___x_287_;
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_box(0);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_296_);
v___x_298_ = v___x_279_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
return v___x_277_;
}
}
else
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v_vars_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars___boxed(lean_object* v_letOrReassign_303_, lean_object* v_vars_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_303_, v_vars_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec_ref(v_vars_304_);
lean_dec(v_letOrReassign_303_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0(lean_object* v_00_u03b1_314_, lean_object* v_ref_315_, lean_object* v_msg_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_ref_315_, v_msg_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___boxed(lean_object* v_00_u03b1_326_, lean_object* v_ref_327_, lean_object* v_msg_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0(v_00_u03b1_326_, v_ref_327_, v_msg_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v_ref_327_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0(lean_object* v_00_u03b1_338_, lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v_msg_339_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0(v_00_u03b1_349_, v_msg_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object* v_as_360_, size_t v_sz_361_, size_t v_i_362_, lean_object* v_b_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_lt(v_i_362_, v_sz_361_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v_b_363_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; lean_object* v_a_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_374_ = lean_box(0);
v_a_375_ = lean_array_uget_borrowed(v_as_360_, v_i_362_);
v___x_376_ = l_Lean_TSyntax_getId(v_a_375_);
v___x_377_ = l_Lean_Elab_Do_registerMutVarAlias(v___x_376_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_377_) == 0)
{
size_t v___x_378_; size_t v___x_379_; 
lean_dec_ref_known(v___x_377_, 1);
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_362_, v___x_378_);
v_i_362_ = v___x_379_;
v_b_363_ = v___x_374_;
goto _start;
}
else
{
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object* v_as_381_, lean_object* v_sz_382_, lean_object* v_i_383_, lean_object* v_b_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
size_t v_sz_boxed_393_; size_t v_i_boxed_394_; lean_object* v_res_395_; 
v_sz_boxed_393_ = lean_unbox_usize(v_sz_382_);
lean_dec(v_sz_382_);
v_i_boxed_394_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_as_381_, v_sz_boxed_393_, v_i_boxed_394_, v_b_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec_ref(v_as_381_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object* v_letOrReassign_396_, lean_object* v_vars_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
if (lean_obj_tag(v_letOrReassign_396_) == 2)
{
lean_object* v___x_406_; size_t v_sz_407_; size_t v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_box(0);
v_sz_407_ = lean_array_size(v_vars_397_);
v___x_408_ = ((size_t)0ULL);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_vars_397_, v_sz_407_, v___x_408_, v___x_406_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; 
v_unused_417_ = lean_ctor_get(v___x_409_, 0);
lean_dec(v_unused_417_);
v___x_411_ = v___x_409_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_dec(v___x_409_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_406_);
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_406_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
else
{
return v___x_409_;
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_box(0);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object* v_letOrReassign_420_, lean_object* v_vars_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_420_, v_vars_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec_ref(v_vars_421_);
lean_dec(v_letOrReassign_420_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0(lean_object* v___x_431_, lean_object* v_b_432_, uint8_t v_a_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Elab_Do_withErasedProj(v___x_431_, v_b_432_, v_a_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0___boxed(lean_object* v___x_443_, lean_object* v_b_444_, lean_object* v_a_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
uint8_t v_a_720__boxed_454_; lean_object* v_res_455_; 
v_a_720__boxed_454_ = lean_unbox(v_a_445_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0(v___x_443_, v_b_444_, v_a_720__boxed_454_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec_ref(v___y_446_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(uint8_t v_a_456_, lean_object* v_as_457_, size_t v_i_458_, size_t v_stop_459_, lean_object* v_b_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_eq(v_i_458_, v_stop_459_);
if (v___x_469_ == 0)
{
size_t v___x_470_; size_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___f_474_; 
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_sub(v_i_458_, v___x_470_);
v___x_472_ = lean_array_uget_borrowed(v_as_457_, v___x_471_);
v___x_473_ = lean_box(v_a_456_);
lean_inc(v___x_472_);
v___f_474_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0___boxed), 11, 3);
lean_closure_set(v___f_474_, 0, v___x_472_);
lean_closure_set(v___f_474_, 1, v_b_460_);
lean_closure_set(v___f_474_, 2, v___x_473_);
v_i_458_ = v___x_471_;
v_b_460_ = v___f_474_;
goto _start;
}
else
{
lean_object* v___x_476_; 
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
lean_inc(v___y_463_);
lean_inc_ref(v___y_462_);
lean_inc_ref(v___y_461_);
v___x_476_ = lean_apply_8(v_b_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, lean_box(0));
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___boxed(lean_object* v_a_477_, lean_object* v_as_478_, lean_object* v_i_479_, lean_object* v_stop_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
uint8_t v_a_751__boxed_490_; size_t v_i_boxed_491_; size_t v_stop_boxed_492_; lean_object* v_res_493_; 
v_a_751__boxed_490_ = lean_unbox(v_a_477_);
v_i_boxed_491_ = lean_unbox_usize(v_i_479_);
lean_dec(v_i_479_);
v_stop_boxed_492_ = lean_unbox_usize(v_stop_480_);
lean_dec(v_stop_480_);
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(v_a_751__boxed_490_, v_as_478_, v_i_boxed_491_, v_stop_boxed_492_, v_b_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v_as_478_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___lam__0(lean_object* v_letOrReassign_494_, lean_object* v_vars_495_, lean_object* v_k_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_494_, v_vars_495_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v___x_506_; 
lean_dec_ref_known(v___x_505_, 1);
v___x_506_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_494_, v_vars_495_, v___y_497_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; uint8_t v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = lean_unbox(v_a_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec(v_a_507_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc_ref(v___y_497_);
v___x_509_ = lean_apply_8(v_k_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, lean_box(0));
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_array_get_size(v_vars_495_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_nat_dec_lt(v___x_511_, v___x_510_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_a_507_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc_ref(v___y_497_);
v___x_513_ = lean_apply_8(v_k_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, lean_box(0));
return v___x_513_;
}
else
{
size_t v___x_514_; size_t v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; 
v___x_514_ = lean_usize_of_nat(v___x_510_);
v___x_515_ = ((size_t)0ULL);
v___x_516_ = lean_unbox(v_a_507_);
lean_dec(v_a_507_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(v___x_516_, v_vars_495_, v___x_514_, v___x_515_, v_k_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_517_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_k_496_);
v_a_518_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_506_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_506_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v_k_496_);
v_a_526_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_505_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_505_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___lam__0___boxed(lean_object* v_letOrReassign_534_, lean_object* v_vars_535_, lean_object* v_k_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Elab_Do_elabWithReassignments___lam__0(v_letOrReassign_534_, v_vars_535_, v_k_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec_ref(v_vars_535_);
lean_dec(v_letOrReassign_534_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments(lean_object* v_letOrReassign_546_, lean_object* v_vars_547_, lean_object* v_k_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___f_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; 
lean_inc_ref(v_vars_547_);
lean_inc(v_letOrReassign_546_);
v___f_557_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___lam__0___boxed), 11, 3);
lean_closure_set(v___f_557_, 0, v_letOrReassign_546_);
lean_closure_set(v___f_557_, 1, v_vars_547_);
lean_closure_set(v___f_557_, 2, v_k_548_);
v___x_558_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_546_);
v___x_559_ = l_Lean_Elab_Do_LetOrReassign_isErasedDecl(v_letOrReassign_546_);
lean_dec(v_letOrReassign_546_);
v___x_560_ = l_Lean_Elab_Do_declareMutVars_x3f___redArg(v___x_558_, v_vars_547_, v___x_559_, v___f_557_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
lean_dec(v___x_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___boxed(lean_object* v_letOrReassign_561_, lean_object* v_vars_562_, lean_object* v_k_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_561_, v_vars_562_, v_k_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(lean_object* v_a_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg___boxed(lean_object* v_a_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(lean_object* v_00_u03b1_591_, lean_object* v_a_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___boxed(lean_object* v_00_u03b1_601_, lean_object* v_a_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(v_00_u03b1_601_, v_a_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_610_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_box(1);
v___x_612_ = l_Lean_MessageData_ofFormat(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__2));
v___x_617_ = l_Lean_MessageData_ofFormat(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3(lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
return v_x_618_;
}
else
{
lean_object* v_head_620_; lean_object* v_tail_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_643_; 
v_head_620_ = lean_ctor_get(v_x_619_, 0);
v_tail_621_ = lean_ctor_get(v_x_619_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_619_);
if (v_isSharedCheck_643_ == 0)
{
v___x_623_ = v_x_619_;
v_isShared_624_ = v_isSharedCheck_643_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_tail_621_);
lean_inc(v_head_620_);
lean_dec(v_x_619_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_643_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_before_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_641_; 
v_before_625_ = lean_ctor_get(v_head_620_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_head_620_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v_head_620_, 1);
lean_dec(v_unused_642_);
v___x_627_ = v_head_620_;
v_isShared_628_ = v_isSharedCheck_641_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_before_625_);
lean_dec(v_head_620_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_641_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 7);
lean_ctor_set(v___x_627_, 1, v___x_629_);
lean_ctor_set(v___x_627_, 0, v_x_618_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_x_618_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_629_);
v___x_631_ = v_reuseFailAlloc_640_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_632_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3);
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 7);
lean_ctor_set(v___x_623_, 1, v___x_632_);
lean_ctor_set(v___x_623_, 0, v___x_631_);
v___x_634_ = v___x_623_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_639_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = l_Lean_MessageData_ofSyntax(v_before_625_);
v___x_636_ = l_Lean_indentD(v___x_635_);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_634_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v_x_618_ = v___x_637_;
v_x_619_ = v_tail_621_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(lean_object* v_opts_644_, lean_object* v_opt_645_){
_start:
{
lean_object* v_name_646_; lean_object* v_defValue_647_; lean_object* v_map_648_; lean_object* v___x_649_; 
v_name_646_ = lean_ctor_get(v_opt_645_, 0);
v_defValue_647_ = lean_ctor_get(v_opt_645_, 1);
v_map_648_ = lean_ctor_get(v_opts_644_, 0);
v___x_649_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_648_, v_name_646_);
if (lean_obj_tag(v___x_649_) == 0)
{
uint8_t v___x_650_; 
v___x_650_ = lean_unbox(v_defValue_647_);
return v___x_650_;
}
else
{
lean_object* v_val_651_; 
v_val_651_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_649_, 1);
if (lean_obj_tag(v_val_651_) == 1)
{
uint8_t v_v_652_; 
v_v_652_ = lean_ctor_get_uint8(v_val_651_, 0);
lean_dec_ref_known(v_val_651_, 0);
return v_v_652_;
}
else
{
uint8_t v___x_653_; 
lean_dec(v_val_651_);
v___x_653_ = lean_unbox(v_defValue_647_);
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_654_, lean_object* v_opt_655_){
_start:
{
uint8_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(v_opts_654_, v_opt_655_);
lean_dec_ref(v_opt_655_);
lean_dec_ref(v_opts_654_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__1));
v___x_662_ = l_Lean_MessageData_ofFormat(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(lean_object* v_msgData_663_, lean_object* v_macroStack_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_665_);
v___x_668_ = l_Lean_Elab_pp_macroStack;
v___x_669_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(v___x_667_, v___x_668_);
lean_dec_ref(v___x_667_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v_macroStack_664_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v_msgData_663_);
return v___x_670_;
}
else
{
if (lean_obj_tag(v_macroStack_664_) == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_msgData_663_);
return v___x_671_;
}
else
{
lean_object* v_head_672_; lean_object* v_after_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_688_; 
v_head_672_ = lean_ctor_get(v_macroStack_664_, 0);
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
lean_ctor_set(v___x_675_, 0, v_msgData_663_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_msgData_663_);
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
v___x_685_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3(v_msgData_684_, v_macroStack_664_);
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
v___x_997_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_986_, v_a_995_, v___x_831_, v___x_831_, v___x_996_, v___y_994_, v___y_991_, v___y_988_, v___y_992_, v___y_993_, v___y_990_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref_known(v___x_997_, 1);
v___x_998_ = l_Lean_TSyntax_getId(v_x_986_);
v___x_999_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_998_, v___y_988_, v___y_992_, v___y_993_, v___y_990_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Lean_LocalDecl_type(v_a_1000_);
lean_dec(v_a_1000_);
v___x_1002_ = l_Lean_Elab_Term_exprToSyntax(v___x_1001_, v___y_994_, v___y_991_, v___y_988_, v___y_992_, v___y_993_, v___y_990_);
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
v_ref_1007_ = lean_ctor_get(v___y_993_, 2);
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
v___x_1021_ = l_Lean_Syntax_node5(v___x_1009_, v___x_838_, v___x_1010_, v___x_1013_, v___x_1018_, v___x_1020_, v___y_989_);
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
lean_dec(v___y_989_);
lean_dec(v_x_986_);
return v___x_1002_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v___y_989_);
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
lean_dec(v___y_989_);
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
v___y_988_ = v___y_1047_;
v___y_989_ = v___x_1052_;
v___y_990_ = v___y_1050_;
v___y_991_ = v___y_1046_;
v___y_992_ = v___y_1048_;
v___y_993_ = v___y_1049_;
v___y_994_ = v___y_1045_;
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
v___y_988_ = v___y_1047_;
v___y_989_ = v___x_1052_;
v___y_990_ = v___y_1050_;
v___y_991_ = v___y_1046_;
v___y_992_ = v___y_1048_;
v___y_993_ = v___y_1049_;
v___y_994_ = v___y_1045_;
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
uint8_t v___x_88364__boxed_1602_; uint8_t v___x_88367__boxed_1603_; lean_object* v_res_1604_; 
v___x_88364__boxed_1602_ = lean_unbox(v___x_1591_);
v___x_88367__boxed_1603_ = lean_unbox(v___x_1594_);
v_res_1604_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1589_, v___x_1590_, v___x_88364__boxed_1602_, v___x_1592_, v___x_1593_, v___x_88367__boxed_1603_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
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
size_t v_x_88499__boxed_1762_; size_t v_x_88500__boxed_1763_; lean_object* v_res_1764_; 
v_x_88499__boxed_1762_ = lean_unbox_usize(v_x_1758_);
lean_dec(v_x_1758_);
v_x_88500__boxed_1763_ = lean_unbox_usize(v_x_1759_);
lean_dec(v_x_1759_);
v_res_1764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1757_, v_x_88499__boxed_1762_, v_x_88500__boxed_1763_, v_x_1760_, v_x_1761_);
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
lean_object* v___x_1927_; 
v___x_1927_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1894_ = v___x_1927_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1928_; 
v___x_1928_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1894_ = v___x_1928_;
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
size_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_usize_of_nat(v___x_1907_);
lean_inc_ref(v_lctx_1906_);
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v___x_1852_, v___x_1851_, v___x_1909_, v_lctx_1906_);
v___y_1858_ = v___x_1910_;
goto v___jp_1857_;
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_a_1856_);
lean_dec_ref(v___x_1852_);
lean_dec(v_value_1837_);
v_a_1911_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1905_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1905_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v___x_1896_);
lean_dec(v_a_1856_);
lean_dec_ref(v___x_1852_);
lean_dec(v_value_1837_);
lean_dec(v_type_1836_);
v_a_1919_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1900_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1900_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v___x_1852_);
lean_dec(v_value_1837_);
lean_dec(v_type_1836_);
v_a_1929_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1855_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1855_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1937_, lean_object* v_value_1938_, lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v___x_1941_, lean_object* v___y_1942_, lean_object* v_xs_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
uint8_t v___x_88796__boxed_1951_; uint8_t v___x_88797__boxed_1952_; uint8_t v___y_88799__boxed_1953_; lean_object* v_res_1954_; 
v___x_88796__boxed_1951_ = lean_unbox(v___x_1939_);
v___x_88797__boxed_1952_ = lean_unbox(v___x_1940_);
v___y_88799__boxed_1953_ = lean_unbox(v___y_1942_);
v_res_1954_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1937_, v_value_1938_, v___x_88796__boxed_1951_, v___x_88797__boxed_1952_, v___x_1941_, v___y_88799__boxed_1953_, v_xs_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___x_1941_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1955_, lean_object* v_a_1956_, lean_object* v_letOrReassign_1957_, lean_object* v_a_1958_, uint8_t v_zeta_1959_, uint8_t v___y_1960_, lean_object* v_x_1961_, uint8_t v_usedOnly_1962_, uint8_t v___x_1963_, lean_object* v_snd_1964_, lean_object* v_h_x27_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
lean_inc_ref(v_h_x27_1965_);
v___x_1974_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1955_, v_h_x27_1965_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_dec_ref_known(v___x_1974_, 1);
v___x_1975_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_1975_, 0, v_a_1956_);
v___x_1976_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1957_, v_a_1958_, v___x_1975_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1976_) == 0)
{
if (v_zeta_1959_ == 0)
{
if (v___y_1960_ == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; 
lean_dec_ref(v_snd_1964_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1978_ = lean_unsigned_to_nat(2u);
v___x_1979_ = lean_mk_empty_array_with_capacity(v___x_1978_);
v___x_1980_ = lean_array_push(v___x_1979_, v_x_1961_);
v___x_1981_ = lean_array_push(v___x_1980_, v_h_x27_1965_);
v___x_1982_ = 1;
v___x_1983_ = l_Lean_Meta_mkLetFVars(v___x_1981_, v_a_1977_, v_usedOnly_1962_, v___y_1960_, v___x_1982_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec_ref(v___x_1981_);
return v___x_1983_;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; 
v_a_1984_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1985_ = lean_unsigned_to_nat(2u);
v___x_1986_ = lean_mk_empty_array_with_capacity(v___x_1985_);
v___x_1987_ = lean_array_push(v___x_1986_, v_x_1961_);
v___x_1988_ = lean_array_push(v___x_1987_, v_h_x27_1965_);
v___x_1989_ = 1;
v___x_1990_ = l_Lean_Meta_mkLambdaFVars(v___x_1988_, v_a_1984_, v_zeta_1959_, v___x_1963_, v_zeta_1959_, v___x_1963_, v___x_1989_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec_ref(v___x_1988_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1992_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
lean_inc_ref(v_snd_1964_);
v___x_1992_ = l_Lean_Meta_mkEqRefl(v_snd_1964_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2001_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2001_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2001_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1997_ = l_Lean_mkAppB(v_a_1991_, v_snd_1964_, v_a_1993_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_1997_);
v___x_1999_ = v___x_1995_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_dec(v_a_1991_);
lean_dec_ref(v_snd_1964_);
return v___x_1992_;
}
}
else
{
lean_dec_ref(v_snd_1964_);
return v___x_1990_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_a_2002_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_2003_ = lean_unsigned_to_nat(2u);
v___x_2004_ = lean_mk_empty_array_with_capacity(v___x_2003_);
lean_inc_ref(v___x_2004_);
v___x_2005_ = lean_array_push(v___x_2004_, v_x_1961_);
v___x_2006_ = lean_array_push(v___x_2005_, v_h_x27_1965_);
v___x_2007_ = l_Lean_Expr_abstractM(v_a_2002_, v___x_2006_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec_ref(v___x_2006_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
lean_inc_ref(v_snd_1964_);
v___x_2009_ = l_Lean_Meta_mkEqRefl(v_snd_1964_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2020_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2014_ = lean_array_push(v___x_2004_, v_snd_1964_);
v___x_2015_ = lean_array_push(v___x_2014_, v_a_2010_);
v___x_2016_ = lean_expr_instantiate_rev(v_a_2008_, v___x_2015_);
lean_dec_ref(v___x_2015_);
lean_dec(v_a_2008_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2016_);
v___x_2018_ = v___x_2012_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_dec(v_a_2008_);
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_snd_1964_);
return v___x_2009_;
}
}
else
{
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_snd_1964_);
return v___x_2007_;
}
}
}
else
{
lean_dec_ref(v_h_x27_1965_);
lean_dec_ref(v_snd_1964_);
lean_dec_ref(v_x_1961_);
return v___x_1976_;
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref(v_h_x27_1965_);
lean_dec_ref(v_snd_1964_);
lean_dec_ref(v_x_1961_);
lean_dec_ref(v_a_1958_);
lean_dec(v_letOrReassign_1957_);
lean_dec_ref(v_a_1956_);
v_a_2021_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_1974_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_1974_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object** _args){
lean_object* v_val_2029_ = _args[0];
lean_object* v_a_2030_ = _args[1];
lean_object* v_letOrReassign_2031_ = _args[2];
lean_object* v_a_2032_ = _args[3];
lean_object* v_zeta_2033_ = _args[4];
lean_object* v___y_2034_ = _args[5];
lean_object* v_x_2035_ = _args[6];
lean_object* v_usedOnly_2036_ = _args[7];
lean_object* v___x_2037_ = _args[8];
lean_object* v_snd_2038_ = _args[9];
lean_object* v_h_x27_2039_ = _args[10];
lean_object* v___y_2040_ = _args[11];
lean_object* v___y_2041_ = _args[12];
lean_object* v___y_2042_ = _args[13];
lean_object* v___y_2043_ = _args[14];
lean_object* v___y_2044_ = _args[15];
lean_object* v___y_2045_ = _args[16];
lean_object* v___y_2046_ = _args[17];
lean_object* v___y_2047_ = _args[18];
_start:
{
uint8_t v_zeta_boxed_2048_; uint8_t v___y_89018__boxed_2049_; uint8_t v_usedOnly_boxed_2050_; uint8_t v___x_89019__boxed_2051_; lean_object* v_res_2052_; 
v_zeta_boxed_2048_ = lean_unbox(v_zeta_2033_);
v___y_89018__boxed_2049_ = lean_unbox(v___y_2034_);
v_usedOnly_boxed_2050_ = lean_unbox(v_usedOnly_2036_);
v___x_89019__boxed_2051_ = lean_unbox(v___x_2037_);
v_res_2052_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_2029_, v_a_2030_, v_letOrReassign_2031_, v_a_2032_, v_zeta_boxed_2048_, v___y_89018__boxed_2049_, v_x_2035_, v_usedOnly_boxed_2050_, v___x_89019__boxed_2051_, v_snd_2038_, v_h_x27_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_id_2053_, lean_object* v_eq_x3f_2054_, lean_object* v_a_2055_, lean_object* v_letOrReassign_2056_, lean_object* v_a_2057_, uint8_t v_zeta_2058_, uint8_t v_usedOnly_2059_, lean_object* v_snd_2060_, uint8_t v___y_2061_, uint8_t v___x_2062_, lean_object* v_x_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___x_2072_; 
lean_inc_ref(v_x_2063_);
v___x_2072_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_2053_, v_x_2063_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_dec_ref_known(v___x_2072_, 1);
if (lean_obj_tag(v_eq_x3f_2054_) == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_2073_, 0, v_a_2055_);
v___x_2074_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_2056_, v_a_2057_, v___x_2073_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2074_) == 0)
{
if (v_zeta_2058_ == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
lean_dec_ref(v_snd_2060_);
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_mk_empty_array_with_capacity(v___x_2076_);
v___x_2078_ = lean_array_push(v___x_2077_, v_x_2063_);
v___x_2079_ = 1;
v___x_2080_ = l_Lean_Meta_mkLetFVars(v___x_2078_, v_a_2075_, v_usedOnly_2059_, v_zeta_2058_, v___x_2079_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec_ref(v___x_2078_);
return v___x_2080_;
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v_a_2081_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2082_ = lean_unsigned_to_nat(1u);
v___x_2083_ = lean_mk_empty_array_with_capacity(v___x_2082_);
v___x_2084_ = lean_array_push(v___x_2083_, v_x_2063_);
v___x_2085_ = l_Lean_Expr_abstractM(v_a_2081_, v___x_2084_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec_ref(v___x_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2094_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2094_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2094_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_expr_instantiate1(v_a_2086_, v_snd_2060_);
lean_dec_ref(v_snd_2060_);
lean_dec(v_a_2086_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2090_);
v___x_2092_ = v___x_2088_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_dec_ref(v_snd_2060_);
return v___x_2085_;
}
}
}
else
{
lean_dec_ref(v_x_2063_);
lean_dec_ref(v_snd_2060_);
return v___x_2074_;
}
}
else
{
lean_object* v_val_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___f_2100_; lean_object* v___x_2101_; 
v_val_2095_ = lean_ctor_get(v_eq_x3f_2054_, 0);
lean_inc_n(v_val_2095_, 2);
lean_dec_ref_known(v_eq_x3f_2054_, 1);
v___x_2096_ = lean_box(v_zeta_2058_);
v___x_2097_ = lean_box(v___y_2061_);
v___x_2098_ = lean_box(v_usedOnly_2059_);
v___x_2099_ = lean_box(v___x_2062_);
lean_inc_ref(v_snd_2060_);
lean_inc_ref_n(v_x_2063_, 2);
v___f_2100_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 19, 10);
lean_closure_set(v___f_2100_, 0, v_val_2095_);
lean_closure_set(v___f_2100_, 1, v_a_2055_);
lean_closure_set(v___f_2100_, 2, v_letOrReassign_2056_);
lean_closure_set(v___f_2100_, 3, v_a_2057_);
lean_closure_set(v___f_2100_, 4, v___x_2096_);
lean_closure_set(v___f_2100_, 5, v___x_2097_);
lean_closure_set(v___f_2100_, 6, v_x_2063_);
lean_closure_set(v___f_2100_, 7, v___x_2098_);
lean_closure_set(v___f_2100_, 8, v___x_2099_);
lean_closure_set(v___f_2100_, 9, v_snd_2060_);
v___x_2101_ = l_Lean_Meta_mkEq(v_x_2063_, v_snd_2060_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = l_Lean_Meta_mkEqRefl(v_x_2063_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
v___x_2105_ = l_Lean_TSyntax_getId(v_val_2095_);
lean_dec(v_val_2095_);
v___x_2106_ = 0;
v___x_2107_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_2105_, v_a_2102_, v_a_2104_, v___f_2100_, v___x_2062_, v___x_2106_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
return v___x_2107_;
}
else
{
lean_dec(v_a_2102_);
lean_dec_ref(v___f_2100_);
lean_dec(v_val_2095_);
return v___x_2103_;
}
}
else
{
lean_dec_ref(v___f_2100_);
lean_dec(v_val_2095_);
lean_dec_ref(v_x_2063_);
return v___x_2101_;
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v_x_2063_);
lean_dec_ref(v_snd_2060_);
lean_dec_ref(v_a_2057_);
lean_dec(v_letOrReassign_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_eq_x3f_2054_);
v_a_2108_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2072_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2072_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object** _args){
lean_object* v_id_2116_ = _args[0];
lean_object* v_eq_x3f_2117_ = _args[1];
lean_object* v_a_2118_ = _args[2];
lean_object* v_letOrReassign_2119_ = _args[3];
lean_object* v_a_2120_ = _args[4];
lean_object* v_zeta_2121_ = _args[5];
lean_object* v_usedOnly_2122_ = _args[6];
lean_object* v_snd_2123_ = _args[7];
lean_object* v___y_2124_ = _args[8];
lean_object* v___x_2125_ = _args[9];
lean_object* v_x_2126_ = _args[10];
lean_object* v___y_2127_ = _args[11];
lean_object* v___y_2128_ = _args[12];
lean_object* v___y_2129_ = _args[13];
lean_object* v___y_2130_ = _args[14];
lean_object* v___y_2131_ = _args[15];
lean_object* v___y_2132_ = _args[16];
lean_object* v___y_2133_ = _args[17];
lean_object* v___y_2134_ = _args[18];
_start:
{
uint8_t v_zeta_boxed_2135_; uint8_t v_usedOnly_boxed_2136_; uint8_t v___y_89176__boxed_2137_; uint8_t v___x_89177__boxed_2138_; lean_object* v_res_2139_; 
v_zeta_boxed_2135_ = lean_unbox(v_zeta_2121_);
v_usedOnly_boxed_2136_ = lean_unbox(v_usedOnly_2122_);
v___y_89176__boxed_2137_ = lean_unbox(v___y_2124_);
v___x_89177__boxed_2138_ = lean_unbox(v___x_2125_);
v_res_2139_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_id_2116_, v_eq_x3f_2117_, v_a_2118_, v_letOrReassign_2119_, v_a_2120_, v_zeta_boxed_2135_, v_usedOnly_boxed_2136_, v_snd_2123_, v___y_89176__boxed_2137_, v___x_89177__boxed_2138_, v_x_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(uint8_t v___x_2140_, lean_object* v_____do__lift_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2141_, v___x_2140_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object* v___x_2152_, lean_object* v_____do__lift_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
uint8_t v___x_89304__boxed_2162_; lean_object* v_res_2163_; 
v___x_89304__boxed_2162_ = lean_unbox(v___x_2152_);
v_res_2163_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v___x_89304__boxed_2162_, v_____do__lift_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v_____do__lift_2153_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(lean_object* v_term_2164_, lean_object* v___x_2165_, uint8_t v___x_2166_, lean_object* v___x_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_2164_, v___x_2165_, v___x_2166_, v___x_2166_, v___x_2167_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v_term_2177_, lean_object* v___x_2178_, lean_object* v___x_2179_, lean_object* v___x_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
uint8_t v___x_89339__boxed_2189_; lean_object* v_res_2190_; 
v___x_89339__boxed_2189_ = lean_unbox(v___x_2179_);
v_res_2190_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v_term_2177_, v___x_2178_, v___x_89339__boxed_2189_, v___x_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0(lean_object* v_stx_2191_, lean_object* v_output_2192_, lean_object* v_trees_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_lctx_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_lctx_2201_ = lean_ctor_get(v___y_2196_, 2);
lean_inc_ref(v_lctx_2201_);
v___x_2202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2202_, 0, v_lctx_2201_);
lean_ctor_set(v___x_2202_, 1, v_stx_2191_);
lean_ctor_set(v___x_2202_, 2, v_output_2192_);
v___x_2203_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v_trees_2193_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_stx_2206_, lean_object* v_output_2207_, lean_object* v_trees_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0(v_stx_2206_, v_output_2207_, v_trees_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
return v_res_2216_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_unsigned_to_nat(32u);
v___x_2218_ = lean_mk_empty_array_with_capacity(v___x_2217_);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1(void){
_start:
{
size_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2220_ = ((size_t)5ULL);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_unsigned_to_nat(32u);
v___x_2223_ = lean_mk_empty_array_with_capacity(v___x_2222_);
v___x_2224_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0);
v___x_2225_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v___x_2223_);
lean_ctor_set(v___x_2225_, 2, v___x_2221_);
lean_ctor_set(v___x_2225_, 3, v___x_2221_);
lean_ctor_set_usize(v___x_2225_, 4, v___x_2220_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v_infoState_2229_; lean_object* v_trees_2230_; lean_object* v___x_2231_; lean_object* v_infoState_2232_; lean_object* v_env_2233_; lean_object* v_nextMacroScope_2234_; lean_object* v_ngen_2235_; lean_object* v_auxDeclNGen_2236_; lean_object* v_traceState_2237_; lean_object* v_cache_2238_; lean_object* v_recordedDeps_2239_; lean_object* v_messages_2240_; lean_object* v_snapshotTasks_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2262_; 
v___x_2228_ = lean_st_ref_get(v___y_2226_);
v_infoState_2229_ = lean_ctor_get(v___x_2228_, 8);
lean_inc_ref(v_infoState_2229_);
lean_dec(v___x_2228_);
v_trees_2230_ = lean_ctor_get(v_infoState_2229_, 2);
lean_inc_ref(v_trees_2230_);
lean_dec_ref(v_infoState_2229_);
v___x_2231_ = lean_st_ref_take(v___y_2226_);
v_infoState_2232_ = lean_ctor_get(v___x_2231_, 8);
v_env_2233_ = lean_ctor_get(v___x_2231_, 0);
v_nextMacroScope_2234_ = lean_ctor_get(v___x_2231_, 1);
v_ngen_2235_ = lean_ctor_get(v___x_2231_, 2);
v_auxDeclNGen_2236_ = lean_ctor_get(v___x_2231_, 3);
v_traceState_2237_ = lean_ctor_get(v___x_2231_, 4);
v_cache_2238_ = lean_ctor_get(v___x_2231_, 5);
v_recordedDeps_2239_ = lean_ctor_get(v___x_2231_, 6);
v_messages_2240_ = lean_ctor_get(v___x_2231_, 7);
v_snapshotTasks_2241_ = lean_ctor_get(v___x_2231_, 9);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2243_ = v___x_2231_;
v_isShared_2244_ = v_isSharedCheck_2262_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_snapshotTasks_2241_);
lean_inc(v_infoState_2232_);
lean_inc(v_messages_2240_);
lean_inc(v_recordedDeps_2239_);
lean_inc(v_cache_2238_);
lean_inc(v_traceState_2237_);
lean_inc(v_auxDeclNGen_2236_);
lean_inc(v_ngen_2235_);
lean_inc(v_nextMacroScope_2234_);
lean_inc(v_env_2233_);
lean_dec(v___x_2231_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2262_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
uint8_t v_enabled_2245_; lean_object* v_assignment_2246_; lean_object* v_lazyAssignment_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2260_; 
v_enabled_2245_ = lean_ctor_get_uint8(v_infoState_2232_, sizeof(void*)*3);
v_assignment_2246_ = lean_ctor_get(v_infoState_2232_, 0);
v_lazyAssignment_2247_ = lean_ctor_get(v_infoState_2232_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_infoState_2232_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; 
v_unused_2261_ = lean_ctor_get(v_infoState_2232_, 2);
lean_dec(v_unused_2261_);
v___x_2249_ = v_infoState_2232_;
v_isShared_2250_ = v_isSharedCheck_2260_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_lazyAssignment_2247_);
lean_inc(v_assignment_2246_);
lean_dec(v_infoState_2232_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2260_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2251_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 2, v___x_2251_);
v___x_2253_ = v___x_2249_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_assignment_2246_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_lazyAssignment_2247_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v___x_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2259_, sizeof(void*)*3, v_enabled_2245_);
v___x_2253_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 8, v___x_2253_);
v___x_2255_ = v___x_2243_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_env_2233_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_nextMacroScope_2234_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_ngen_2235_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_auxDeclNGen_2236_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_traceState_2237_);
lean_ctor_set(v_reuseFailAlloc_2258_, 5, v_cache_2238_);
lean_ctor_set(v_reuseFailAlloc_2258_, 6, v_recordedDeps_2239_);
lean_ctor_set(v_reuseFailAlloc_2258_, 7, v_messages_2240_);
lean_ctor_set(v_reuseFailAlloc_2258_, 8, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2258_, 9, v_snapshotTasks_2241_);
v___x_2255_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_st_ref_put(v___y_2226_, v___x_2255_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v_trees_2230_);
return v___x_2257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___boxed(lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(v___y_2263_);
lean_dec(v___y_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(lean_object* v___y_2266_, lean_object* v_mkInfoTree_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v_a_2273_, lean_object* v_a_x3f_2274_){
_start:
{
lean_object* v___x_2276_; lean_object* v_infoState_2277_; lean_object* v_trees_2278_; lean_object* v___x_2279_; 
v___x_2276_ = lean_st_ref_get(v___y_2266_);
v_infoState_2277_ = lean_ctor_get(v___x_2276_, 8);
lean_inc_ref(v_infoState_2277_);
lean_dec(v___x_2276_);
v_trees_2278_ = lean_ctor_get(v_infoState_2277_, 2);
lean_inc_ref(v_trees_2278_);
lean_dec_ref(v_infoState_2277_);
lean_inc(v___y_2266_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2268_);
v___x_2279_ = lean_apply_8(v_mkInfoTree_2267_, v_trees_2278_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2266_, lean_box(0));
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2319_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2319_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2319_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v_infoState_2285_; lean_object* v_env_2286_; lean_object* v_nextMacroScope_2287_; lean_object* v_ngen_2288_; lean_object* v_auxDeclNGen_2289_; lean_object* v_traceState_2290_; lean_object* v_cache_2291_; lean_object* v_recordedDeps_2292_; lean_object* v_messages_2293_; lean_object* v_snapshotTasks_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2318_; 
v___x_2284_ = lean_st_ref_take(v___y_2266_);
v_infoState_2285_ = lean_ctor_get(v___x_2284_, 8);
v_env_2286_ = lean_ctor_get(v___x_2284_, 0);
v_nextMacroScope_2287_ = lean_ctor_get(v___x_2284_, 1);
v_ngen_2288_ = lean_ctor_get(v___x_2284_, 2);
v_auxDeclNGen_2289_ = lean_ctor_get(v___x_2284_, 3);
v_traceState_2290_ = lean_ctor_get(v___x_2284_, 4);
v_cache_2291_ = lean_ctor_get(v___x_2284_, 5);
v_recordedDeps_2292_ = lean_ctor_get(v___x_2284_, 6);
v_messages_2293_ = lean_ctor_get(v___x_2284_, 7);
v_snapshotTasks_2294_ = lean_ctor_get(v___x_2284_, 9);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2296_ = v___x_2284_;
v_isShared_2297_ = v_isSharedCheck_2318_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_snapshotTasks_2294_);
lean_inc(v_infoState_2285_);
lean_inc(v_messages_2293_);
lean_inc(v_recordedDeps_2292_);
lean_inc(v_cache_2291_);
lean_inc(v_traceState_2290_);
lean_inc(v_auxDeclNGen_2289_);
lean_inc(v_ngen_2288_);
lean_inc(v_nextMacroScope_2287_);
lean_inc(v_env_2286_);
lean_dec(v___x_2284_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2318_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
uint8_t v_enabled_2298_; lean_object* v_assignment_2299_; lean_object* v_lazyAssignment_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2316_; 
v_enabled_2298_ = lean_ctor_get_uint8(v_infoState_2285_, sizeof(void*)*3);
v_assignment_2299_ = lean_ctor_get(v_infoState_2285_, 0);
v_lazyAssignment_2300_ = lean_ctor_get(v_infoState_2285_, 1);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_infoState_2285_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v_infoState_2285_, 2);
lean_dec(v_unused_2317_);
v___x_2302_ = v_infoState_2285_;
v_isShared_2303_ = v_isSharedCheck_2316_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_lazyAssignment_2300_);
lean_inc(v_assignment_2299_);
lean_dec(v_infoState_2285_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2316_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2304_ = lean_box(0);
v___x_2305_ = l_Lean_PersistentArray_push___redArg(v_a_2273_, v_a_2280_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 2, v___x_2305_);
v___x_2307_ = v___x_2302_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_assignment_2299_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_lazyAssignment_2300_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v___x_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2315_, sizeof(void*)*3, v_enabled_2298_);
v___x_2307_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2309_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 8, v___x_2307_);
v___x_2309_ = v___x_2296_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_env_2286_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_nextMacroScope_2287_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_ngen_2288_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_auxDeclNGen_2289_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_traceState_2290_);
lean_ctor_set(v_reuseFailAlloc_2314_, 5, v_cache_2291_);
lean_ctor_set(v_reuseFailAlloc_2314_, 6, v_recordedDeps_2292_);
lean_ctor_set(v_reuseFailAlloc_2314_, 7, v_messages_2293_);
lean_ctor_set(v_reuseFailAlloc_2314_, 8, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2314_, 9, v_snapshotTasks_2294_);
v___x_2309_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2310_ = lean_st_ref_put(v___y_2266_, v___x_2309_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2304_);
v___x_2312_ = v___x_2282_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2304_);
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
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref(v_a_2273_);
v_a_2320_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2279_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2279_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v___y_2328_, lean_object* v_mkInfoTree_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v_a_2335_, lean_object* v_a_x3f_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(v___y_2328_, v_mkInfoTree_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v_a_2335_, v_a_x3f_2336_);
lean_dec(v_a_x3f_2336_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2328_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(lean_object* v_x_2339_, lean_object* v_mkInfoTree_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; lean_object* v_infoState_2349_; uint8_t v_enabled_2350_; 
v___x_2348_ = lean_st_ref_get(v___y_2346_);
v_infoState_2349_ = lean_ctor_get(v___x_2348_, 8);
lean_inc_ref(v_infoState_2349_);
lean_dec(v___x_2348_);
v_enabled_2350_ = lean_ctor_get_uint8(v_infoState_2349_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2349_);
if (v_enabled_2350_ == 0)
{
lean_object* v___x_2351_; 
lean_dec_ref(v_mkInfoTree_2340_);
lean_inc(v___y_2346_);
lean_inc_ref(v___y_2345_);
lean_inc(v___y_2344_);
lean_inc_ref(v___y_2343_);
lean_inc(v___y_2342_);
lean_inc_ref(v___y_2341_);
v___x_2351_ = lean_apply_7(v_x_2339_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, lean_box(0));
return v___x_2351_;
}
else
{
lean_object* v___x_2352_; lean_object* v_a_2353_; lean_object* v_r_2354_; 
v___x_2352_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(v___y_2346_);
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref(v___x_2352_);
lean_inc(v___y_2346_);
lean_inc_ref(v___y_2345_);
lean_inc(v___y_2344_);
lean_inc_ref(v___y_2343_);
lean_inc(v___y_2342_);
lean_inc_ref(v___y_2341_);
v_r_2354_ = lean_apply_7(v_x_2339_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, lean_box(0));
if (lean_obj_tag(v_r_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2379_; 
v_a_2355_ = lean_ctor_get(v_r_2354_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_r_2354_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2357_ = v_r_2354_;
v_isShared_2358_ = v_isSharedCheck_2379_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v_r_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2379_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
lean_inc(v_a_2355_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set_tag(v___x_2357_, 1);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(v___y_2346_, v_mkInfoTree_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v_a_2353_, v___x_2360_);
lean_dec_ref(v___x_2360_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v___x_2361_, 0);
lean_dec(v_unused_2369_);
v___x_2363_ = v___x_2361_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_dec(v___x_2361_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v_a_2355_);
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2355_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec(v_a_2355_);
v_a_2370_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2361_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2361_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_a_2380_ = lean_ctor_get(v_r_2354_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v_r_2354_, 1);
v___x_2381_ = lean_box(0);
v___x_2382_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(v___y_2346_, v_mkInfoTree_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v_a_2353_, v___x_2381_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v___x_2382_, 0);
lean_dec(v_unused_2390_);
v___x_2384_ = v___x_2382_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_dec(v___x_2382_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set_tag(v___x_2384_, 1);
lean_ctor_set(v___x_2384_, 0, v_a_2380_);
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2380_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_a_2380_);
v_a_2391_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2382_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2382_);
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
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_x_2399_, lean_object* v_mkInfoTree_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(v_x_2399_, v_mkInfoTree_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(lean_object* v_stx_2409_, lean_object* v_output_2410_, lean_object* v_x_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___f_2419_; lean_object* v___x_2420_; 
v___f_2419_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2419_, 0, v_stx_2409_);
lean_closure_set(v___f_2419_, 1, v_output_2410_);
v___x_2420_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(v_x_2411_, v___f_2419_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___boxed(lean_object* v_stx_2421_, lean_object* v_output_2422_, lean_object* v_x_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_stx_2421_, v_output_2422_, v_x_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0(lean_object* v_x_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; 
lean_inc_ref(v___y_2433_);
v___x_2441_ = lean_apply_8(v_x_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, lean_box(0));
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0___boxed(lean_object* v_x_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0(v_x_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec_ref(v___y_2443_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(lean_object* v_beforeStx_2452_, lean_object* v_afterStx_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___f_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
lean_inc_ref(v___y_2455_);
v___f_2463_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2463_, 0, v_x_2454_);
lean_closure_set(v___f_2463_, 1, v___y_2455_);
lean_inc(v_afterStx_2453_);
lean_inc(v_beforeStx_2452_);
v___x_2464_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2464_, 0, lean_box(0));
lean_closure_set(v___x_2464_, 1, v_beforeStx_2452_);
lean_closure_set(v___x_2464_, 2, v_afterStx_2453_);
lean_closure_set(v___x_2464_, 3, v___f_2463_);
v___x_2465_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_beforeStx_2452_, v_afterStx_2453_, v___x_2464_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2465_) == 0)
{
return v___x_2465_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___boxed(lean_object* v_beforeStx_2474_, lean_object* v_afterStx_2475_, lean_object* v_x_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_beforeStx_2474_, v_afterStx_2475_, v_x_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v___y_2477_);
return v_res_2485_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__1));
v___x_2489_ = l_String_toRawSubstring_x27(v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_rhs_2511_, uint8_t v___x_2512_, lean_object* v_config_2513_, lean_object* v_a_2514_, uint8_t v___x_2515_, lean_object* v___x_2516_, lean_object* v___x_2517_, lean_object* v___x_2518_, lean_object* v___f_2519_, lean_object* v___x_2520_, lean_object* v_body_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_term_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v_ref_2538_; lean_object* v___y_2539_; lean_object* v_toCold_2545_; lean_object* v_ref_2546_; lean_object* v_quotContext_2547_; lean_object* v_currMacroScope_2548_; lean_object* v_ref_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_eq_x3f_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_toCold_2545_ = lean_ctor_get(v___y_2527_, 0);
v_ref_2546_ = lean_ctor_get(v___y_2527_, 2);
v_quotContext_2547_ = lean_ctor_get(v_toCold_2545_, 8);
v_currMacroScope_2548_ = lean_ctor_get(v_toCold_2545_, 9);
v_ref_2549_ = l_Lean_replaceRef(v_rhs_2511_, v_ref_2546_);
v___x_2550_ = l_Lean_SourceInfo_fromRef(v_ref_2549_, v___x_2512_);
lean_dec(v_ref_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__0));
lean_inc_n(v___x_2550_, 2);
v___x_2552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2);
v_eq_x3f_2554_ = lean_ctor_get(v_config_2513_, 0);
lean_inc(v_eq_x3f_2554_);
lean_dec_ref(v_config_2513_);
v___x_2555_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__3));
lean_inc(v_currMacroScope_2548_);
lean_inc(v_quotContext_2547_);
v___x_2556_ = l_Lean_addMacroScope(v_quotContext_2547_, v___x_2555_, v_currMacroScope_2548_);
v___x_2557_ = lean_box(0);
lean_inc(v___x_2556_);
v___x_2558_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2550_);
lean_ctor_set(v___x_2558_, 1, v___x_2553_);
lean_ctor_set(v___x_2558_, 2, v___x_2556_);
lean_ctor_set(v___x_2558_, 3, v___x_2557_);
v___x_2559_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__4));
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
lean_inc_ref(v___x_2516_);
v___x_2560_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node2(v___x_2550_, v___x_2560_, v___x_2552_, v___x_2558_);
if (lean_obj_tag(v_eq_x3f_2554_) == 1)
{
lean_object* v_val_2562_; lean_object* v___x_2563_; 
v_val_2562_ = lean_ctor_get(v_eq_x3f_2554_, 0);
lean_inc(v_val_2562_);
lean_dec_ref_known(v_eq_x3f_2554_, 1);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v_ref_2546_);
v___x_2563_ = lean_apply_9(v___f_2519_, v_ref_2546_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, lean_box(0));
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc_n(v_a_2564_, 23);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5));
lean_inc_ref_n(v___x_2518_, 5);
lean_inc_ref_n(v___x_2517_, 5);
lean_inc_ref_n(v___x_2516_, 5);
v___x_2566_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2565_);
v___x_2567_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6));
v___x_2568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2568_, 0, v_a_2564_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_a_2564_);
lean_ctor_set(v___x_2569_, 1, v___x_2551_);
v___x_2570_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2570_, 0, v_a_2564_);
lean_ctor_set(v___x_2570_, 1, v___x_2553_);
lean_ctor_set(v___x_2570_, 2, v___x_2556_);
lean_ctor_set(v___x_2570_, 3, v___x_2557_);
v___x_2571_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_a_2564_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_2574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_a_2564_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8));
v___x_2576_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2575_);
v___x_2577_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9));
v___x_2578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2578_, 0, v_a_2564_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_2580_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2581_, 0, v_a_2564_);
lean_ctor_set(v___x_2581_, 1, v___x_2579_);
v___x_2582_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2583_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2584_, 0, v_a_2564_);
lean_ctor_set(v___x_2584_, 1, v___x_2582_);
lean_ctor_set(v___x_2584_, 2, v___x_2583_);
v___x_2585_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11));
v___x_2586_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2585_);
v___x_2587_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2588_, 0, v_a_2564_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Lean_Syntax_node2(v_a_2564_, v___x_2582_, v_val_2562_, v___x_2588_);
v___x_2590_ = l_Lean_Syntax_node2(v_a_2564_, v___x_2586_, v___x_2589_, v___x_2561_);
v___x_2591_ = l_Lean_Syntax_node1(v_a_2564_, v___x_2582_, v___x_2590_);
v___x_2592_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_2593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2593_, 0, v_a_2564_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13));
v___x_2595_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2594_);
v___x_2596_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14));
v___x_2597_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2596_);
v___x_2598_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_2599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_a_2564_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = l_Lean_Syntax_node1(v_a_2564_, v___x_2582_, v___x_2520_);
v___x_2601_ = l_Lean_Syntax_node1(v_a_2564_, v___x_2582_, v___x_2600_);
v___x_2602_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_2603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2603_, 0, v_a_2564_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = l_Lean_Syntax_node4(v_a_2564_, v___x_2597_, v___x_2599_, v___x_2601_, v___x_2603_, v_body_2521_);
v___x_2605_ = l_Lean_Syntax_node1(v_a_2564_, v___x_2582_, v___x_2604_);
v___x_2606_ = l_Lean_Syntax_node1(v_a_2564_, v___x_2595_, v___x_2605_);
lean_inc_ref(v___x_2584_);
v___x_2607_ = l_Lean_Syntax_node6(v_a_2564_, v___x_2580_, v___x_2581_, v___x_2584_, v___x_2584_, v___x_2591_, v___x_2593_, v___x_2606_);
lean_inc_ref(v___x_2574_);
lean_inc_ref(v___x_2570_);
lean_inc_ref(v___x_2569_);
v___x_2608_ = l_Lean_Syntax_node5(v_a_2564_, v___x_2576_, v___x_2578_, v___x_2569_, v___x_2570_, v___x_2574_, v___x_2607_);
v___x_2609_ = l_Lean_Syntax_node7(v_a_2564_, v___x_2566_, v___x_2568_, v___x_2569_, v___x_2570_, v___x_2572_, v_rhs_2511_, v___x_2574_, v___x_2608_);
lean_inc(v_ref_2546_);
v_term_2531_ = v___x_2609_;
v___y_2532_ = v___y_2522_;
v___y_2533_ = v___y_2523_;
v___y_2534_ = v___y_2524_;
v___y_2535_ = v___y_2525_;
v___y_2536_ = v___y_2526_;
v___y_2537_ = v___y_2527_;
v_ref_2538_ = v_ref_2546_;
v___y_2539_ = v___y_2528_;
goto v___jp_2530_;
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_val_2562_);
lean_dec(v___x_2561_);
lean_dec(v___x_2556_);
lean_dec(v_body_2521_);
lean_dec(v___x_2520_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v_a_2514_);
lean_dec(v_rhs_2511_);
v_a_2610_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2563_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2563_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v___x_2618_; 
lean_dec(v_eq_x3f_2554_);
lean_inc_ref(v_a_2514_);
v___x_2618_ = l_Lean_Elab_Term_exprToSyntax(v_a_2514_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v_ref_2546_);
v___x_2620_ = lean_apply_9(v___f_2519_, v_ref_2546_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, lean_box(0));
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc_n(v_a_2621_, 32);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5));
lean_inc_ref_n(v___x_2518_, 8);
lean_inc_ref_n(v___x_2517_, 8);
lean_inc_ref_n(v___x_2516_, 8);
v___x_2623_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2622_);
v___x_2624_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6));
v___x_2625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2625_, 0, v_a_2621_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2626_, 0, v_a_2621_);
lean_ctor_set(v___x_2626_, 1, v___x_2551_);
v___x_2627_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2627_, 0, v_a_2621_);
lean_ctor_set(v___x_2627_, 1, v___x_2553_);
lean_ctor_set(v___x_2627_, 2, v___x_2556_);
lean_ctor_set(v___x_2627_, 3, v___x_2557_);
v___x_2628_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2629_, 0, v_a_2621_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_2631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2631_, 0, v_a_2621_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8));
v___x_2633_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2632_);
v___x_2634_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9));
v___x_2635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2635_, 0, v_a_2621_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_2637_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v_a_2621_);
lean_ctor_set(v___x_2638_, 1, v___x_2636_);
v___x_2639_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2640_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2641_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2641_, 0, v_a_2621_);
lean_ctor_set(v___x_2641_, 1, v___x_2639_);
lean_ctor_set(v___x_2641_, 2, v___x_2640_);
v___x_2642_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__17));
v___x_2643_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2642_);
v___x_2644_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2645_, 0, v_a_2621_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2646_, 0, v_a_2621_);
lean_ctor_set(v___x_2646_, 1, v___x_2642_);
v___x_2647_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__18));
v___x_2648_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2647_);
v___x_2649_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__19));
v___x_2650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2650_, 0, v_a_2621_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__20));
v___x_2652_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2651_);
v___x_2653_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_2654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2654_, 0, v_a_2621_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = l_Lean_Syntax_node1(v_a_2621_, v___x_2652_, v___x_2654_);
v___x_2656_ = l_Lean_Syntax_node1(v_a_2621_, v___x_2639_, v___x_2655_);
v___x_2657_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__22));
v___x_2658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_a_2621_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
lean_inc_ref_n(v___x_2641_, 2);
v___x_2659_ = l_Lean_Syntax_node5(v_a_2621_, v___x_2648_, v___x_2650_, v___x_2656_, v___x_2641_, v___x_2658_, v_a_2619_);
v___x_2660_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2661_, 0, v_a_2621_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
lean_inc_ref(v___x_2629_);
v___x_2662_ = l_Lean_Syntax_node5(v_a_2621_, v___x_2643_, v___x_2645_, v___x_2646_, v___x_2629_, v___x_2659_, v___x_2661_);
v___x_2663_ = l_Lean_Syntax_node1(v_a_2621_, v___x_2639_, v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11));
v___x_2665_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2664_);
v___x_2666_ = l_Lean_Syntax_node2(v_a_2621_, v___x_2665_, v___x_2641_, v___x_2561_);
v___x_2667_ = l_Lean_Syntax_node1(v_a_2621_, v___x_2639_, v___x_2666_);
v___x_2668_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_2669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_a_2621_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13));
v___x_2671_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2670_);
v___x_2672_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14));
v___x_2673_ = l_Lean_Name_mkStr4(v___x_2516_, v___x_2517_, v___x_2518_, v___x_2672_);
v___x_2674_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_2675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_a_2621_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = l_Lean_Syntax_node1(v_a_2621_, v___x_2639_, v___x_2520_);
v___x_2677_ = l_Lean_Syntax_node1(v_a_2621_, v___x_2639_, v___x_2676_);
v___x_2678_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_2679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2679_, 0, v_a_2621_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = l_Lean_Syntax_node4(v_a_2621_, v___x_2673_, v___x_2675_, v___x_2677_, v___x_2679_, v_body_2521_);
v___x_2681_ = l_Lean_Syntax_node1(v_a_2621_, v___x_2639_, v___x_2680_);
v___x_2682_ = l_Lean_Syntax_node1(v_a_2621_, v___x_2671_, v___x_2681_);
v___x_2683_ = l_Lean_Syntax_node6(v_a_2621_, v___x_2637_, v___x_2638_, v___x_2641_, v___x_2663_, v___x_2667_, v___x_2669_, v___x_2682_);
lean_inc_ref(v___x_2631_);
lean_inc_ref(v___x_2627_);
lean_inc_ref(v___x_2626_);
v___x_2684_ = l_Lean_Syntax_node5(v_a_2621_, v___x_2633_, v___x_2635_, v___x_2626_, v___x_2627_, v___x_2631_, v___x_2683_);
v___x_2685_ = l_Lean_Syntax_node7(v_a_2621_, v___x_2623_, v___x_2625_, v___x_2626_, v___x_2627_, v___x_2629_, v_rhs_2511_, v___x_2631_, v___x_2684_);
lean_inc(v_ref_2546_);
v_term_2531_ = v___x_2685_;
v___y_2532_ = v___y_2522_;
v___y_2533_ = v___y_2523_;
v___y_2534_ = v___y_2524_;
v___y_2535_ = v___y_2525_;
v___y_2536_ = v___y_2526_;
v___y_2537_ = v___y_2527_;
v_ref_2538_ = v_ref_2546_;
v___y_2539_ = v___y_2528_;
goto v___jp_2530_;
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_a_2619_);
lean_dec(v___x_2561_);
lean_dec(v___x_2556_);
lean_dec(v_body_2521_);
lean_dec(v___x_2520_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v_a_2514_);
lean_dec(v_rhs_2511_);
v_a_2686_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2620_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2620_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v___x_2561_);
lean_dec(v___x_2556_);
lean_dec(v_body_2521_);
lean_dec(v___x_2520_);
lean_dec_ref(v___f_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___x_2516_);
lean_dec_ref(v_a_2514_);
lean_dec(v_rhs_2511_);
v_a_2694_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2618_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2618_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
v___jp_2530_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; 
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_a_2514_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_box(v___x_2515_);
lean_inc(v_term_2531_);
v___f_2543_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 12, 4);
lean_closure_set(v___f_2543_, 0, v_term_2531_);
lean_closure_set(v___f_2543_, 1, v___x_2540_);
lean_closure_set(v___f_2543_, 2, v___x_2542_);
lean_closure_set(v___f_2543_, 3, v___x_2541_);
v___x_2544_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_ref_2538_, v_term_2531_, v___f_2543_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2539_);
return v___x_2544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object** _args){
lean_object* v_rhs_2702_ = _args[0];
lean_object* v___x_2703_ = _args[1];
lean_object* v_config_2704_ = _args[2];
lean_object* v_a_2705_ = _args[3];
lean_object* v___x_2706_ = _args[4];
lean_object* v___x_2707_ = _args[5];
lean_object* v___x_2708_ = _args[6];
lean_object* v___x_2709_ = _args[7];
lean_object* v___f_2710_ = _args[8];
lean_object* v___x_2711_ = _args[9];
lean_object* v_body_2712_ = _args[10];
lean_object* v___y_2713_ = _args[11];
lean_object* v___y_2714_ = _args[12];
lean_object* v___y_2715_ = _args[13];
lean_object* v___y_2716_ = _args[14];
lean_object* v___y_2717_ = _args[15];
lean_object* v___y_2718_ = _args[16];
lean_object* v___y_2719_ = _args[17];
lean_object* v___y_2720_ = _args[18];
_start:
{
uint8_t v___x_89868__boxed_2721_; uint8_t v___x_89870__boxed_2722_; lean_object* v_res_2723_; 
v___x_89868__boxed_2721_ = lean_unbox(v___x_2703_);
v___x_89870__boxed_2722_ = lean_unbox(v___x_2706_);
v_res_2723_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_rhs_2702_, v___x_89868__boxed_2721_, v_config_2704_, v_a_2705_, v___x_89870__boxed_2722_, v___x_2707_, v___x_2708_, v___x_2709_, v___f_2710_, v___x_2711_, v_body_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2723_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2724_; double v___x_2725_; 
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = lean_float_of_nat(v___x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_cls_2728_, lean_object* v_msg_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_ref_2735_; lean_object* v___x_2736_; lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2782_; 
v_ref_2735_ = lean_ctor_get(v___y_2732_, 2);
v___x_2736_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(v_msg_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2782_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2782_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v_traceState_2742_; lean_object* v_env_2743_; lean_object* v_nextMacroScope_2744_; lean_object* v_ngen_2745_; lean_object* v_auxDeclNGen_2746_; lean_object* v_cache_2747_; lean_object* v_recordedDeps_2748_; lean_object* v_messages_2749_; lean_object* v_infoState_2750_; lean_object* v_snapshotTasks_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2781_; 
v___x_2741_ = lean_st_ref_take(v___y_2733_);
v_traceState_2742_ = lean_ctor_get(v___x_2741_, 4);
v_env_2743_ = lean_ctor_get(v___x_2741_, 0);
v_nextMacroScope_2744_ = lean_ctor_get(v___x_2741_, 1);
v_ngen_2745_ = lean_ctor_get(v___x_2741_, 2);
v_auxDeclNGen_2746_ = lean_ctor_get(v___x_2741_, 3);
v_cache_2747_ = lean_ctor_get(v___x_2741_, 5);
v_recordedDeps_2748_ = lean_ctor_get(v___x_2741_, 6);
v_messages_2749_ = lean_ctor_get(v___x_2741_, 7);
v_infoState_2750_ = lean_ctor_get(v___x_2741_, 8);
v_snapshotTasks_2751_ = lean_ctor_get(v___x_2741_, 9);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2753_ = v___x_2741_;
v_isShared_2754_ = v_isSharedCheck_2781_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_snapshotTasks_2751_);
lean_inc(v_infoState_2750_);
lean_inc(v_messages_2749_);
lean_inc(v_recordedDeps_2748_);
lean_inc(v_cache_2747_);
lean_inc(v_traceState_2742_);
lean_inc(v_auxDeclNGen_2746_);
lean_inc(v_ngen_2745_);
lean_inc(v_nextMacroScope_2744_);
lean_inc(v_env_2743_);
lean_dec(v___x_2741_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2781_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
uint64_t v_tid_2755_; lean_object* v_traces_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2780_; 
v_tid_2755_ = lean_ctor_get_uint64(v_traceState_2742_, sizeof(void*)*1);
v_traces_2756_ = lean_ctor_get(v_traceState_2742_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_traceState_2742_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2758_ = v_traceState_2742_;
v_isShared_2759_ = v_isSharedCheck_2780_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_traces_2756_);
lean_dec(v_traceState_2742_);
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
lean_ctor_set(v___x_2765_, 0, v_cls_2728_);
lean_ctor_set(v___x_2765_, 1, v___x_2761_);
lean_ctor_set(v___x_2765_, 2, v___x_2764_);
lean_ctor_set_float(v___x_2765_, sizeof(void*)*3, v___x_2762_);
lean_ctor_set_float(v___x_2765_, sizeof(void*)*3 + 8, v___x_2762_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*3 + 16, v___x_2763_);
v___x_2766_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1));
v___x_2767_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v_a_2737_);
lean_ctor_set(v___x_2767_, 2, v___x_2766_);
lean_inc(v_ref_2735_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_ref_2735_);
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
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_env_2743_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_nextMacroScope_2744_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_ngen_2745_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_auxDeclNGen_2746_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2778_, 5, v_cache_2747_);
lean_ctor_set(v_reuseFailAlloc_2778_, 6, v_recordedDeps_2748_);
lean_ctor_set(v_reuseFailAlloc_2778_, 7, v_messages_2749_);
lean_ctor_set(v_reuseFailAlloc_2778_, 8, v_infoState_2750_);
lean_ctor_set(v_reuseFailAlloc_2778_, 9, v_snapshotTasks_2751_);
v___x_2773_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = lean_st_ref_put(v___y_2733_, v___x_2773_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2760_);
v___x_2776_ = v___x_2739_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(lean_object* v_env_2791_, lean_object* v_currNamespace_2792_, lean_object* v_openDecls_2793_, lean_object* v_n_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = l_Lean_ResolveName_resolveNamespace(v_env_2791_, v_currNamespace_2792_, v_openDecls_2793_, v_n_2794_);
v___x_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
lean_ctor_set(v___x_2798_, 1, v___y_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed(lean_object* v_env_2799_, lean_object* v_currNamespace_2800_, lean_object* v_openDecls_2801_, lean_object* v_n_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(v_env_2799_, v_currNamespace_2800_, v_openDecls_2801_, v_n_2802_, v___y_2803_, v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(lean_object* v_currNamespace_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v_currNamespace_2806_);
lean_ctor_set(v___x_2809_, 1, v___y_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed(lean_object* v_currNamespace_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(v_currNamespace_2810_, v___y_2811_, v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_env_2814_, lean_object* v_declName_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
uint8_t v___x_2818_; lean_object* v_env_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; uint8_t v___x_2822_; 
v___x_2818_ = 0;
v_env_2819_ = l_Lean_Environment_setExporting(v_env_2814_, v___x_2818_);
lean_inc(v_declName_2815_);
v___x_2820_ = l_Lean_mkPrivateName(v_env_2819_, v_declName_2815_);
v___x_2821_ = 1;
lean_inc_ref(v_env_2819_);
v___x_2822_ = l_Lean_Environment_contains(v_env_2819_, v___x_2820_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2823_ = l_Lean_privateToUserName(v_declName_2815_);
v___x_2824_ = l_Lean_Environment_contains(v_env_2819_, v___x_2823_, v___x_2821_);
v___x_2825_ = lean_box(v___x_2824_);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
lean_ctor_set(v___x_2826_, 1, v___y_2817_);
return v___x_2826_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec_ref(v_env_2819_);
lean_dec(v_declName_2815_);
v___x_2827_ = lean_box(v___x_2822_);
v___x_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
lean_ctor_set(v___x_2828_, 1, v___y_2817_);
return v___x_2828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_env_2829_, lean_object* v_declName_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_env_2829_, v_declName_2830_, v___y_2831_, v___y_2832_);
lean_dec_ref(v___y_2831_);
return v_res_2833_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = l_Lean_maxRecDepthErrorMessage;
v___x_2840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
return v___x_2840_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3);
v___x_2842_ = l_Lean_MessageData_ofFormat(v___x_2841_);
return v___x_2842_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4);
v___x_2844_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__2));
v___x_2845_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v___x_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(lean_object* v_ref_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v_ref_2846_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(v_ref_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(lean_object* v_keys_2854_, lean_object* v_i_2855_, lean_object* v_k_2856_){
_start:
{
lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = lean_array_get_size(v_keys_2854_);
v___x_2858_ = lean_nat_dec_lt(v_i_2855_, v___x_2857_);
if (v___x_2858_ == 0)
{
lean_dec(v_i_2855_);
return v___x_2858_;
}
else
{
lean_object* v_k_x27_2859_; uint8_t v___x_2860_; 
v_k_x27_2859_ = lean_array_fget_borrowed(v_keys_2854_, v_i_2855_);
v___x_2860_ = l_Lean_instBEqExtraModUse_beq(v_k_2856_, v_k_x27_2859_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = lean_nat_add(v_i_2855_, v___x_2861_);
lean_dec(v_i_2855_);
v_i_2855_ = v___x_2862_;
goto _start;
}
else
{
lean_dec(v_i_2855_);
return v___x_2858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg___boxed(lean_object* v_keys_2864_, lean_object* v_i_2865_, lean_object* v_k_2866_){
_start:
{
uint8_t v_res_2867_; lean_object* v_r_2868_; 
v_res_2867_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(v_keys_2864_, v_i_2865_, v_k_2866_);
lean_dec_ref(v_k_2866_);
lean_dec_ref(v_keys_2864_);
v_r_2868_ = lean_box(v_res_2867_);
return v_r_2868_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(lean_object* v_x_2869_, size_t v_x_2870_, lean_object* v_x_2871_){
_start:
{
if (lean_obj_tag(v_x_2869_) == 0)
{
lean_object* v_es_2872_; lean_object* v___x_2873_; size_t v___x_2874_; size_t v___x_2875_; lean_object* v_j_2876_; lean_object* v___x_2877_; 
v_es_2872_ = lean_ctor_get(v_x_2869_, 0);
v___x_2873_ = lean_box(2);
v___x_2874_ = ((size_t)31ULL);
v___x_2875_ = lean_usize_land(v_x_2870_, v___x_2874_);
v_j_2876_ = lean_usize_to_nat(v___x_2875_);
v___x_2877_ = lean_array_get_borrowed(v___x_2873_, v_es_2872_, v_j_2876_);
lean_dec(v_j_2876_);
switch(lean_obj_tag(v___x_2877_))
{
case 0:
{
lean_object* v_key_2878_; uint8_t v___x_2879_; 
v_key_2878_ = lean_ctor_get(v___x_2877_, 0);
v___x_2879_ = l_Lean_instBEqExtraModUse_beq(v_x_2871_, v_key_2878_);
return v___x_2879_;
}
case 1:
{
lean_object* v_node_2880_; size_t v___x_2881_; size_t v___x_2882_; 
v_node_2880_ = lean_ctor_get(v___x_2877_, 0);
v___x_2881_ = ((size_t)5ULL);
v___x_2882_ = lean_usize_shift_right(v_x_2870_, v___x_2881_);
v_x_2869_ = v_node_2880_;
v_x_2870_ = v___x_2882_;
goto _start;
}
default: 
{
uint8_t v___x_2884_; 
v___x_2884_ = 0;
return v___x_2884_;
}
}
}
else
{
lean_object* v_ks_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v_ks_2885_ = lean_ctor_get(v_x_2869_, 0);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(v_ks_2885_, v___x_2886_, v_x_2871_);
return v___x_2887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_x_2888_, lean_object* v_x_2889_, lean_object* v_x_2890_){
_start:
{
size_t v_x_90470__boxed_2891_; uint8_t v_res_2892_; lean_object* v_r_2893_; 
v_x_90470__boxed_2891_ = lean_unbox_usize(v_x_2889_);
lean_dec(v_x_2889_);
v_res_2892_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(v_x_2888_, v_x_90470__boxed_2891_, v_x_2890_);
lean_dec_ref(v_x_2890_);
lean_dec_ref(v_x_2888_);
v_r_2893_ = lean_box(v_res_2892_);
return v_r_2893_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(lean_object* v_x_2894_, lean_object* v_x_2895_){
_start:
{
uint64_t v___x_2896_; size_t v___x_2897_; uint8_t v___x_2898_; 
v___x_2896_ = l_Lean_instHashableExtraModUse_hash(v_x_2895_);
v___x_2897_ = lean_uint64_to_usize(v___x_2896_);
v___x_2898_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(v_x_2894_, v___x_2897_, v_x_2895_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg___boxed(lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
uint8_t v_res_2901_; lean_object* v_r_2902_; 
v_res_2901_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(v_x_2899_, v_x_2900_);
lean_dec_ref(v_x_2900_);
lean_dec_ref(v_x_2899_);
v_r_2902_ = lean_box(v_res_2901_);
return v_r_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___lam__0(lean_object* v___x_2903_, lean_object* v_entry_2904_, lean_object* v_s_2905_){
_start:
{
lean_object* v_addEntryFn_2906_; lean_object* v_importedEntries_2907_; lean_object* v_state_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2916_; 
v_addEntryFn_2906_ = lean_ctor_get(v___x_2903_, 3);
lean_inc(v_addEntryFn_2906_);
lean_dec_ref(v___x_2903_);
v_importedEntries_2907_ = lean_ctor_get(v_s_2905_, 0);
v_state_2908_ = lean_ctor_get(v_s_2905_, 1);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_s_2905_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2910_ = v_s_2905_;
v_isShared_2911_ = v_isSharedCheck_2916_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_state_2908_);
lean_inc(v_importedEntries_2907_);
lean_dec(v_s_2905_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2916_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v_state_2912_; lean_object* v___x_2914_; 
v_state_2912_ = lean_apply_2(v_addEntryFn_2906_, v_state_2908_, v_entry_2904_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v_state_2912_);
v___x_2914_ = v___x_2910_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_importedEntries_2907_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_state_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0(void){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2917_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1);
v___x_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
return v___x_2921_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1);
v___x_2923_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
lean_ctor_set(v___x_2923_, 2, v___x_2922_);
lean_ctor_set(v___x_2923_, 3, v___x_2922_);
lean_ctor_set(v___x_2923_, 4, v___x_2922_);
lean_ctor_set(v___x_2923_, 5, v___x_2922_);
return v___x_2923_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4(void){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2924_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__7));
v___x_2930_ = l_Lean_stringToMessageData(v___x_2929_);
return v___x_2930_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__9));
v___x_2933_ = l_Lean_stringToMessageData(v___x_2932_);
return v___x_2933_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2935_ = l_Lean_stringToMessageData(v___x_2934_);
return v___x_2935_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14(void){
_start:
{
lean_object* v_cls_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_cls_2939_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__6));
v___x_2940_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13));
v___x_2941_ = l_Lean_Name_append(v___x_2940_, v_cls_2939_);
return v___x_2941_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__15));
v___x_2944_ = l_Lean_stringToMessageData(v___x_2943_);
return v___x_2944_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__17));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(lean_object* v_mod_2952_, uint8_t v_isMeta_2953_, lean_object* v_hint_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v_env_2997_; uint8_t v_isExporting_2998_; lean_object* v_entry_2999_; lean_object* v___x_3000_; lean_object* v_env_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_2995_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4);
v___x_2996_ = lean_st_ref_get(v___y_2961_);
v_env_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc_ref(v_env_2997_);
lean_dec(v___x_2996_);
v_isExporting_2998_ = lean_ctor_get_uint8(v_env_2997_, sizeof(void*)*13);
lean_dec_ref(v_env_2997_);
lean_inc(v_mod_2952_);
v_entry_2999_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2999_, 0, v_mod_2952_);
lean_ctor_set_uint8(v_entry_2999_, sizeof(void*)*1, v_isExporting_2998_);
lean_ctor_set_uint8(v_entry_2999_, sizeof(void*)*1 + 1, v_isMeta_2953_);
v___x_3000_ = lean_st_ref_get(v___y_2961_);
v_env_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc_ref(v_env_3001_);
lean_dec(v___x_3000_);
v___x_3002_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3003_ = lean_box(1);
v___x_3004_ = lean_box(0);
v___x_3005_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2995_, v___x_3002_, v_env_3001_, v___x_3003_, v___x_3004_);
v___x_3006_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(v___x_3005_, v_entry_2999_);
lean_dec(v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v_toCold_3007_; lean_object* v_options_3008_; lean_object* v_inheritedTraceOptions_3009_; uint8_t v_hasTrace_3010_; lean_object* v___f_3011_; uint8_t v___x_3012_; lean_object* v___y_3014_; lean_object* v___y_3015_; 
v_toCold_3007_ = lean_ctor_get(v___y_2960_, 0);
v_options_3008_ = lean_ctor_get(v_toCold_3007_, 2);
v_inheritedTraceOptions_3009_ = lean_ctor_get(v_toCold_3007_, 11);
v_hasTrace_3010_ = lean_ctor_get_uint8(v_options_3008_, sizeof(void*)*1);
v___f_3011_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___lam__0), 3, 2);
lean_closure_set(v___f_3011_, 0, v___x_3002_);
lean_closure_set(v___f_3011_, 1, v_entry_2999_);
v___x_3012_ = 1;
if (v_hasTrace_3010_ == 0)
{
lean_dec(v_hint_2954_);
lean_dec(v_mod_2952_);
v___y_3014_ = v___y_2959_;
v___y_3015_ = v___y_2961_;
goto v___jp_3013_;
}
else
{
lean_object* v_cls_3042_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v_cls_3042_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__6));
v___x_3062_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14);
v___x_3063_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3009_, v_options_3008_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_dec(v_hint_2954_);
lean_dec(v_mod_2952_);
v___y_3014_ = v___y_2959_;
v___y_3015_ = v___y_2961_;
goto v___jp_3013_;
}
else
{
lean_object* v___x_3064_; lean_object* v___y_3066_; 
v___x_3064_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16);
if (v_isExporting_2998_ == 0)
{
lean_object* v___x_3073_; 
v___x_3073_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__21));
v___y_3066_ = v___x_3073_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3074_; 
v___x_3074_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__22));
v___y_3066_ = v___x_3074_;
goto v___jp_3065_;
}
v___jp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_inc_ref(v___y_3066_);
v___x_3067_ = l_Lean_stringToMessageData(v___y_3066_);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3064_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
if (v_isMeta_2953_ == 0)
{
lean_object* v___x_3071_; 
v___x_3071_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__19));
v___y_3049_ = v___x_3070_;
v___y_3050_ = v___x_3071_;
goto v___jp_3048_;
}
else
{
lean_object* v___x_3072_; 
v___x_3072_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__20));
v___y_3049_ = v___x_3070_;
v___y_3050_ = v___x_3072_;
goto v___jp_3048_;
}
}
}
v___jp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___y_3044_);
lean_ctor_set(v___x_3046_, 1, v___y_3045_);
v___x_3047_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_3042_, v___x_3046_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_dec_ref_known(v___x_3047_, 1);
v___y_3014_ = v___y_2959_;
v___y_3015_ = v___y_2961_;
goto v___jp_3013_;
}
else
{
lean_dec_ref(v___f_3011_);
return v___x_3047_;
}
}
v___jp_3048_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
lean_inc_ref(v___y_3050_);
v___x_3051_ = l_Lean_stringToMessageData(v___y_3050_);
v___x_3052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___y_3049_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8);
v___x_3054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = l_Lean_MessageData_ofName(v_mod_2952_);
v___x_3056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3054_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = l_Lean_Name_isAnonymous(v_hint_2954_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10);
v___x_3059_ = l_Lean_MessageData_ofName(v_hint_2954_);
v___x_3060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___y_3044_ = v___x_3056_;
v___y_3045_ = v___x_3060_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3061_; 
lean_dec(v_hint_2954_);
v___x_3061_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11);
v___y_3044_ = v___x_3056_;
v___y_3045_ = v___x_3061_;
goto v___jp_3043_;
}
}
}
v___jp_3013_:
{
lean_object* v___x_3016_; lean_object* v_toEnvExtension_3017_; uint8_t v_logWrites_3018_; 
v___x_3016_ = lean_st_ref_take(v___y_3015_);
v_toEnvExtension_3017_ = lean_ctor_get(v___x_3002_, 0);
v_logWrites_3018_ = lean_ctor_get_uint8(v_toEnvExtension_3017_, sizeof(void*)*6);
if (v_logWrites_3018_ == 0)
{
lean_object* v_env_3019_; lean_object* v_nextMacroScope_3020_; lean_object* v_ngen_3021_; lean_object* v_auxDeclNGen_3022_; lean_object* v_traceState_3023_; lean_object* v_recordedDeps_3024_; lean_object* v_messages_3025_; lean_object* v_infoState_3026_; lean_object* v_snapshotTasks_3027_; lean_object* v_asyncMode_3028_; lean_object* v___x_3029_; 
v_env_3019_ = lean_ctor_get(v___x_3016_, 0);
lean_inc_ref(v_env_3019_);
v_nextMacroScope_3020_ = lean_ctor_get(v___x_3016_, 1);
lean_inc(v_nextMacroScope_3020_);
v_ngen_3021_ = lean_ctor_get(v___x_3016_, 2);
lean_inc_ref(v_ngen_3021_);
v_auxDeclNGen_3022_ = lean_ctor_get(v___x_3016_, 3);
lean_inc_ref(v_auxDeclNGen_3022_);
v_traceState_3023_ = lean_ctor_get(v___x_3016_, 4);
lean_inc_ref(v_traceState_3023_);
v_recordedDeps_3024_ = lean_ctor_get(v___x_3016_, 6);
lean_inc_ref(v_recordedDeps_3024_);
v_messages_3025_ = lean_ctor_get(v___x_3016_, 7);
lean_inc_ref(v_messages_3025_);
v_infoState_3026_ = lean_ctor_get(v___x_3016_, 8);
lean_inc_ref(v_infoState_3026_);
v_snapshotTasks_3027_ = lean_ctor_get(v___x_3016_, 9);
lean_inc_ref(v_snapshotTasks_3027_);
lean_dec(v___x_3016_);
v_asyncMode_3028_ = lean_ctor_get(v_toEnvExtension_3017_, 2);
lean_inc_ref(v_toEnvExtension_3017_);
v___x_3029_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3017_, v_env_3019_, v___f_3011_, v_asyncMode_3028_, v___x_3004_, v___x_3012_);
v___y_2964_ = v_infoState_3026_;
v___y_2965_ = v_messages_3025_;
v___y_2966_ = v_recordedDeps_3024_;
v___y_2967_ = v_ngen_3021_;
v___y_2968_ = v___y_3014_;
v___y_2969_ = v_snapshotTasks_3027_;
v___y_2970_ = v_auxDeclNGen_3022_;
v___y_2971_ = v___y_3015_;
v___y_2972_ = v_nextMacroScope_3020_;
v___y_2973_ = v_traceState_3023_;
v___y_2974_ = v___x_3029_;
goto v___jp_2963_;
}
else
{
lean_object* v_env_3030_; lean_object* v_nextMacroScope_3031_; lean_object* v_ngen_3032_; lean_object* v_auxDeclNGen_3033_; lean_object* v_traceState_3034_; lean_object* v_recordedDeps_3035_; lean_object* v_messages_3036_; lean_object* v_infoState_3037_; lean_object* v_snapshotTasks_3038_; lean_object* v_asyncMode_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_env_3030_ = lean_ctor_get(v___x_3016_, 0);
lean_inc_ref(v_env_3030_);
v_nextMacroScope_3031_ = lean_ctor_get(v___x_3016_, 1);
lean_inc(v_nextMacroScope_3031_);
v_ngen_3032_ = lean_ctor_get(v___x_3016_, 2);
lean_inc_ref(v_ngen_3032_);
v_auxDeclNGen_3033_ = lean_ctor_get(v___x_3016_, 3);
lean_inc_ref(v_auxDeclNGen_3033_);
v_traceState_3034_ = lean_ctor_get(v___x_3016_, 4);
lean_inc_ref(v_traceState_3034_);
v_recordedDeps_3035_ = lean_ctor_get(v___x_3016_, 6);
lean_inc_ref(v_recordedDeps_3035_);
v_messages_3036_ = lean_ctor_get(v___x_3016_, 7);
lean_inc_ref(v_messages_3036_);
v_infoState_3037_ = lean_ctor_get(v___x_3016_, 8);
lean_inc_ref(v_infoState_3037_);
v_snapshotTasks_3038_ = lean_ctor_get(v___x_3016_, 9);
lean_inc_ref(v_snapshotTasks_3038_);
lean_dec(v___x_3016_);
v_asyncMode_3039_ = lean_ctor_get(v_toEnvExtension_3017_, 2);
lean_inc_ref_n(v_toEnvExtension_3017_, 2);
v___x_3040_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3017_, v_env_3030_);
lean_dec_ref(v_env_3030_);
v___x_3041_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3017_, v___x_3040_, v___f_3011_, v_asyncMode_3039_, v___x_3004_, v___x_3012_);
v___y_2964_ = v_infoState_3037_;
v___y_2965_ = v_messages_3036_;
v___y_2966_ = v_recordedDeps_3035_;
v___y_2967_ = v_ngen_3032_;
v___y_2968_ = v___y_3014_;
v___y_2969_ = v_snapshotTasks_3038_;
v___y_2970_ = v_auxDeclNGen_3033_;
v___y_2971_ = v___y_3015_;
v___y_2972_ = v_nextMacroScope_3031_;
v___y_2973_ = v_traceState_3034_;
v___y_2974_ = v___x_3041_;
goto v___jp_2963_;
}
}
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec_ref_known(v_entry_2999_, 1);
lean_dec(v_hint_2954_);
lean_dec(v_mod_2952_);
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
return v___x_3076_;
}
v___jp_2963_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v_mctx_2979_; lean_object* v_zetaDeltaFVarIds_2980_; lean_object* v_postponed_2981_; lean_object* v_diag_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2993_; 
v___x_2975_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2);
v___x_2976_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2976_, 0, v___y_2974_);
lean_ctor_set(v___x_2976_, 1, v___y_2972_);
lean_ctor_set(v___x_2976_, 2, v___y_2967_);
lean_ctor_set(v___x_2976_, 3, v___y_2970_);
lean_ctor_set(v___x_2976_, 4, v___y_2973_);
lean_ctor_set(v___x_2976_, 5, v___x_2975_);
lean_ctor_set(v___x_2976_, 6, v___y_2966_);
lean_ctor_set(v___x_2976_, 7, v___y_2965_);
lean_ctor_set(v___x_2976_, 8, v___y_2964_);
lean_ctor_set(v___x_2976_, 9, v___y_2969_);
v___x_2977_ = lean_st_ref_put(v___y_2971_, v___x_2976_);
v___x_2978_ = lean_st_ref_take(v___y_2968_);
v_mctx_2979_ = lean_ctor_get(v___x_2978_, 0);
v_zetaDeltaFVarIds_2980_ = lean_ctor_get(v___x_2978_, 2);
v_postponed_2981_ = lean_ctor_get(v___x_2978_, 3);
v_diag_2982_ = lean_ctor_get(v___x_2978_, 4);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; 
v_unused_2994_ = lean_ctor_get(v___x_2978_, 1);
lean_dec(v_unused_2994_);
v___x_2984_ = v___x_2978_;
v_isShared_2985_ = v_isSharedCheck_2993_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_diag_2982_);
lean_inc(v_postponed_2981_);
lean_inc(v_zetaDeltaFVarIds_2980_);
lean_inc(v_mctx_2979_);
lean_dec(v___x_2978_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2993_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2986_ = lean_box(0);
v___x_2987_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v___x_2987_);
v___x_2989_ = v___x_2984_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_mctx_2979_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_zetaDeltaFVarIds_2980_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_postponed_2981_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v_diag_2982_);
v___x_2989_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_st_ref_put(v___y_2968_, v___x_2989_);
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2986_);
return v___x_2991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___boxed(lean_object* v_mod_3077_, lean_object* v_isMeta_3078_, lean_object* v_hint_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
uint8_t v_isMeta_boxed_3088_; lean_object* v_res_3089_; 
v_isMeta_boxed_3088_ = lean_unbox(v_isMeta_3078_);
v_res_3089_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(v_mod_3077_, v_isMeta_boxed_3088_, v_hint_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec_ref(v___y_3080_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(lean_object* v___x_3090_, lean_object* v_declName_3091_, lean_object* v_as_3092_, size_t v_sz_3093_, size_t v_i_3094_, lean_object* v_b_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
uint8_t v___x_3104_; 
v___x_3104_ = lean_usize_dec_lt(v_i_3094_, v_sz_3093_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
lean_dec(v_declName_3091_);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v_b_3095_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v_modules_3107_; lean_object* v___x_3108_; lean_object* v_a_3109_; lean_object* v___x_3110_; lean_object* v_toImport_3111_; lean_object* v_module_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; lean_object* v___x_3115_; 
v___x_3106_ = l_Lean_Environment_header(v___x_3090_);
v_modules_3107_ = lean_ctor_get(v___x_3106_, 3);
lean_inc_ref(v_modules_3107_);
lean_dec_ref(v___x_3106_);
v___x_3108_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3109_ = lean_array_uget_borrowed(v_as_3092_, v_i_3094_);
v___x_3110_ = lean_array_get(v___x_3108_, v_modules_3107_, v_a_3109_);
lean_dec_ref(v_modules_3107_);
v_toImport_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc_ref(v_toImport_3111_);
lean_dec(v___x_3110_);
v_module_3112_ = lean_ctor_get(v_toImport_3111_, 0);
lean_inc(v_module_3112_);
lean_dec_ref(v_toImport_3111_);
v___x_3113_ = lean_box(0);
v___x_3114_ = 0;
lean_inc(v_declName_3091_);
v___x_3115_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(v_module_3112_, v___x_3114_, v_declName_3091_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3115_) == 0)
{
size_t v___x_3116_; size_t v___x_3117_; 
lean_dec_ref_known(v___x_3115_, 1);
v___x_3116_ = ((size_t)1ULL);
v___x_3117_ = lean_usize_add(v_i_3094_, v___x_3116_);
v_i_3094_ = v___x_3117_;
v_b_3095_ = v___x_3113_;
goto _start;
}
else
{
lean_dec(v_declName_3091_);
return v___x_3115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17___boxed(lean_object* v___x_3119_, lean_object* v_declName_3120_, lean_object* v_as_3121_, lean_object* v_sz_3122_, lean_object* v_i_3123_, lean_object* v_b_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
size_t v_sz_boxed_3133_; size_t v_i_boxed_3134_; lean_object* v_res_3135_; 
v_sz_boxed_3133_ = lean_unbox_usize(v_sz_3122_);
lean_dec(v_sz_3122_);
v_i_boxed_3134_ = lean_unbox_usize(v_i_3123_);
lean_dec(v_i_3123_);
v_res_3135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(v___x_3119_, v_declName_3120_, v_as_3121_, v_sz_boxed_3133_, v_i_boxed_3134_, v_b_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec_ref(v_as_3121_);
lean_dec_ref(v___x_3119_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(lean_object* v_a_3136_, lean_object* v_x_3137_){
_start:
{
if (lean_obj_tag(v_x_3137_) == 0)
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_box(0);
return v___x_3138_;
}
else
{
lean_object* v_key_3139_; lean_object* v_value_3140_; lean_object* v_tail_3141_; uint8_t v___x_3142_; 
v_key_3139_ = lean_ctor_get(v_x_3137_, 0);
v_value_3140_ = lean_ctor_get(v_x_3137_, 1);
v_tail_3141_ = lean_ctor_get(v_x_3137_, 2);
v___x_3142_ = lean_name_eq(v_key_3139_, v_a_3136_);
if (v___x_3142_ == 0)
{
v_x_3137_ = v_tail_3141_;
goto _start;
}
else
{
lean_object* v___x_3144_; 
lean_inc(v_value_3140_);
v___x_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3144_, 0, v_value_3140_);
return v___x_3144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg___boxed(lean_object* v_a_3145_, lean_object* v_x_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(v_a_3145_, v_x_3146_);
lean_dec(v_x_3146_);
lean_dec(v_a_3145_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(lean_object* v_m_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_buckets_3150_; lean_object* v___x_3151_; uint64_t v___y_3153_; 
v_buckets_3150_ = lean_ctor_get(v_m_3148_, 1);
v___x_3151_ = lean_array_get_size(v_buckets_3150_);
if (lean_obj_tag(v_a_3149_) == 0)
{
uint64_t v___x_3167_; 
v___x_3167_ = 1723ULL;
v___y_3153_ = v___x_3167_;
goto v___jp_3152_;
}
else
{
uint64_t v_hash_3168_; 
v_hash_3168_ = lean_ctor_get_uint64(v_a_3149_, sizeof(void*)*2);
v___y_3153_ = v_hash_3168_;
goto v___jp_3152_;
}
v___jp_3152_:
{
uint64_t v___x_3154_; uint64_t v___x_3155_; uint64_t v_fold_3156_; uint64_t v___x_3157_; uint64_t v___x_3158_; uint64_t v___x_3159_; size_t v___x_3160_; size_t v___x_3161_; size_t v___x_3162_; size_t v___x_3163_; size_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3154_ = 32ULL;
v___x_3155_ = lean_uint64_shift_right(v___y_3153_, v___x_3154_);
v_fold_3156_ = lean_uint64_xor(v___y_3153_, v___x_3155_);
v___x_3157_ = 16ULL;
v___x_3158_ = lean_uint64_shift_right(v_fold_3156_, v___x_3157_);
v___x_3159_ = lean_uint64_xor(v_fold_3156_, v___x_3158_);
v___x_3160_ = lean_uint64_to_usize(v___x_3159_);
v___x_3161_ = lean_usize_of_nat(v___x_3151_);
v___x_3162_ = ((size_t)1ULL);
v___x_3163_ = lean_usize_sub(v___x_3161_, v___x_3162_);
v___x_3164_ = lean_usize_land(v___x_3160_, v___x_3163_);
v___x_3165_ = lean_array_uget_borrowed(v_buckets_3150_, v___x_3164_);
v___x_3166_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(v_a_3149_, v___x_3165_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg___boxed(lean_object* v_m_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(v_m_3169_, v_a_3170_);
lean_dec(v_a_3170_);
lean_dec_ref(v_m_3169_);
return v_res_3171_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Std_HashMap_instInhabited___redArg();
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(lean_object* v_declName_3175_, uint8_t v_isMeta_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v_env_3190_; lean_object* v___y_3192_; lean_object* v___x_3205_; 
v___x_3185_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0);
v___x_3186_ = lean_st_ref_get(v___y_3183_);
v_env_3190_ = lean_ctor_get(v___x_3186_, 0);
lean_inc_ref(v_env_3190_);
lean_dec(v___x_3186_);
v___x_3205_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3190_, v_declName_3175_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_dec_ref(v_env_3190_);
lean_dec(v_declName_3175_);
goto v___jp_3187_;
}
else
{
lean_object* v_val_3206_; lean_object* v___x_3207_; lean_object* v_modules_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; 
v_val_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_val_3206_);
lean_dec_ref_known(v___x_3205_, 1);
v___x_3207_ = l_Lean_Environment_header(v_env_3190_);
v_modules_3208_ = lean_ctor_get(v___x_3207_, 3);
lean_inc_ref(v_modules_3208_);
lean_dec_ref(v___x_3207_);
v___x_3209_ = lean_array_get_size(v_modules_3208_);
v___x_3210_ = lean_nat_dec_lt(v_val_3206_, v___x_3209_);
if (v___x_3210_ == 0)
{
lean_dec_ref(v_modules_3208_);
lean_dec(v_val_3206_);
lean_dec_ref(v_env_3190_);
lean_dec(v_declName_3175_);
goto v___jp_3187_;
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___y_3214_; 
v___x_3211_ = lean_array_fget(v_modules_3208_, v_val_3206_);
lean_dec(v_val_3206_);
lean_dec_ref(v_modules_3208_);
v___x_3212_ = lean_st_ref_get(v___y_3183_);
if (v_isMeta_3176_ == 0)
{
lean_dec(v___x_3212_);
v___y_3214_ = v_isMeta_3176_;
goto v___jp_3213_;
}
else
{
lean_object* v_env_3225_; uint8_t v___x_3226_; 
v_env_3225_ = lean_ctor_get(v___x_3212_, 0);
lean_inc_ref(v_env_3225_);
lean_dec(v___x_3212_);
lean_inc(v_declName_3175_);
v___x_3226_ = l_Lean_isMarkedMeta(v_env_3225_, v_declName_3175_);
if (v___x_3226_ == 0)
{
v___y_3214_ = v_isMeta_3176_;
goto v___jp_3213_;
}
else
{
uint8_t v___x_3227_; 
v___x_3227_ = 0;
v___y_3214_ = v___x_3227_;
goto v___jp_3213_;
}
}
v___jp_3213_:
{
lean_object* v_toImport_3215_; lean_object* v_module_3216_; lean_object* v___x_3217_; 
v_toImport_3215_ = lean_ctor_get(v___x_3211_, 0);
lean_inc_ref(v_toImport_3215_);
lean_dec(v___x_3211_);
v_module_3216_ = lean_ctor_get(v_toImport_3215_, 0);
lean_inc(v_module_3216_);
lean_dec_ref(v_toImport_3215_);
lean_inc(v_declName_3175_);
v___x_3217_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(v_module_3216_, v___y_3214_, v_declName_3175_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_dec_ref_known(v___x_3217_, 1);
v___x_3218_ = l_Lean_indirectModUseExt;
v___x_3219_ = lean_box(1);
v___x_3220_ = lean_box(0);
lean_inc_ref(v_env_3190_);
v___x_3221_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3185_, v___x_3218_, v_env_3190_, v___x_3219_, v___x_3220_);
v___x_3222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(v___x_3221_, v_declName_3175_);
lean_dec(v___x_3221_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v___x_3223_; 
v___x_3223_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__1));
v___y_3192_ = v___x_3223_;
goto v___jp_3191_;
}
else
{
lean_object* v_val_3224_; 
v_val_3224_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_val_3224_);
lean_dec_ref_known(v___x_3222_, 1);
v___y_3192_ = v_val_3224_;
goto v___jp_3191_;
}
}
else
{
lean_dec_ref(v_env_3190_);
lean_dec(v_declName_3175_);
return v___x_3217_;
}
}
}
}
v___jp_3187_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_box(0);
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
return v___x_3189_;
}
v___jp_3191_:
{
lean_object* v___x_3193_; size_t v_sz_3194_; size_t v___x_3195_; lean_object* v___x_3196_; 
v___x_3193_ = lean_box(0);
v_sz_3194_ = lean_array_size(v___y_3192_);
v___x_3195_ = ((size_t)0ULL);
v___x_3196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(v_env_3190_, v_declName_3175_, v___y_3192_, v_sz_3194_, v___x_3195_, v___x_3193_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec_ref(v___y_3192_);
lean_dec_ref(v_env_3190_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3203_ == 0)
{
lean_object* v_unused_3204_; 
v_unused_3204_ = lean_ctor_get(v___x_3196_, 0);
lean_dec(v_unused_3204_);
v___x_3198_ = v___x_3196_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_dec(v___x_3196_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3193_);
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3193_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
else
{
return v___x_3196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___boxed(lean_object* v_declName_3228_, lean_object* v_isMeta_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v_isMeta_boxed_3238_; lean_object* v_res_3239_; 
v_isMeta_boxed_3238_ = lean_unbox(v_isMeta_3229_);
v_res_3239_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(v_declName_3228_, v_isMeta_boxed_3238_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec_ref(v___y_3230_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(lean_object* v_as_x27_3240_, lean_object* v_b_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
if (lean_obj_tag(v_as_x27_3240_) == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_b_3241_);
return v___x_3250_;
}
else
{
lean_object* v_head_3251_; lean_object* v_tail_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; 
v_head_3251_ = lean_ctor_get(v_as_x27_3240_, 0);
v_tail_3252_ = lean_ctor_get(v_as_x27_3240_, 1);
v___x_3253_ = lean_box(0);
v___x_3254_ = 1;
lean_inc(v_head_3251_);
v___x_3255_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(v_head_3251_, v___x_3254_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_dec_ref_known(v___x_3255_, 1);
v_as_x27_3240_ = v_tail_3252_;
v_b_3241_ = v___x_3253_;
goto _start;
}
else
{
return v___x_3255_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg___boxed(lean_object* v_as_x27_3257_, lean_object* v_b_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(v_as_x27_3257_, v_b_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v_as_x27_3257_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(lean_object* v_env_3268_, lean_object* v___x_3269_, lean_object* v_currNamespace_3270_, lean_object* v_openDecls_3271_, lean_object* v_n_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = l_Lean_ResolveName_resolveGlobalName(v_env_3268_, v___x_3269_, v_currNamespace_3270_, v_openDecls_3271_, v_n_3272_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
lean_ctor_set(v___x_3276_, 1, v___y_3274_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed(lean_object* v_env_3277_, lean_object* v___x_3278_, lean_object* v_currNamespace_3279_, lean_object* v_openDecls_3280_, lean_object* v_n_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(v_env_3277_, v___x_3278_, v_currNamespace_3279_, v_openDecls_3280_, v_n_3281_, v___y_3282_, v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec_ref(v___x_3278_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(lean_object* v_as_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
if (lean_obj_tag(v_as_3285_) == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = lean_box(0);
v___x_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
return v___x_3295_;
}
else
{
lean_object* v_toCold_3296_; lean_object* v_options_3297_; uint8_t v_hasTrace_3298_; 
v_toCold_3296_ = lean_ctor_get(v___y_3291_, 0);
v_options_3297_ = lean_ctor_get(v_toCold_3296_, 2);
v_hasTrace_3298_ = lean_ctor_get_uint8(v_options_3297_, sizeof(void*)*1);
if (v_hasTrace_3298_ == 0)
{
lean_object* v_tail_3299_; 
v_tail_3299_ = lean_ctor_get(v_as_3285_, 1);
lean_inc(v_tail_3299_);
lean_dec_ref_known(v_as_3285_, 2);
v_as_3285_ = v_tail_3299_;
goto _start;
}
else
{
lean_object* v_head_3301_; lean_object* v_tail_3302_; lean_object* v_fst_3303_; lean_object* v_snd_3304_; lean_object* v_inheritedTraceOptions_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; 
v_head_3301_ = lean_ctor_get(v_as_3285_, 0);
lean_inc(v_head_3301_);
v_tail_3302_ = lean_ctor_get(v_as_3285_, 1);
lean_inc(v_tail_3302_);
lean_dec_ref_known(v_as_3285_, 2);
v_fst_3303_ = lean_ctor_get(v_head_3301_, 0);
lean_inc_n(v_fst_3303_, 2);
v_snd_3304_ = lean_ctor_get(v_head_3301_, 1);
lean_inc(v_snd_3304_);
lean_dec(v_head_3301_);
v_inheritedTraceOptions_3305_ = lean_ctor_get(v_toCold_3296_, 11);
v___x_3306_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13));
v___x_3307_ = l_Lean_Name_append(v___x_3306_, v_fst_3303_);
v___x_3308_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3305_, v_options_3297_, v___x_3307_);
lean_dec(v___x_3307_);
if (v___x_3308_ == 0)
{
lean_dec(v_snd_3304_);
lean_dec(v_fst_3303_);
v_as_3285_ = v_tail_3302_;
goto _start;
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3310_, 0, v_snd_3304_);
v___x_3311_ = l_Lean_MessageData_ofFormat(v___x_3310_);
v___x_3312_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_fst_3303_, v___x_3311_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref_known(v___x_3312_, 1);
v_as_3285_ = v_tail_3302_;
goto _start;
}
else
{
lean_dec(v_tail_3302_);
return v___x_3312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___boxed(lean_object* v_as_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(v_as_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v___y_3315_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(lean_object* v_x_3324_, lean_object* v___y_3325_){
_start:
{
if (lean_obj_tag(v_x_3324_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3327_; 
v_a_3326_ = lean_ctor_get(v_x_3324_, 0);
lean_inc(v_a_3326_);
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v_a_3326_);
lean_ctor_set(v___x_3327_, 1, v___y_3325_);
return v___x_3327_;
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3329_; 
v_a_3328_ = lean_ctor_get(v_x_3324_, 0);
lean_inc(v_a_3328_);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v_a_3328_);
lean_ctor_set(v___x_3329_, 1, v___y_3325_);
return v___x_3329_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg___boxed(lean_object* v_x_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v_x_3330_, v___y_3331_);
lean_dec_ref(v_x_3330_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(lean_object* v_env_3333_, lean_object* v_stx_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_3333_, v_stx_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
if (lean_obj_tag(v_a_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3347_; 
v_a_3339_ = lean_ctor_get(v___x_3337_, 1);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; 
v_unused_3348_ = lean_ctor_get(v___x_3337_, 0);
lean_dec(v_unused_3348_);
v___x_3341_ = v___x_3337_;
v_isShared_3342_ = v_isSharedCheck_3347_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3337_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3347_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3343_ = lean_box(0);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3343_);
v___x_3345_ = v___x_3341_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_a_3339_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
else
{
lean_object* v_val_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3377_; 
v_val_3349_ = lean_ctor_get(v_a_3338_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v_a_3338_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3351_ = v_a_3338_;
v_isShared_3352_ = v_isSharedCheck_3377_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_val_3349_);
lean_dec(v_a_3338_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3377_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v_snd_3353_; 
v_snd_3353_ = lean_ctor_get(v_val_3349_, 1);
lean_inc(v_snd_3353_);
lean_dec(v_val_3349_);
if (lean_obj_tag(v_snd_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3363_; 
lean_del_object(v___x_3351_);
v_a_3354_ = lean_ctor_get(v___x_3337_, 1);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3337_, 2);
v_a_3355_ = lean_ctor_get(v_snd_3353_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_snd_3353_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3357_ = v_snd_3353_;
v_isShared_3358_ = v_isSharedCheck_3363_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v_snd_3353_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3363_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v___x_3360_, v_a_3354_);
lean_dec_ref(v___x_3360_);
return v___x_3361_;
}
}
}
else
{
lean_object* v_a_3364_; lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3376_; 
v_a_3364_ = lean_ctor_get(v___x_3337_, 1);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3337_, 2);
v_a_3365_ = lean_ctor_get(v_snd_3353_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v_snd_3353_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3367_ = v_snd_3353_;
v_isShared_3368_ = v_isSharedCheck_3376_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v_snd_3353_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3376_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v_a_3365_);
v___x_3370_ = v___x_3351_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3372_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3370_);
v___x_3372_ = v___x_3367_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v___x_3372_, v_a_3364_);
lean_dec_ref(v___x_3372_);
return v___x_3373_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
v_a_3378_ = lean_ctor_get(v___x_3337_, 0);
v_a_3379_ = lean_ctor_get(v___x_3337_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3337_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_inc(v_a_3378_);
lean_dec(v___x_3337_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3378_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed(lean_object* v_env_3387_, lean_object* v_stx_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(v_env_3387_, v_stx_3388_, v___y_3389_, v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_x_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; lean_object* v_toCold_3403_; lean_object* v_env_3404_; lean_object* v_currRecDepth_3405_; lean_object* v_ref_3406_; lean_object* v_maxRecDepth_3407_; lean_object* v_currNamespace_3408_; lean_object* v_openDecls_3409_; lean_object* v_quotContext_3410_; lean_object* v_currMacroScope_3411_; lean_object* v___f_3412_; lean_object* v___f_3413_; lean_object* v___x_3414_; lean_object* v___f_3415_; lean_object* v___f_3416_; lean_object* v___f_3417_; lean_object* v_methods_3418_; lean_object* v___x_3419_; lean_object* v_nextMacroScope_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3402_ = lean_st_ref_get(v___y_3400_);
v_toCold_3403_ = lean_ctor_get(v___y_3399_, 0);
v_env_3404_ = lean_ctor_get(v___x_3402_, 0);
lean_inc_ref_n(v_env_3404_, 4);
lean_dec(v___x_3402_);
v_currRecDepth_3405_ = lean_ctor_get(v___y_3399_, 1);
v_ref_3406_ = lean_ctor_get(v___y_3399_, 2);
v_maxRecDepth_3407_ = lean_ctor_get(v_toCold_3403_, 3);
v_currNamespace_3408_ = lean_ctor_get(v_toCold_3403_, 4);
v_openDecls_3409_ = lean_ctor_get(v_toCold_3403_, 5);
v_quotContext_3410_ = lean_ctor_get(v_toCold_3403_, 8);
v_currMacroScope_3411_ = lean_ctor_get(v_toCold_3403_, 9);
v___f_3412_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3412_, 0, v_env_3404_);
v___f_3413_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3413_, 0, v_env_3404_);
v___x_3414_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3399_);
lean_inc_n(v_currNamespace_3408_, 3);
v___f_3415_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3415_, 0, v_currNamespace_3408_);
lean_inc_n(v_openDecls_3409_, 2);
v___f_3416_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_3416_, 0, v_env_3404_);
lean_closure_set(v___f_3416_, 1, v___x_3414_);
lean_closure_set(v___f_3416_, 2, v_currNamespace_3408_);
lean_closure_set(v___f_3416_, 3, v_openDecls_3409_);
v___f_3417_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_3417_, 0, v_env_3404_);
lean_closure_set(v___f_3417_, 1, v_currNamespace_3408_);
lean_closure_set(v___f_3417_, 2, v_openDecls_3409_);
v_methods_3418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3418_, 0, v___f_3413_);
lean_ctor_set(v_methods_3418_, 1, v___f_3415_);
lean_ctor_set(v_methods_3418_, 2, v___f_3412_);
lean_ctor_set(v_methods_3418_, 3, v___f_3417_);
lean_ctor_set(v_methods_3418_, 4, v___f_3416_);
v___x_3419_ = lean_st_ref_get(v___y_3400_);
v_nextMacroScope_3420_ = lean_ctor_get(v___x_3419_, 1);
lean_inc(v_nextMacroScope_3420_);
lean_dec(v___x_3419_);
lean_inc(v_ref_3406_);
lean_inc(v_maxRecDepth_3407_);
lean_inc(v_currRecDepth_3405_);
lean_inc(v_currMacroScope_3411_);
lean_inc(v_quotContext_3410_);
v___x_3421_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3421_, 0, v_methods_3418_);
lean_ctor_set(v___x_3421_, 1, v_quotContext_3410_);
lean_ctor_set(v___x_3421_, 2, v_currMacroScope_3411_);
lean_ctor_set(v___x_3421_, 3, v_currRecDepth_3405_);
lean_ctor_set(v___x_3421_, 4, v_maxRecDepth_3407_);
lean_ctor_set(v___x_3421_, 5, v_ref_3406_);
v___x_3422_ = lean_box(0);
v___x_3423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3423_, 0, v_nextMacroScope_3420_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
lean_ctor_set(v___x_3423_, 2, v___x_3422_);
v___x_3424_ = lean_apply_2(v_x_3393_, v___x_3421_, v___x_3423_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v_a_3426_; lean_object* v_macroScope_3427_; lean_object* v_traceMsgs_3428_; lean_object* v_expandedMacroDecls_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 1);
lean_inc(v_a_3425_);
v_a_3426_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3424_, 2);
v_macroScope_3427_ = lean_ctor_get(v_a_3425_, 0);
lean_inc(v_macroScope_3427_);
v_traceMsgs_3428_ = lean_ctor_get(v_a_3425_, 1);
lean_inc(v_traceMsgs_3428_);
v_expandedMacroDecls_3429_ = lean_ctor_get(v_a_3425_, 2);
lean_inc(v_expandedMacroDecls_3429_);
lean_dec(v_a_3425_);
v___x_3430_ = lean_box(0);
v___x_3431_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(v_expandedMacroDecls_3429_, v___x_3430_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v_expandedMacroDecls_3429_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v___x_3432_; lean_object* v_env_3433_; lean_object* v_ngen_3434_; lean_object* v_auxDeclNGen_3435_; lean_object* v_traceState_3436_; lean_object* v_cache_3437_; lean_object* v_recordedDeps_3438_; lean_object* v_messages_3439_; lean_object* v_infoState_3440_; lean_object* v_snapshotTasks_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref_known(v___x_3431_, 1);
v___x_3432_ = lean_st_ref_take(v___y_3400_);
v_env_3433_ = lean_ctor_get(v___x_3432_, 0);
v_ngen_3434_ = lean_ctor_get(v___x_3432_, 2);
v_auxDeclNGen_3435_ = lean_ctor_get(v___x_3432_, 3);
v_traceState_3436_ = lean_ctor_get(v___x_3432_, 4);
v_cache_3437_ = lean_ctor_get(v___x_3432_, 5);
v_recordedDeps_3438_ = lean_ctor_get(v___x_3432_, 6);
v_messages_3439_ = lean_ctor_get(v___x_3432_, 7);
v_infoState_3440_ = lean_ctor_get(v___x_3432_, 8);
v_snapshotTasks_3441_ = lean_ctor_get(v___x_3432_, 9);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; 
v_unused_3468_ = lean_ctor_get(v___x_3432_, 1);
lean_dec(v_unused_3468_);
v___x_3443_ = v___x_3432_;
v_isShared_3444_ = v_isSharedCheck_3467_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_snapshotTasks_3441_);
lean_inc(v_infoState_3440_);
lean_inc(v_messages_3439_);
lean_inc(v_recordedDeps_3438_);
lean_inc(v_cache_3437_);
lean_inc(v_traceState_3436_);
lean_inc(v_auxDeclNGen_3435_);
lean_inc(v_ngen_3434_);
lean_inc(v_env_3433_);
lean_dec(v___x_3432_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3467_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v_macroScope_3427_);
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_env_3433_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_macroScope_3427_);
lean_ctor_set(v_reuseFailAlloc_3466_, 2, v_ngen_3434_);
lean_ctor_set(v_reuseFailAlloc_3466_, 3, v_auxDeclNGen_3435_);
lean_ctor_set(v_reuseFailAlloc_3466_, 4, v_traceState_3436_);
lean_ctor_set(v_reuseFailAlloc_3466_, 5, v_cache_3437_);
lean_ctor_set(v_reuseFailAlloc_3466_, 6, v_recordedDeps_3438_);
lean_ctor_set(v_reuseFailAlloc_3466_, 7, v_messages_3439_);
lean_ctor_set(v_reuseFailAlloc_3466_, 8, v_infoState_3440_);
lean_ctor_set(v_reuseFailAlloc_3466_, 9, v_snapshotTasks_3441_);
v___x_3446_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = lean_st_ref_put(v___y_3400_, v___x_3446_);
v___x_3448_ = l_List_reverse___redArg(v_traceMsgs_3428_);
v___x_3449_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(v___x_3448_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; 
v_unused_3457_ = lean_ctor_get(v___x_3449_, 0);
lean_dec(v_unused_3457_);
v___x_3451_ = v___x_3449_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_dec(v___x_3449_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v_a_3426_);
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3426_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec(v_a_3426_);
v_a_3458_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3449_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3449_);
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
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v_traceMsgs_3428_);
lean_dec(v_macroScope_3427_);
lean_dec(v_a_3426_);
v_a_3469_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3431_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3431_);
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
lean_object* v_a_3477_; 
v_a_3477_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3424_, 2);
if (lean_obj_tag(v_a_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v_a_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v_a_3478_ = lean_ctor_get(v_a_3477_, 0);
lean_inc(v_a_3478_);
v_a_3479_ = lean_ctor_get(v_a_3477_, 1);
lean_inc_ref(v_a_3479_);
lean_dec_ref_known(v_a_3477_, 2);
v___x_3480_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___closed__0));
v___x_3481_ = lean_string_dec_eq(v_a_3479_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3482_, 0, v_a_3479_);
v___x_3483_ = l_Lean_MessageData_ofFormat(v___x_3482_);
v___x_3484_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_a_3478_, v___x_3483_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v_a_3478_);
return v___x_3484_;
}
else
{
lean_object* v___x_3485_; 
lean_dec_ref(v_a_3479_);
v___x_3485_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(v_a_3478_);
return v___x_3485_;
}
}
else
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_x_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(lean_object* v___x_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_toCold_3501_; lean_object* v_quotContext_3502_; lean_object* v_currMacroScope_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_toCold_3501_ = lean_ctor_get(v___y_3498_, 0);
lean_inc_ref(v_toCold_3501_);
lean_dec_ref(v___y_3498_);
v_quotContext_3502_ = lean_ctor_get(v_toCold_3501_, 8);
lean_inc(v_quotContext_3502_);
v_currMacroScope_3503_ = lean_ctor_get(v_toCold_3501_, 9);
lean_inc(v_currMacroScope_3503_);
lean_dec_ref(v_toCold_3501_);
v___x_3504_ = l_Lean_addMacroScope(v_quotContext_3502_, v___x_3497_, v_currMacroScope_3503_);
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v___x_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(v___x_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___f_3519_; lean_object* v___x_3520_; 
v___f_3519_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__2));
v___x_3520_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3519_, v___y_3516_, v___y_3517_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___boxed(lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_ref_3525_, uint8_t v_canonical_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3544_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3538_ = v___x_3535_;
v_isShared_3539_ = v_isSharedCheck_3544_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3544_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3540_ = l_Lean_mkIdentFrom(v_ref_3525_, v_a_3536_, v_canonical_3526_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v___x_3540_);
v___x_3542_ = v___x_3538_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
v_a_3545_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3535_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3535_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_ref_3553_, lean_object* v_canonical_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
uint8_t v_canonical_boxed_3563_; lean_object* v_res_3564_; 
v_canonical_boxed_3563_ = lean_unbox(v_canonical_3554_);
v_res_3564_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_ref_3553_, v_canonical_boxed_3563_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v_ref_3553_);
return v_res_3564_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__0));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3574_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13));
v___x_3575_ = l_Lean_Name_append(v___x_3574_, v___x_3573_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3578_ = l_Lean_stringToMessageData(v___x_3577_);
return v___x_3578_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3581_ = l_Lean_stringToMessageData(v___x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3588_, lean_object* v_letOrReassign_3589_, lean_object* v_decl_3590_, lean_object* v_tk_3591_, lean_object* v_dec_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3588_, v_letOrReassign_3589_, v_decl_3590_, v_tk_3591_, v_dec_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
lean_dec(v_a_3595_);
lean_dec_ref(v_a_3594_);
lean_dec_ref(v_a_3593_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3602_, lean_object* v_letOrReassign_3603_, lean_object* v_decl_3604_, lean_object* v_tk_3605_, lean_object* v_dec_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_config_3602_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v___x_3616_; 
lean_dec_ref_known(v___x_3615_, 1);
lean_inc(v_decl_3604_);
v___x_3616_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3604_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3618_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3603_, v_a_3617_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v___x_3619_; 
lean_dec_ref_known(v___x_3618_, 1);
v___x_3619_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3606_, v_tk_3605_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; lean_object* v___y_3622_; lean_object* v___y_3623_; uint8_t v___y_3624_; lean_object* v___y_3625_; uint8_t v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v_rhs_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3650_; lean_object* v___y_3651_; uint8_t v___y_3652_; uint8_t v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; uint8_t v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v_xType_x3f_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; uint8_t v___y_3719_; uint8_t v___y_3720_; uint8_t v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; uint8_t v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; uint8_t v___y_3737_; lean_object* v___y_3796_; uint8_t v___y_3797_; lean_object* v___y_3798_; uint8_t v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; uint8_t v___y_3802_; uint8_t v___y_3803_; lean_object* v_id_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v_decl_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___x_3908_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3619_, 1);
v___x_3908_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_3603_, v_a_3617_, v_a_3607_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3603_, v_decl_3604_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
if (lean_obj_tag(v___x_3910_) == 0)
{
uint8_t v___x_3911_; 
v___x_3911_ = lean_unbox(v_a_3909_);
lean_dec(v_a_3909_);
if (v___x_3911_ == 0)
{
lean_object* v_a_3912_; 
v_a_3912_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3910_, 1);
v_decl_3823_ = v_a_3912_;
v___y_3824_ = v_a_3607_;
v___y_3825_ = v_a_3608_;
v___y_3826_ = v_a_3609_;
v___y_3827_ = v_a_3610_;
v___y_3828_ = v_a_3611_;
v___y_3829_ = v_a_3612_;
v___y_3830_ = v_a_3613_;
goto v___jp_3822_;
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3914_; 
v_a_3913_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3914_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(v_a_3913_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v_decl_3823_ = v_a_3915_;
v___y_3824_ = v_a_3607_;
v___y_3825_ = v_a_3608_;
v___y_3826_ = v_a_3609_;
v___y_3827_ = v_a_3610_;
v___y_3828_ = v_a_3611_;
v___y_3829_ = v_a_3612_;
v___y_3830_ = v_a_3613_;
goto v___jp_3822_;
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_tk_3605_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v_a_3916_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3914_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3914_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v_a_3909_);
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_tk_3605_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v_a_3924_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3910_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3910_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_tk_3605_);
lean_dec(v_decl_3604_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v_a_3932_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3908_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3908_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
v___jp_3621_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___f_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3639_ = lean_box(v___y_3624_);
v___x_3640_ = lean_box(v___y_3626_);
lean_inc_ref(v___y_3627_);
lean_inc_ref(v___y_3625_);
lean_inc_ref(v___y_3622_);
v___f_3641_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 19, 10);
lean_closure_set(v___f_3641_, 0, v_rhs_3631_);
lean_closure_set(v___f_3641_, 1, v___x_3639_);
lean_closure_set(v___f_3641_, 2, v_config_3602_);
lean_closure_set(v___f_3641_, 3, v___y_3628_);
lean_closure_set(v___f_3641_, 4, v___x_3640_);
lean_closure_set(v___f_3641_, 5, v___y_3622_);
lean_closure_set(v___f_3641_, 6, v___y_3625_);
lean_closure_set(v___f_3641_, 7, v___y_3627_);
lean_closure_set(v___f_3641_, 8, v___y_3623_);
lean_closure_set(v___f_3641_, 9, v___y_3629_);
v___x_3642_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3642_, 0, v_a_3620_);
v___x_3643_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3643_, 0, v_letOrReassign_3603_);
lean_closure_set(v___x_3643_, 1, v_a_3617_);
lean_closure_set(v___x_3643_, 2, v___x_3642_);
v___x_3644_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1);
v___x_3645_ = l_Lean_MessageData_ofSyntax(v___y_3630_);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3644_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = lean_box(0);
v___x_3648_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3646_, v___x_3643_, v___f_3641_, v___x_3647_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
return v___x_3648_;
}
v___jp_3649_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = lean_unsigned_to_nat(4u);
v___x_3672_ = l_Lean_Syntax_getArg(v___y_3661_, v___x_3671_);
lean_dec(v___y_3661_);
if (lean_obj_tag(v_xType_x3f_3663_) == 0)
{
lean_inc(v___y_3657_);
v___y_3622_ = v___y_3650_;
v___y_3623_ = v___y_3651_;
v___y_3624_ = v___y_3652_;
v___y_3625_ = v___y_3654_;
v___y_3626_ = v___y_3653_;
v___y_3627_ = v___y_3655_;
v___y_3628_ = v___y_3656_;
v___y_3629_ = v___y_3657_;
v___y_3630_ = v___y_3657_;
v_rhs_3631_ = v___x_3672_;
v___y_3632_ = v___y_3664_;
v___y_3633_ = v___y_3665_;
v___y_3634_ = v___y_3666_;
v___y_3635_ = v___y_3667_;
v___y_3636_ = v___y_3668_;
v___y_3637_ = v___y_3669_;
v___y_3638_ = v___y_3670_;
goto v___jp_3621_;
}
else
{
lean_object* v_toCold_3673_; lean_object* v_val_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3717_; 
v_toCold_3673_ = lean_ctor_get(v___y_3669_, 0);
v_val_3674_ = lean_ctor_get(v_xType_x3f_3663_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_xType_x3f_3663_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3676_ = v_xType_x3f_3663_;
v_isShared_3677_ = v_isSharedCheck_3717_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_val_3674_);
lean_dec(v_xType_x3f_3663_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3717_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_ref_3678_; lean_object* v_quotContext_3679_; lean_object* v_currMacroScope_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
v_ref_3678_ = lean_ctor_get(v___y_3669_, 2);
v_quotContext_3679_ = lean_ctor_get(v_toCold_3673_, 8);
v_currMacroScope_3680_ = lean_ctor_get(v_toCold_3673_, 9);
v___x_3681_ = l_Lean_SourceInfo_fromRef(v_ref_3678_, v___y_3659_);
v___x_3682_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__15));
lean_inc_ref_n(v___y_3662_, 2);
lean_inc_ref_n(v___y_3660_, 2);
lean_inc_ref_n(v___y_3658_, 3);
v___x_3683_ = l_Lean_Name_mkStr4(v___y_3658_, v___y_3660_, v___y_3662_, v___x_3682_);
v___x_3684_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__17));
v___x_3685_ = l_Lean_Name_mkStr4(v___y_3658_, v___y_3660_, v___y_3662_, v___x_3684_);
v___x_3686_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_3681_);
v___x_3687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3681_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3689_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3690_ = lean_box(0);
lean_inc(v_currMacroScope_3680_);
lean_inc(v_quotContext_3679_);
v___x_3691_ = l_Lean_addMacroScope(v_quotContext_3679_, v___x_3690_, v_currMacroScope_3680_);
v___x_3692_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24));
v___x_3693_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25));
v___x_3694_ = l_Lean_Name_mkStr3(v___y_3658_, v___x_3692_, v___x_3693_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set_tag(v___x_3676_, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3694_);
v___x_3696_ = v___x_3676_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3697_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__28));
lean_inc_ref_n(v___y_3658_, 2);
v___x_3698_ = l_Lean_Name_mkStr2(v___y_3658_, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
lean_inc_ref(v___y_3662_);
lean_inc_ref(v___y_3660_);
v___x_3700_ = l_Lean_Name_mkStr3(v___y_3658_, v___y_3660_, v___y_3662_);
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
v___x_3702_ = lean_box(0);
v___x_3703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3699_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3696_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
lean_inc_n(v___x_3681_, 6);
v___x_3706_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3681_);
lean_ctor_set(v___x_3706_, 1, v___x_3689_);
lean_ctor_set(v___x_3706_, 2, v___x_3691_);
lean_ctor_set(v___x_3706_, 3, v___x_3705_);
v___x_3707_ = l_Lean_Syntax_node1(v___x_3681_, v___x_3688_, v___x_3706_);
v___x_3708_ = l_Lean_Syntax_node2(v___x_3681_, v___x_3685_, v___x_3687_, v___x_3707_);
v___x_3709_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3681_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3712_ = l_Lean_Syntax_node1(v___x_3681_, v___x_3711_, v_val_3674_);
v___x_3713_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3681_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = l_Lean_Syntax_node5(v___x_3681_, v___x_3683_, v___x_3708_, v___x_3672_, v___x_3710_, v___x_3712_, v___x_3714_);
lean_inc(v___y_3657_);
v___y_3622_ = v___y_3650_;
v___y_3623_ = v___y_3651_;
v___y_3624_ = v___y_3652_;
v___y_3625_ = v___y_3654_;
v___y_3626_ = v___y_3653_;
v___y_3627_ = v___y_3655_;
v___y_3628_ = v___y_3656_;
v___y_3629_ = v___y_3657_;
v___y_3630_ = v___y_3657_;
v_rhs_3631_ = v___x_3715_;
v___y_3632_ = v___y_3664_;
v___y_3633_ = v___y_3665_;
v___y_3634_ = v___y_3666_;
v___y_3635_ = v___y_3667_;
v___y_3636_ = v___y_3668_;
v___y_3637_ = v___y_3669_;
v___y_3638_ = v___y_3670_;
goto v___jp_3621_;
}
}
}
}
v___jp_3718_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___f_3741_; lean_object* v___x_3742_; 
v___x_3738_ = lean_box(v___y_3721_);
v___x_3739_ = lean_box(v___y_3719_);
v___x_3740_ = lean_box(v___y_3737_);
v___f_3741_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3741_, 0, v___y_3725_);
lean_closure_set(v___f_3741_, 1, v___y_3722_);
lean_closure_set(v___f_3741_, 2, v___x_3738_);
lean_closure_set(v___f_3741_, 3, v___x_3739_);
lean_closure_set(v___f_3741_, 4, v___y_3727_);
lean_closure_set(v___f_3741_, 5, v___x_3740_);
v___x_3742_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___y_3733_, v___f_3741_, v___y_3736_, v___y_3734_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3729_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v_toCold_3744_; lean_object* v_options_3745_; lean_object* v_fst_3746_; lean_object* v_snd_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3786_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v_toCold_3744_ = lean_ctor_get(v___y_3732_, 0);
v_options_3745_ = lean_ctor_get(v_toCold_3744_, 2);
v_fst_3746_ = lean_ctor_get(v_a_3743_, 0);
v_snd_3747_ = lean_ctor_get(v_a_3743_, 1);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_a_3743_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3749_ = v_a_3743_;
v_isShared_3750_ = v_isSharedCheck_3786_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_snd_3747_);
lean_inc(v_fst_3746_);
lean_dec(v_a_3743_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3786_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v_inheritedTraceOptions_3751_; uint8_t v_hasTrace_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___f_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v_inheritedTraceOptions_3751_ = lean_ctor_get(v_toCold_3744_, 11);
v_hasTrace_3752_ = lean_ctor_get_uint8(v_options_3745_, sizeof(void*)*1);
v___x_3753_ = lean_box(v___y_3720_);
v___x_3754_ = lean_box(v___y_3724_);
v___x_3755_ = lean_box(v___y_3737_);
v___x_3756_ = lean_box(v___y_3721_);
lean_inc(v_snd_3747_);
v___f_3757_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 19, 10);
lean_closure_set(v___f_3757_, 0, v___y_3726_);
lean_closure_set(v___f_3757_, 1, v___y_3723_);
lean_closure_set(v___f_3757_, 2, v_a_3620_);
lean_closure_set(v___f_3757_, 3, v_letOrReassign_3603_);
lean_closure_set(v___f_3757_, 4, v_a_3617_);
lean_closure_set(v___f_3757_, 5, v___x_3753_);
lean_closure_set(v___f_3757_, 6, v___x_3754_);
lean_closure_set(v___f_3757_, 7, v_snd_3747_);
lean_closure_set(v___f_3757_, 8, v___x_3755_);
lean_closure_set(v___f_3757_, 9, v___x_3756_);
v___x_3758_ = l_Lean_Syntax_getId(v___y_3735_);
lean_dec(v___y_3735_);
v___x_3759_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3758_);
if (v_hasTrace_3752_ == 0)
{
lean_object* v___x_3760_; 
lean_del_object(v___x_3749_);
v___x_3760_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3758_, v_fst_3746_, v_snd_3747_, v___f_3757_, v___y_3737_, v___x_3759_, v___y_3728_, v___y_3736_, v___y_3734_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3729_);
return v___x_3760_;
}
else
{
lean_object* v___x_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3761_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3762_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3763_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3751_, v_options_3745_, v___x_3762_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
lean_del_object(v___x_3749_);
v___x_3764_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3758_, v_fst_3746_, v_snd_3747_, v___f_3757_, v___y_3737_, v___x_3759_, v___y_3728_, v___y_3736_, v___y_3734_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3729_);
return v___x_3764_;
}
else
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
lean_inc(v___x_3758_);
v___x_3765_ = l_Lean_MessageData_ofName(v___x_3758_);
v___x_3766_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3750_ == 0)
{
lean_ctor_set_tag(v___x_3749_, 7);
lean_ctor_set(v___x_3749_, 1, v___x_3766_);
lean_ctor_set(v___x_3749_, 0, v___x_3765_);
v___x_3768_ = v___x_3749_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
lean_inc(v_fst_3746_);
v___x_3769_ = l_Lean_MessageData_ofExpr(v_fst_3746_);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3768_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3770_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
lean_inc(v_snd_3747_);
v___x_3773_ = l_Lean_MessageData_ofExpr(v_snd_3747_);
v___x_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3761_, v___x_3774_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3729_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v___x_3776_; 
lean_dec_ref_known(v___x_3775_, 1);
v___x_3776_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3758_, v_fst_3746_, v_snd_3747_, v___f_3757_, v___y_3737_, v___x_3759_, v___y_3728_, v___y_3736_, v___y_3734_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3729_);
return v___x_3776_;
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec(v___x_3758_);
lean_dec_ref(v___f_3757_);
lean_dec(v_snd_3747_);
lean_dec(v_fst_3746_);
v_a_3777_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3775_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3775_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
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
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec(v___y_3735_);
lean_dec(v___y_3726_);
lean_dec(v___y_3723_);
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_letOrReassign_3603_);
v_a_3787_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3742_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3742_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
v___jp_3795_:
{
uint8_t v_nondep_3812_; 
v_nondep_3812_ = lean_ctor_get_uint8(v_config_3602_, sizeof(void*)*1);
if (v_nondep_3812_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3603_) == 1)
{
uint8_t v_usedOnly_3813_; uint8_t v_zeta_3814_; lean_object* v_eq_x3f_3815_; 
v_usedOnly_3813_ = lean_ctor_get_uint8(v_config_3602_, sizeof(void*)*1 + 1);
v_zeta_3814_ = lean_ctor_get_uint8(v_config_3602_, sizeof(void*)*1 + 2);
v_eq_x3f_3815_ = lean_ctor_get(v_config_3602_, 0);
lean_inc(v_eq_x3f_3815_);
lean_dec_ref(v_config_3602_);
lean_inc(v_id_3804_);
v___y_3719_ = v___y_3797_;
v___y_3720_ = v_zeta_3814_;
v___y_3721_ = v___y_3799_;
v___y_3722_ = v___y_3798_;
v___y_3723_ = v_eq_x3f_3815_;
v___y_3724_ = v_usedOnly_3813_;
v___y_3725_ = v___y_3800_;
v___y_3726_ = v_id_3804_;
v___y_3727_ = v___y_3801_;
v___y_3728_ = v___y_3805_;
v___y_3729_ = v___y_3811_;
v___y_3730_ = v___y_3808_;
v___y_3731_ = v___y_3809_;
v___y_3732_ = v___y_3810_;
v___y_3733_ = v___y_3796_;
v___y_3734_ = v___y_3807_;
v___y_3735_ = v_id_3804_;
v___y_3736_ = v___y_3806_;
v___y_3737_ = v___y_3803_;
goto v___jp_3718_;
}
else
{
uint8_t v_usedOnly_3816_; uint8_t v_zeta_3817_; lean_object* v_eq_x3f_3818_; 
v_usedOnly_3816_ = lean_ctor_get_uint8(v_config_3602_, sizeof(void*)*1 + 1);
v_zeta_3817_ = lean_ctor_get_uint8(v_config_3602_, sizeof(void*)*1 + 2);
v_eq_x3f_3818_ = lean_ctor_get(v_config_3602_, 0);
lean_inc(v_eq_x3f_3818_);
lean_dec_ref(v_config_3602_);
lean_inc(v_id_3804_);
v___y_3719_ = v___y_3797_;
v___y_3720_ = v_zeta_3817_;
v___y_3721_ = v___y_3799_;
v___y_3722_ = v___y_3798_;
v___y_3723_ = v_eq_x3f_3818_;
v___y_3724_ = v_usedOnly_3816_;
v___y_3725_ = v___y_3800_;
v___y_3726_ = v_id_3804_;
v___y_3727_ = v___y_3801_;
v___y_3728_ = v___y_3805_;
v___y_3729_ = v___y_3811_;
v___y_3730_ = v___y_3808_;
v___y_3731_ = v___y_3809_;
v___y_3732_ = v___y_3810_;
v___y_3733_ = v___y_3796_;
v___y_3734_ = v___y_3807_;
v___y_3735_ = v_id_3804_;
v___y_3736_ = v___y_3806_;
v___y_3737_ = v___y_3802_;
goto v___jp_3718_;
}
}
else
{
uint8_t v_usedOnly_3819_; uint8_t v_zeta_3820_; lean_object* v_eq_x3f_3821_; 
v_usedOnly_3819_ = lean_ctor_get_uint8(v_config_3602_, sizeof(void*)*1 + 1);
v_zeta_3820_ = lean_ctor_get_uint8(v_config_3602_, sizeof(void*)*1 + 2);
v_eq_x3f_3821_ = lean_ctor_get(v_config_3602_, 0);
lean_inc(v_eq_x3f_3821_);
lean_dec_ref(v_config_3602_);
lean_inc(v_id_3804_);
v___y_3719_ = v___y_3797_;
v___y_3720_ = v_zeta_3820_;
v___y_3721_ = v___y_3799_;
v___y_3722_ = v___y_3798_;
v___y_3723_ = v_eq_x3f_3821_;
v___y_3724_ = v_usedOnly_3819_;
v___y_3725_ = v___y_3800_;
v___y_3726_ = v_id_3804_;
v___y_3727_ = v___y_3801_;
v___y_3728_ = v___y_3805_;
v___y_3729_ = v___y_3811_;
v___y_3730_ = v___y_3808_;
v___y_3731_ = v___y_3809_;
v___y_3732_ = v___y_3810_;
v___y_3733_ = v___y_3796_;
v___y_3734_ = v___y_3807_;
v___y_3735_ = v_id_3804_;
v___y_3736_ = v___y_3806_;
v___y_3737_ = v___y_3803_;
goto v___jp_3718_;
}
}
v___jp_3822_:
{
lean_object* v_doBlockResultType_3831_; lean_object* v___x_3832_; 
v_doBlockResultType_3831_ = lean_ctor_get(v___y_3824_, 3);
lean_inc_ref(v_doBlockResultType_3831_);
v___x_3832_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3831_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3907_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3835_ = v___x_3832_;
v_isShared_3836_ = v_isSharedCheck_3907_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3907_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v___x_3837_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3838_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3839_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3840_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_3823_);
v___x_3841_ = l_Lean_Syntax_isOfKind(v_decl_3823_, v___x_3840_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; 
lean_del_object(v___x_3835_);
lean_dec(v_a_3833_);
lean_dec(v_decl_3823_);
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_tk_3605_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v___x_3842_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3842_;
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v___x_3843_ = lean_unsigned_to_nat(0u);
v___x_3844_ = l_Lean_Syntax_getArg(v_decl_3823_, v___x_3843_);
lean_dec(v_decl_3823_);
v___x_3845_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__10));
lean_inc(v___x_3844_);
v___x_3846_ = l_Lean_Syntax_isOfKind(v___x_3844_, v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; uint8_t v___x_3848_; 
lean_dec(v_tk_3605_);
v___x_3847_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3844_);
v___x_3848_ = l_Lean_Syntax_isOfKind(v___x_3844_, v___x_3847_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; uint8_t v___x_3850_; 
lean_del_object(v___x_3835_);
lean_dec(v_a_3833_);
v___x_3849_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3844_);
v___x_3850_ = l_Lean_Syntax_isOfKind(v___x_3844_, v___x_3849_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; 
lean_dec(v___x_3844_);
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v___x_3851_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3851_;
}
else
{
lean_object* v___x_3852_; lean_object* v_id_3853_; lean_object* v_binders_3854_; lean_object* v_type_3855_; lean_object* v_value_3856_; uint8_t v___x_3857_; 
v___x_3852_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3844_);
lean_dec(v___x_3844_);
v_id_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_id_3853_);
v_binders_3854_ = lean_ctor_get(v___x_3852_, 1);
lean_inc_ref(v_binders_3854_);
v_type_3855_ = lean_ctor_get(v___x_3852_, 2);
lean_inc(v_type_3855_);
v_value_3856_ = lean_ctor_get(v___x_3852_, 3);
lean_inc(v_value_3856_);
lean_dec_ref(v___x_3852_);
v___x_3857_ = l_Lean_Syntax_isIdent(v_id_3853_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_id_3853_, v___x_3841_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
lean_dec(v_id_3853_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___x_3858_, 1);
v___y_3796_ = v_binders_3854_;
v___y_3797_ = v___x_3848_;
v___y_3798_ = v_value_3856_;
v___y_3799_ = v___x_3841_;
v___y_3800_ = v_type_3855_;
v___y_3801_ = v___x_3843_;
v___y_3802_ = v___x_3848_;
v___y_3803_ = v___x_3841_;
v_id_3804_ = v_a_3859_;
v___y_3805_ = v___y_3824_;
v___y_3806_ = v___y_3825_;
v___y_3807_ = v___y_3826_;
v___y_3808_ = v___y_3827_;
v___y_3809_ = v___y_3828_;
v___y_3810_ = v___y_3829_;
v___y_3811_ = v___y_3830_;
goto v___jp_3795_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_value_3856_);
lean_dec(v_type_3855_);
lean_dec_ref(v_binders_3854_);
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v_a_3860_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3858_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3858_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
v___y_3796_ = v_binders_3854_;
v___y_3797_ = v___x_3848_;
v___y_3798_ = v_value_3856_;
v___y_3799_ = v___x_3841_;
v___y_3800_ = v_type_3855_;
v___y_3801_ = v___x_3843_;
v___y_3802_ = v___x_3848_;
v___y_3803_ = v___x_3841_;
v_id_3804_ = v_id_3853_;
v___y_3805_ = v___y_3824_;
v___y_3806_ = v___y_3825_;
v___y_3807_ = v___y_3826_;
v___y_3808_ = v___y_3827_;
v___y_3809_ = v___y_3828_;
v___y_3810_ = v___y_3829_;
v___y_3811_ = v___y_3830_;
goto v___jp_3795_;
}
}
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = l_Lean_Syntax_getArg(v___x_3844_, v___x_3868_);
v___x_3870_ = l_Lean_Syntax_matchesNull(v___x_3869_, v___x_3843_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
lean_dec(v___x_3844_);
lean_del_object(v___x_3835_);
lean_dec(v_a_3833_);
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v___x_3871_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3871_;
}
else
{
lean_object* v___x_3872_; lean_object* v___f_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3872_ = lean_box(v___x_3846_);
v___f_3873_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 10, 1);
lean_closure_set(v___f_3873_, 0, v___x_3872_);
v___x_3874_ = l_Lean_Syntax_getArg(v___x_3844_, v___x_3843_);
v___x_3875_ = lean_unsigned_to_nat(2u);
v___x_3876_ = l_Lean_Syntax_getArg(v___x_3844_, v___x_3875_);
v___x_3877_ = l_Lean_Syntax_isNone(v___x_3876_);
if (v___x_3877_ == 0)
{
uint8_t v___x_3878_; 
lean_inc(v___x_3876_);
v___x_3878_ = l_Lean_Syntax_matchesNull(v___x_3876_, v___x_3868_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; 
lean_dec(v___x_3876_);
lean_dec(v___x_3874_);
lean_dec_ref(v___f_3873_);
lean_dec(v___x_3844_);
lean_del_object(v___x_3835_);
lean_dec(v_a_3833_);
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v___x_3879_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3879_;
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3880_ = l_Lean_Syntax_getArg(v___x_3876_, v___x_3843_);
lean_dec(v___x_3876_);
v___x_3881_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3880_);
v___x_3882_ = l_Lean_Syntax_isOfKind(v___x_3880_, v___x_3881_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3883_; 
lean_dec(v___x_3880_);
lean_dec(v___x_3874_);
lean_dec_ref(v___f_3873_);
lean_dec(v___x_3844_);
lean_del_object(v___x_3835_);
lean_dec(v_a_3833_);
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v___x_3883_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3883_;
}
else
{
lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3884_ = l_Lean_Syntax_getArg(v___x_3880_, v___x_3868_);
lean_dec(v___x_3880_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 1);
lean_ctor_set(v___x_3835_, 0, v___x_3884_);
v___x_3886_ = v___x_3835_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
v___y_3650_ = v___x_3837_;
v___y_3651_ = v___f_3873_;
v___y_3652_ = v___x_3846_;
v___y_3653_ = v___x_3841_;
v___y_3654_ = v___x_3838_;
v___y_3655_ = v___x_3839_;
v___y_3656_ = v_a_3833_;
v___y_3657_ = v___x_3874_;
v___y_3658_ = v___x_3837_;
v___y_3659_ = v___x_3846_;
v___y_3660_ = v___x_3838_;
v___y_3661_ = v___x_3844_;
v___y_3662_ = v___x_3839_;
v_xType_x3f_3663_ = v___x_3886_;
v___y_3664_ = v___y_3824_;
v___y_3665_ = v___y_3825_;
v___y_3666_ = v___y_3826_;
v___y_3667_ = v___y_3827_;
v___y_3668_ = v___y_3828_;
v___y_3669_ = v___y_3829_;
v___y_3670_ = v___y_3830_;
goto v___jp_3649_;
}
}
}
}
else
{
lean_object* v___x_3888_; 
lean_dec(v___x_3876_);
lean_del_object(v___x_3835_);
v___x_3888_ = lean_box(0);
v___y_3650_ = v___x_3837_;
v___y_3651_ = v___f_3873_;
v___y_3652_ = v___x_3846_;
v___y_3653_ = v___x_3841_;
v___y_3654_ = v___x_3838_;
v___y_3655_ = v___x_3839_;
v___y_3656_ = v_a_3833_;
v___y_3657_ = v___x_3874_;
v___y_3658_ = v___x_3837_;
v___y_3659_ = v___x_3846_;
v___y_3660_ = v___x_3838_;
v___y_3661_ = v___x_3844_;
v___y_3662_ = v___x_3839_;
v_xType_x3f_3663_ = v___x_3888_;
v___y_3664_ = v___y_3824_;
v___y_3665_ = v___y_3825_;
v___y_3666_ = v___y_3826_;
v___y_3667_ = v___y_3827_;
v___y_3668_ = v___y_3828_;
v___y_3669_ = v___y_3829_;
v___y_3670_ = v___y_3830_;
goto v___jp_3649_;
}
}
}
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_del_object(v___x_3835_);
lean_dec(v_a_3833_);
lean_dec(v_a_3617_);
v___x_3889_ = lean_box(v___x_3841_);
lean_inc(v___x_3844_);
v___x_3890_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3890_, 0, v___x_3844_);
lean_closure_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3890_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v_ref_3893_; uint8_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v_ref_3893_ = lean_ctor_get(v___y_3829_, 2);
v___x_3894_ = 0;
v___x_3895_ = l_Lean_SourceInfo_fromRef(v_ref_3893_, v___x_3894_);
v___x_3896_ = l_Lean_Syntax_node1(v___x_3895_, v___x_3840_, v_a_3892_);
lean_inc(v___x_3896_);
v___x_3897_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3897_, 0, v_config_3602_);
lean_closure_set(v___x_3897_, 1, v_letOrReassign_3603_);
lean_closure_set(v___x_3897_, 2, v___x_3896_);
lean_closure_set(v___x_3897_, 3, v_tk_3605_);
lean_closure_set(v___x_3897_, 4, v_a_3620_);
v___x_3898_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v___x_3844_, v___x_3896_, v___x_3897_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
return v___x_3898_;
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec(v___x_3844_);
lean_dec(v_a_3620_);
lean_dec(v_tk_3605_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v_a_3899_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3891_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3891_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
}
}
else
{
lean_dec(v_decl_3823_);
lean_dec(v_a_3620_);
lean_dec(v_a_3617_);
lean_dec(v_tk_3605_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
return v___x_3832_;
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec(v_a_3617_);
lean_dec(v_tk_3605_);
lean_dec(v_decl_3604_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v_a_3940_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3619_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3619_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec(v_a_3617_);
lean_dec_ref(v_dec_3606_);
lean_dec(v_tk_3605_);
lean_dec(v_decl_3604_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v_a_3948_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3618_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3618_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref(v_dec_3606_);
lean_dec(v_tk_3605_);
lean_dec(v_decl_3604_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v_a_3956_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3616_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3616_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec_ref(v_dec_3606_);
lean_dec(v_tk_3605_);
lean_dec(v_decl_3604_);
lean_dec(v_letOrReassign_3603_);
lean_dec_ref(v_config_3602_);
v_a_3964_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3615_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3615_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3972_, lean_object* v_x_3973_, lean_object* v_x_3974_, lean_object* v_x_3975_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3973_, v_x_3974_, v_x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_cls_3977_, lean_object* v_msg_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_3977_, v_msg_3978_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_cls_3988_, lean_object* v_msg_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_cls_3988_, v_msg_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec_ref(v___y_3990_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_4004_, v___y_4005_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___boxed(lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec_ref(v___y_4008_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_00_u03b1_4017_, lean_object* v_beforeStx_4018_, lean_object* v_afterStx_4019_, lean_object* v_x_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_beforeStx_4018_, v_afterStx_4019_, v_x_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_00_u03b1_4030_, lean_object* v_beforeStx_4031_, lean_object* v_afterStx_4032_, lean_object* v_x_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_00_u03b1_4030_, v_beforeStx_4031_, v_afterStx_4032_, v_x_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec_ref(v___y_4034_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11(lean_object* v_00_u03b1_4043_, lean_object* v_x_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v_x_4044_, v___y_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___boxed(lean_object* v_00_u03b1_4048_, lean_object* v_x_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11(v_00_u03b1_4048_, v_x_4049_, v___y_4050_, v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v_x_4049_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(lean_object* v_00_u03b1_4053_, lean_object* v_ref_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(v_ref_4054_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___boxed(lean_object* v_00_u03b1_4064_, lean_object* v_ref_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(v_00_u03b1_4064_, v_ref_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_4075_, lean_object* v_x_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_4086_, lean_object* v_x_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_4086_, v_x_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec_ref(v___y_4088_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_4097_, lean_object* v_x_4098_, size_t v_x_4099_, size_t v_x_4100_, lean_object* v_x_4101_, lean_object* v_x_4102_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_4098_, v_x_4099_, v_x_4100_, v_x_4101_, v_x_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4104_, lean_object* v_x_4105_, lean_object* v_x_4106_, lean_object* v_x_4107_, lean_object* v_x_4108_, lean_object* v_x_4109_){
_start:
{
size_t v_x_92520__boxed_4110_; size_t v_x_92521__boxed_4111_; lean_object* v_res_4112_; 
v_x_92520__boxed_4110_ = lean_unbox_usize(v_x_4106_);
lean_dec(v_x_4106_);
v_x_92521__boxed_4111_ = lean_unbox_usize(v_x_4107_);
lean_dec(v_x_4107_);
v_res_4112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_4104_, v_x_4105_, v_x_92520__boxed_4110_, v_x_92521__boxed_4111_, v_x_4108_, v_x_4109_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(lean_object* v_00_u03b1_4113_, lean_object* v_stx_4114_, lean_object* v_output_4115_, lean_object* v_x_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_stx_4114_, v_output_4115_, v_x_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4125_, lean_object* v_stx_4126_, lean_object* v_output_4127_, lean_object* v_x_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(v_00_u03b1_4125_, v_stx_4126_, v_output_4127_, v_x_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(lean_object* v_as_4137_, lean_object* v_as_x27_4138_, lean_object* v_b_4139_, lean_object* v_a_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v___x_4149_; 
v___x_4149_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(v_as_x27_4138_, v_b_4139_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___boxed(lean_object* v_as_4150_, lean_object* v_as_x27_4151_, lean_object* v_b_4152_, lean_object* v_a_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(v_as_4150_, v_as_x27_4151_, v_b_4152_, v_a_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v_as_x27_4151_);
lean_dec(v_as_4150_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4163_, lean_object* v_n_4164_, lean_object* v_k_4165_, lean_object* v_v_4166_){
_start:
{
lean_object* v___x_4167_; 
v___x_4167_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(v_n_4164_, v_k_4165_, v_v_4166_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_4168_, size_t v_depth_4169_, lean_object* v_keys_4170_, lean_object* v_vals_4171_, lean_object* v_heq_4172_, lean_object* v_i_4173_, lean_object* v_entries_4174_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_depth_4169_, v_keys_4170_, v_vals_4171_, v_i_4173_, v_entries_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_4176_, lean_object* v_depth_4177_, lean_object* v_keys_4178_, lean_object* v_vals_4179_, lean_object* v_heq_4180_, lean_object* v_i_4181_, lean_object* v_entries_4182_){
_start:
{
size_t v_depth_boxed_4183_; lean_object* v_res_4184_; 
v_depth_boxed_4183_ = lean_unbox_usize(v_depth_4177_);
lean_dec(v_depth_4177_);
v_res_4184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(v_00_u03b2_4176_, v_depth_boxed_4183_, v_keys_4178_, v_vals_4179_, v_heq_4180_, v_i_4181_, v_entries_4182_);
lean_dec_ref(v_vals_4179_);
lean_dec_ref(v_keys_4178_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17(lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(v___y_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___boxed(lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17(v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_4201_, lean_object* v_x_4202_, lean_object* v_mkInfoTree_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(v_x_4202_, v_mkInfoTree_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4212_, lean_object* v_x_4213_, lean_object* v_mkInfoTree_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12(v_00_u03b1_4212_, v_x_4213_, v_mkInfoTree_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18(lean_object* v_00_u03b2_4223_, lean_object* v_m_4224_, lean_object* v_a_4225_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(v_m_4224_, v_a_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___boxed(lean_object* v_00_u03b2_4227_, lean_object* v_m_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18(v_00_u03b2_4227_, v_m_4228_, v_a_4229_);
lean_dec(v_a_4229_);
lean_dec_ref(v_m_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13(lean_object* v_00_u03b2_4231_, lean_object* v_x_4232_, lean_object* v_x_4233_, lean_object* v_x_4234_, lean_object* v_x_4235_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13___redArg(v_x_4232_, v_x_4233_, v_x_4234_, v_x_4235_);
return v___x_4236_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20(lean_object* v_00_u03b2_4237_, lean_object* v_x_4238_, lean_object* v_x_4239_){
_start:
{
uint8_t v___x_4240_; 
v___x_4240_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(v_x_4238_, v_x_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___boxed(lean_object* v_00_u03b2_4241_, lean_object* v_x_4242_, lean_object* v_x_4243_){
_start:
{
uint8_t v_res_4244_; lean_object* v_r_4245_; 
v_res_4244_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20(v_00_u03b2_4241_, v_x_4242_, v_x_4243_);
lean_dec_ref(v_x_4243_);
lean_dec_ref(v_x_4242_);
v_r_4245_ = lean_box(v_res_4244_);
return v_r_4245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23(lean_object* v_00_u03b2_4246_, lean_object* v_a_4247_, lean_object* v_x_4248_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(v_a_4247_, v_x_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___boxed(lean_object* v_00_u03b2_4250_, lean_object* v_a_4251_, lean_object* v_x_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23(v_00_u03b2_4250_, v_a_4251_, v_x_4252_);
lean_dec(v_x_4252_);
lean_dec(v_a_4251_);
return v_res_4253_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_4254_, lean_object* v_x_4255_, size_t v_x_4256_, lean_object* v_x_4257_){
_start:
{
uint8_t v___x_4258_; 
v___x_4258_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(v_x_4255_, v_x_4256_, v_x_4257_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_4259_, lean_object* v_x_4260_, lean_object* v_x_4261_, lean_object* v_x_4262_){
_start:
{
size_t v_x_92664__boxed_4263_; uint8_t v_res_4264_; lean_object* v_r_4265_; 
v_x_92664__boxed_4263_ = lean_unbox_usize(v_x_4261_);
lean_dec(v_x_4261_);
v_res_4264_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23(v_00_u03b2_4259_, v_x_4260_, v_x_92664__boxed_4263_, v_x_4262_);
lean_dec_ref(v_x_4262_);
lean_dec_ref(v_x_4260_);
v_r_4265_ = lean_box(v_res_4264_);
return v_r_4265_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26(lean_object* v_00_u03b2_4266_, lean_object* v_keys_4267_, lean_object* v_vals_4268_, lean_object* v_heq_4269_, lean_object* v_i_4270_, lean_object* v_k_4271_){
_start:
{
uint8_t v___x_4272_; 
v___x_4272_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(v_keys_4267_, v_i_4270_, v_k_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___boxed(lean_object* v_00_u03b2_4273_, lean_object* v_keys_4274_, lean_object* v_vals_4275_, lean_object* v_heq_4276_, lean_object* v_i_4277_, lean_object* v_k_4278_){
_start:
{
uint8_t v_res_4279_; lean_object* v_r_4280_; 
v_res_4279_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26(v_00_u03b2_4273_, v_keys_4274_, v_vals_4275_, v_heq_4276_, v_i_4277_, v_k_4278_);
lean_dec_ref(v_k_4278_);
lean_dec_ref(v_vals_4275_);
lean_dec_ref(v_keys_4274_);
v_r_4280_ = lean_box(v_res_4279_);
return v_r_4280_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4282_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__0));
v___x_4283_ = l_Lean_stringToMessageData(v___x_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4284_, lean_object* v_mutTk_x3f_4285_, lean_object* v_initConfig_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4285_) == 0)
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4284_, v_initConfig_4286_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_);
return v___x_4295_;
}
else
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4296_ = lean_unsigned_to_nat(0u);
v___x_4297_ = l_Lean_Syntax_getArg(v_letConfigStx_4284_, v___x_4296_);
v___x_4298_ = l_Lean_Syntax_getArgs(v___x_4297_);
lean_dec(v___x_4297_);
v___x_4299_ = lean_array_get_size(v___x_4298_);
lean_dec_ref(v___x_4298_);
v___x_4300_ = lean_nat_dec_eq(v___x_4299_, v___x_4296_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
lean_dec_ref(v_initConfig_4286_);
v___x_4301_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1);
v___x_4302_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_letConfigStx_4284_, v___x_4301_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_);
lean_dec(v_letConfigStx_4284_);
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4302_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4302_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
else
{
lean_object* v___x_4311_; 
v___x_4311_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4284_, v_initConfig_4286_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_);
return v___x_4311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4312_, lean_object* v_mutTk_x3f_4313_, lean_object* v_initConfig_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4312_, v_mutTk_x3f_4313_, v_initConfig_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v_a_4319_);
lean_dec_ref(v_a_4318_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_mutTk_x3f_4313_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4339_, lean_object* v_dec_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_){
_start:
{
lean_object* v___x_4349_; uint8_t v___x_4350_; 
v___x_4349_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_stx_4339_);
v___x_4350_ = l_Lean_Syntax_isOfKind(v_stx_4339_, v___x_4349_);
if (v___x_4350_ == 0)
{
lean_object* v___x_4351_; 
lean_dec_ref(v_dec_4340_);
lean_dec(v_stx_4339_);
v___x_4351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4351_;
}
else
{
lean_object* v___x_4352_; lean_object* v_tk_4353_; lean_object* v_mutTk_x3f_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4352_ = lean_unsigned_to_nat(0u);
v_tk_4353_ = l_Lean_Syntax_getArg(v_stx_4339_, v___x_4352_);
v___x_4387_ = lean_unsigned_to_nat(1u);
v___x_4388_ = l_Lean_Syntax_getArg(v_stx_4339_, v___x_4387_);
v___x_4389_ = l_Lean_Syntax_isNone(v___x_4388_);
if (v___x_4389_ == 0)
{
uint8_t v___x_4390_; 
lean_inc(v___x_4388_);
v___x_4390_ = l_Lean_Syntax_matchesNull(v___x_4388_, v___x_4387_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; 
lean_dec(v___x_4388_);
lean_dec(v_tk_4353_);
lean_dec_ref(v_dec_4340_);
lean_dec(v_stx_4339_);
v___x_4391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4391_;
}
else
{
lean_object* v_mutTk_x3f_4392_; lean_object* v___x_4393_; 
v_mutTk_x3f_4392_ = l_Lean_Syntax_getArg(v___x_4388_, v___x_4352_);
lean_dec(v___x_4388_);
v___x_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4393_, 0, v_mutTk_x3f_4392_);
v_mutTk_x3f_4355_ = v___x_4393_;
v___y_4356_ = v_a_4341_;
v___y_4357_ = v_a_4342_;
v___y_4358_ = v_a_4343_;
v___y_4359_ = v_a_4344_;
v___y_4360_ = v_a_4345_;
v___y_4361_ = v_a_4346_;
v___y_4362_ = v_a_4347_;
goto v___jp_4354_;
}
}
else
{
lean_object* v___x_4394_; 
lean_dec(v___x_4388_);
v___x_4394_ = lean_box(0);
v_mutTk_x3f_4355_ = v___x_4394_;
v___y_4356_ = v_a_4341_;
v___y_4357_ = v_a_4342_;
v___y_4358_ = v_a_4343_;
v___y_4359_ = v_a_4344_;
v___y_4360_ = v_a_4345_;
v___y_4361_ = v_a_4346_;
v___y_4362_ = v_a_4347_;
goto v___jp_4354_;
}
v___jp_4354_:
{
lean_object* v___x_4363_; lean_object* v_config_4364_; lean_object* v___x_4365_; uint8_t v___x_4366_; 
v___x_4363_ = lean_unsigned_to_nat(2u);
v_config_4364_ = l_Lean_Syntax_getArg(v_stx_4339_, v___x_4363_);
v___x_4365_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_config_4364_);
v___x_4366_ = l_Lean_Syntax_isOfKind(v_config_4364_, v___x_4365_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; 
lean_dec(v_config_4364_);
lean_dec(v_mutTk_x3f_4355_);
lean_dec(v_tk_4353_);
lean_dec_ref(v_dec_4340_);
lean_dec(v_stx_4339_);
v___x_4367_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4367_;
}
else
{
lean_object* v___x_4368_; lean_object* v_decl_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; 
v___x_4368_ = lean_unsigned_to_nat(3u);
v_decl_4369_ = l_Lean_Syntax_getArg(v_stx_4339_, v___x_4368_);
lean_dec(v_stx_4339_);
v___x_4370_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4369_);
v___x_4371_ = l_Lean_Syntax_isOfKind(v_decl_4369_, v___x_4370_);
if (v___x_4371_ == 0)
{
lean_object* v___x_4372_; 
lean_dec(v_decl_4369_);
lean_dec(v_config_4364_);
lean_dec(v_mutTk_x3f_4355_);
lean_dec(v_tk_4353_);
lean_dec_ref(v_dec_4340_);
v___x_4372_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4372_;
}
else
{
uint8_t v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4373_ = 0;
v___x_4374_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_4375_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_config_4364_, v_mutTk_x3f_4355_, v___x_4374_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4375_, 1);
v___x_4377_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4377_, 0, v_mutTk_x3f_4355_);
lean_ctor_set_uint8(v___x_4377_, sizeof(void*)*1, v___x_4373_);
v___x_4378_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4376_, v___x_4377_, v_decl_4369_, v_tk_4353_, v_dec_4340_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
return v___x_4378_;
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec(v_decl_4369_);
lean_dec(v_mutTk_x3f_4355_);
lean_dec(v_tk_4353_);
lean_dec_ref(v_dec_4340_);
v_a_4379_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4375_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4375_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4395_, lean_object* v_dec_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_Elab_Do_elabDoLet(v_stx_4395_, v_dec_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
lean_dec(v_a_4399_);
lean_dec_ref(v_a_4398_);
lean_dec_ref(v_a_4397_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4413_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4414_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_4415_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4416_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4417_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4413_, v___x_4414_, v___x_4415_, v___x_4416_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased(lean_object* v_stx_4434_, lean_object* v_dec_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_){
_start:
{
lean_object* v___x_4444_; uint8_t v___x_4445_; 
v___x_4444_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
lean_inc(v_stx_4434_);
v___x_4445_ = l_Lean_Syntax_isOfKind(v_stx_4434_, v___x_4444_);
if (v___x_4445_ == 0)
{
lean_object* v___x_4446_; 
lean_dec_ref(v_dec_4435_);
lean_dec(v_stx_4434_);
v___x_4446_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4446_;
}
else
{
lean_object* v___x_4447_; lean_object* v_tk_4448_; lean_object* v___y_4450_; lean_object* v___y_4451_; uint8_t v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v_t_x3f_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___x_4509_; lean_object* v_mutTk_x3f_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___x_4546_; uint8_t v___x_4547_; 
v___x_4447_ = lean_unsigned_to_nat(0u);
v_tk_4448_ = l_Lean_Syntax_getArg(v_stx_4434_, v___x_4447_);
v___x_4509_ = lean_unsigned_to_nat(1u);
v___x_4546_ = l_Lean_Syntax_getArg(v_stx_4434_, v___x_4509_);
v___x_4547_ = l_Lean_Syntax_isNone(v___x_4546_);
if (v___x_4547_ == 0)
{
uint8_t v___x_4548_; 
lean_inc(v___x_4546_);
v___x_4548_ = l_Lean_Syntax_matchesNull(v___x_4546_, v___x_4509_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; 
lean_dec(v___x_4546_);
lean_dec(v_tk_4448_);
lean_dec_ref(v_dec_4435_);
lean_dec(v_stx_4434_);
v___x_4549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4549_;
}
else
{
lean_object* v_mutTk_x3f_4550_; lean_object* v___x_4551_; 
v_mutTk_x3f_4550_ = l_Lean_Syntax_getArg(v___x_4546_, v___x_4447_);
lean_dec(v___x_4546_);
v___x_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4551_, 0, v_mutTk_x3f_4550_);
v_mutTk_x3f_4511_ = v___x_4551_;
v___y_4512_ = v_a_4436_;
v___y_4513_ = v_a_4437_;
v___y_4514_ = v_a_4438_;
v___y_4515_ = v_a_4439_;
v___y_4516_ = v_a_4440_;
v___y_4517_ = v_a_4441_;
v___y_4518_ = v_a_4442_;
goto v___jp_4510_;
}
}
else
{
lean_object* v___x_4552_; 
lean_dec(v___x_4546_);
v___x_4552_ = lean_box(0);
v_mutTk_x3f_4511_ = v___x_4552_;
v___y_4512_ = v_a_4436_;
v___y_4513_ = v_a_4437_;
v___y_4514_ = v_a_4438_;
v___y_4515_ = v_a_4439_;
v___y_4516_ = v_a_4440_;
v___y_4517_ = v_a_4441_;
v___y_4518_ = v_a_4442_;
goto v___jp_4510_;
}
v___jp_4449_:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
lean_inc_ref(v___y_4461_);
v___x_4468_ = l_Array_append___redArg(v___y_4461_, v___y_4467_);
lean_dec_ref(v___y_4467_);
lean_inc(v___y_4464_);
lean_inc_n(v___y_4465_, 3);
v___x_4469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4469_, 0, v___y_4465_);
lean_ctor_set(v___x_4469_, 1, v___y_4464_);
lean_ctor_set(v___x_4469_, 2, v___x_4468_);
v___x_4470_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___y_4465_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
lean_inc(v___y_4463_);
v___x_4472_ = l_Lean_Syntax_node5(v___y_4465_, v___y_4463_, v___y_4462_, v___y_4457_, v___x_4469_, v___x_4471_, v___y_4460_);
lean_inc(v___y_4450_);
v___x_4473_ = l_Lean_Syntax_node1(v___y_4465_, v___y_4450_, v___x_4472_);
v___x_4474_ = lean_box(0);
v___x_4475_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*1, v___y_4452_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*1 + 1, v___y_4452_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*1 + 2, v___y_4452_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*1 + 3, v___y_4452_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*1 + 4, v___y_4452_);
v___x_4476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4476_, 0, v___y_4454_);
lean_ctor_set_uint8(v___x_4476_, sizeof(void*)*1, v___x_4445_);
v___x_4477_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4475_, v___x_4476_, v___x_4473_, v_tk_4448_, v_dec_4435_, v___y_4459_, v___y_4451_, v___y_4458_, v___y_4455_, v___y_4453_, v___y_4466_, v___y_4456_);
return v___x_4477_;
}
v___jp_4478_:
{
lean_object* v_ref_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; uint8_t v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_ref_4491_ = lean_ctor_get(v___y_4489_, 2);
v___x_4492_ = lean_unsigned_to_nat(4u);
v___x_4493_ = l_Lean_Syntax_getArg(v___y_4481_, v___x_4492_);
lean_dec(v___y_4481_);
v___x_4494_ = 0;
v___x_4495_ = l_Lean_SourceInfo_fromRef(v_ref_4491_, v___x_4494_);
v___x_4496_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4497_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___y_4479_);
lean_inc_n(v___x_4495_, 2);
v___x_4498_ = l_Lean_Syntax_node1(v___x_4495_, v___y_4479_, v___y_4480_);
v___x_4499_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4500_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4495_);
lean_ctor_set(v___x_4501_, 1, v___x_4499_);
lean_ctor_set(v___x_4501_, 2, v___x_4500_);
if (lean_obj_tag(v_t_x3f_4483_) == 1)
{
lean_object* v_val_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v_val_4502_ = lean_ctor_get(v_t_x3f_4483_, 0);
lean_inc(v_val_4502_);
lean_dec_ref_known(v_t_x3f_4483_, 1);
v___x_4503_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4504_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_4495_, 2);
v___x_4505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4495_);
lean_ctor_set(v___x_4505_, 1, v___x_4504_);
v___x_4506_ = l_Lean_Syntax_node2(v___x_4495_, v___x_4503_, v___x_4505_, v_val_4502_);
v___x_4507_ = l_Array_mkArray1___redArg(v___x_4506_);
v___y_4450_ = v___x_4496_;
v___y_4451_ = v___y_4485_;
v___y_4452_ = v___x_4494_;
v___y_4453_ = v___y_4488_;
v___y_4454_ = v___y_4482_;
v___y_4455_ = v___y_4487_;
v___y_4456_ = v___y_4490_;
v___y_4457_ = v___x_4501_;
v___y_4458_ = v___y_4486_;
v___y_4459_ = v___y_4484_;
v___y_4460_ = v___x_4493_;
v___y_4461_ = v___x_4500_;
v___y_4462_ = v___x_4498_;
v___y_4463_ = v___x_4497_;
v___y_4464_ = v___x_4499_;
v___y_4465_ = v___x_4495_;
v___y_4466_ = v___y_4489_;
v___y_4467_ = v___x_4507_;
goto v___jp_4449_;
}
else
{
lean_object* v___x_4508_; 
lean_dec(v_t_x3f_4483_);
v___x_4508_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4450_ = v___x_4496_;
v___y_4451_ = v___y_4485_;
v___y_4452_ = v___x_4494_;
v___y_4453_ = v___y_4488_;
v___y_4454_ = v___y_4482_;
v___y_4455_ = v___y_4487_;
v___y_4456_ = v___y_4490_;
v___y_4457_ = v___x_4501_;
v___y_4458_ = v___y_4486_;
v___y_4459_ = v___y_4484_;
v___y_4460_ = v___x_4493_;
v___y_4461_ = v___x_4500_;
v___y_4462_ = v___x_4498_;
v___y_4463_ = v___x_4497_;
v___y_4464_ = v___x_4499_;
v___y_4465_ = v___x_4495_;
v___y_4466_ = v___y_4489_;
v___y_4467_ = v___x_4508_;
goto v___jp_4449_;
}
}
v___jp_4510_:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; uint8_t v___x_4522_; 
v___x_4519_ = lean_unsigned_to_nat(2u);
v___x_4520_ = l_Lean_Syntax_getArg(v_stx_4434_, v___x_4519_);
lean_dec(v_stx_4434_);
v___x_4521_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_4520_);
v___x_4522_ = l_Lean_Syntax_isOfKind(v___x_4520_, v___x_4521_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; 
lean_dec(v___x_4520_);
lean_dec(v_mutTk_x3f_4511_);
lean_dec(v_tk_4448_);
lean_dec_ref(v_dec_4435_);
v___x_4523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4523_;
}
else
{
lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4524_ = l_Lean_Syntax_getArg(v___x_4520_, v___x_4447_);
v___x_4525_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_4524_);
v___x_4526_ = l_Lean_Syntax_isOfKind(v___x_4524_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
lean_dec(v___x_4524_);
lean_dec(v___x_4520_);
lean_dec(v_mutTk_x3f_4511_);
lean_dec(v_tk_4448_);
lean_dec_ref(v_dec_4435_);
v___x_4527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4527_;
}
else
{
lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4528_ = l_Lean_Syntax_getArg(v___x_4524_, v___x_4447_);
lean_dec(v___x_4524_);
v___x_4529_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4528_);
v___x_4530_ = l_Lean_Syntax_isOfKind(v___x_4528_, v___x_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; 
lean_dec(v___x_4528_);
lean_dec(v___x_4520_);
lean_dec(v_mutTk_x3f_4511_);
lean_dec(v_tk_4448_);
lean_dec_ref(v_dec_4435_);
v___x_4531_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4531_;
}
else
{
lean_object* v___x_4532_; uint8_t v___x_4533_; 
v___x_4532_ = l_Lean_Syntax_getArg(v___x_4520_, v___x_4509_);
v___x_4533_ = l_Lean_Syntax_matchesNull(v___x_4532_, v___x_4447_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; 
lean_dec(v___x_4528_);
lean_dec(v___x_4520_);
lean_dec(v_mutTk_x3f_4511_);
lean_dec(v_tk_4448_);
lean_dec_ref(v_dec_4435_);
v___x_4534_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4534_;
}
else
{
lean_object* v___x_4535_; uint8_t v___x_4536_; 
v___x_4535_ = l_Lean_Syntax_getArg(v___x_4520_, v___x_4519_);
v___x_4536_ = l_Lean_Syntax_isNone(v___x_4535_);
if (v___x_4536_ == 0)
{
uint8_t v___x_4537_; 
lean_inc(v___x_4535_);
v___x_4537_ = l_Lean_Syntax_matchesNull(v___x_4535_, v___x_4509_);
if (v___x_4537_ == 0)
{
lean_object* v___x_4538_; 
lean_dec(v___x_4535_);
lean_dec(v___x_4528_);
lean_dec(v___x_4520_);
lean_dec(v_mutTk_x3f_4511_);
lean_dec(v_tk_4448_);
lean_dec_ref(v_dec_4435_);
v___x_4538_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4538_;
}
else
{
lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
v___x_4539_ = l_Lean_Syntax_getArg(v___x_4535_, v___x_4447_);
lean_dec(v___x_4535_);
v___x_4540_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4539_);
v___x_4541_ = l_Lean_Syntax_isOfKind(v___x_4539_, v___x_4540_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; 
lean_dec(v___x_4539_);
lean_dec(v___x_4528_);
lean_dec(v___x_4520_);
lean_dec(v_mutTk_x3f_4511_);
lean_dec(v_tk_4448_);
lean_dec_ref(v_dec_4435_);
v___x_4542_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4542_;
}
else
{
lean_object* v_t_x3f_4543_; lean_object* v___x_4544_; 
v_t_x3f_4543_ = l_Lean_Syntax_getArg(v___x_4539_, v___x_4509_);
lean_dec(v___x_4539_);
v___x_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4544_, 0, v_t_x3f_4543_);
v___y_4479_ = v___x_4525_;
v___y_4480_ = v___x_4528_;
v___y_4481_ = v___x_4520_;
v___y_4482_ = v_mutTk_x3f_4511_;
v_t_x3f_4483_ = v___x_4544_;
v___y_4484_ = v___y_4512_;
v___y_4485_ = v___y_4513_;
v___y_4486_ = v___y_4514_;
v___y_4487_ = v___y_4515_;
v___y_4488_ = v___y_4516_;
v___y_4489_ = v___y_4517_;
v___y_4490_ = v___y_4518_;
goto v___jp_4478_;
}
}
}
else
{
lean_object* v___x_4545_; 
lean_dec(v___x_4535_);
v___x_4545_ = lean_box(0);
v___y_4479_ = v___x_4525_;
v___y_4480_ = v___x_4528_;
v___y_4481_ = v___x_4520_;
v___y_4482_ = v_mutTk_x3f_4511_;
v_t_x3f_4483_ = v___x_4545_;
v___y_4484_ = v___y_4512_;
v___y_4485_ = v___y_4513_;
v___y_4486_ = v___y_4514_;
v___y_4487_ = v___y_4515_;
v___y_4488_ = v___y_4516_;
v___y_4489_ = v___y_4517_;
v___y_4490_ = v___y_4518_;
goto v___jp_4478_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased___boxed(lean_object* v_stx_4553_, lean_object* v_dec_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l_Lean_Elab_Do_elabDoErased(v_stx_4553_, v_dec_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec_ref(v_a_4555_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1(){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4571_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4572_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4573_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1));
v___x_4574_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoErased___boxed), 10, 0);
v___x_4575_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4571_, v___x_4572_, v___x_4573_, v___x_4574_);
return v___x_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___boxed(lean_object* v_a_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1();
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0(lean_object* v_____do__lift_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
uint8_t v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4581_ = 0;
v___x_4582_ = l_Lean_SourceInfo_fromRef(v_____do__lift_4578_, v___x_4581_);
v___x_4583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
lean_ctor_set(v___x_4583_, 1, v___y_4580_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0___boxed(lean_object* v_____do__lift_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_____do__lift_4584_, v___y_4585_, v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v_____do__lift_4584_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow(lean_object* v_stx_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v___y_4635_; uint8_t v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; lean_object* v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___x_4673_; uint8_t v___x_4674_; 
v___x_4673_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
lean_inc(v_stx_4631_);
v___x_4674_ = l_Lean_Syntax_isOfKind(v_stx_4631_, v___x_4673_);
if (v___x_4674_ == 0)
{
lean_object* v___x_4675_; 
lean_dec(v_stx_4631_);
v___x_4675_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4633_);
return v___x_4675_;
}
else
{
lean_object* v___x_4676_; lean_object* v_tk_4677_; uint8_t v___y_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v___y_4694_; lean_object* v___y_4695_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v_t_x3f_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___x_4762_; lean_object* v_mutTk_x3f_4764_; lean_object* v___y_4765_; lean_object* v___y_4766_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v___x_4676_ = lean_unsigned_to_nat(0u);
v_tk_4677_ = l_Lean_Syntax_getArg(v_stx_4631_, v___x_4676_);
v___x_4762_ = lean_unsigned_to_nat(1u);
v___x_4787_ = l_Lean_Syntax_getArg(v_stx_4631_, v___x_4762_);
v___x_4788_ = l_Lean_Syntax_isNone(v___x_4787_);
if (v___x_4788_ == 0)
{
uint8_t v___x_4789_; 
lean_inc(v___x_4787_);
v___x_4789_ = l_Lean_Syntax_matchesNull(v___x_4787_, v___x_4762_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; 
lean_dec(v___x_4787_);
lean_dec(v_tk_4677_);
lean_dec(v_stx_4631_);
v___x_4790_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4633_);
return v___x_4790_;
}
else
{
lean_object* v_mutTk_x3f_4791_; lean_object* v___x_4792_; 
v_mutTk_x3f_4791_ = l_Lean_Syntax_getArg(v___x_4787_, v___x_4676_);
lean_dec(v___x_4787_);
v___x_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4792_, 0, v_mutTk_x3f_4791_);
v_mutTk_x3f_4764_ = v___x_4792_;
v___y_4765_ = v_a_4632_;
v___y_4766_ = v_a_4633_;
goto v___jp_4763_;
}
}
else
{
lean_object* v___x_4793_; 
lean_dec(v___x_4787_);
v___x_4793_ = lean_box(0);
v_mutTk_x3f_4764_ = v___x_4793_;
v___y_4765_ = v_a_4632_;
v___y_4766_ = v_a_4633_;
goto v___jp_4763_;
}
v___jp_4678_:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v_a_4699_; lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4720_; 
lean_inc_ref(v___y_4694_);
v___x_4696_ = l_Array_append___redArg(v___y_4694_, v___y_4695_);
lean_dec_ref(v___y_4695_);
lean_inc(v___y_4686_);
lean_inc(v___y_4684_);
v___x_4697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4697_, 0, v___y_4684_);
lean_ctor_set(v___x_4697_, 1, v___y_4686_);
lean_ctor_set(v___x_4697_, 2, v___x_4696_);
v___x_4698_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v___y_4687_, v___y_4689_, v___y_4690_);
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_a_4700_ = lean_ctor_get(v___x_4698_, 1);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4702_ = v___x_4698_;
v_isShared_4703_ = v_isSharedCheck_4720_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4720_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4704_; lean_object* v___x_4706_; 
v___x_4704_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__9));
lean_inc(v___y_4684_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set_tag(v___x_4702_, 2);
lean_ctor_set(v___x_4702_, 1, v___x_4704_);
lean_ctor_set(v___x_4702_, 0, v___y_4684_);
v___x_4706_ = v___x_4702_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___y_4684_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v___x_4704_);
v___x_4706_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
lean_inc(v___y_4683_);
lean_inc(v___y_4680_);
lean_inc(v___y_4684_);
v___x_4707_ = l_Lean_Syntax_node4(v___y_4684_, v___y_4680_, v___y_4683_, v___x_4697_, v___x_4706_, v___y_4685_);
lean_inc(v___y_4691_);
v___x_4708_ = l_Lean_Syntax_node4(v___y_4684_, v___y_4691_, v___y_4692_, v___y_4681_, v___y_4682_, v___x_4707_);
v___x_4709_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4710_ = l_Lean_SourceInfo_fromRef(v_tk_4677_, v___x_4674_);
lean_dec(v_tk_4677_);
v___x_4711_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__10));
v___x_4712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4710_);
lean_ctor_set(v___x_4712_, 1, v___x_4711_);
if (lean_obj_tag(v___y_4688_) == 1)
{
lean_object* v_val_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v_val_4713_ = lean_ctor_get(v___y_4688_, 0);
lean_inc(v_val_4713_);
lean_dec_ref_known(v___y_4688_, 1);
v___x_4714_ = l_Lean_SourceInfo_fromRef(v_val_4713_, v___x_4674_);
lean_dec(v_val_4713_);
v___x_4715_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_4716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4714_);
lean_ctor_set(v___x_4716_, 1, v___x_4715_);
v___x_4717_ = l_Array_mkArray1___redArg(v___x_4716_);
v___y_4635_ = v_a_4700_;
v___y_4636_ = v___y_4679_;
v___y_4637_ = v___x_4709_;
v___y_4638_ = v___x_4708_;
v___y_4639_ = v___y_4686_;
v___y_4640_ = v_a_4699_;
v___y_4641_ = v___y_4687_;
v___y_4642_ = v___x_4712_;
v___y_4643_ = v___y_4683_;
v___y_4644_ = v___y_4693_;
v___y_4645_ = v___y_4694_;
v___y_4646_ = v___x_4717_;
goto v___jp_4634_;
}
else
{
lean_object* v___x_4718_; 
lean_dec(v___y_4688_);
v___x_4718_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4635_ = v_a_4700_;
v___y_4636_ = v___y_4679_;
v___y_4637_ = v___x_4709_;
v___y_4638_ = v___x_4708_;
v___y_4639_ = v___y_4686_;
v___y_4640_ = v_a_4699_;
v___y_4641_ = v___y_4687_;
v___y_4642_ = v___x_4712_;
v___y_4643_ = v___y_4683_;
v___y_4644_ = v___y_4693_;
v___y_4645_ = v___y_4694_;
v___y_4646_ = v___x_4718_;
goto v___jp_4634_;
}
}
}
}
v___jp_4721_:
{
lean_object* v_quotContext_4729_; lean_object* v_currMacroScope_4730_; lean_object* v_ref_4731_; lean_object* v___x_4732_; lean_object* v_a_4733_; lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4761_; 
v_quotContext_4729_ = lean_ctor_get(v___y_4727_, 1);
v_currMacroScope_4730_ = lean_ctor_get(v___y_4727_, 2);
v_ref_4731_ = lean_ctor_get(v___y_4727_, 5);
v___x_4732_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_ref_4731_, v___y_4727_, v___y_4728_);
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
v_a_4734_ = lean_ctor_get(v___x_4732_, 1);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4736_ = v___x_4732_;
v_isShared_4737_ = v_isSharedCheck_4761_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_inc(v_a_4733_);
lean_dec(v___x_4732_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4761_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4747_; 
v___x_4738_ = lean_unsigned_to_nat(3u);
v___x_4739_ = l_Lean_Syntax_getArg(v___y_4722_, v___x_4738_);
lean_dec(v___y_4722_);
v___x_4740_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
lean_inc(v_currMacroScope_4730_);
lean_inc(v_quotContext_4729_);
v___x_4741_ = l_Lean_addMacroScope(v_quotContext_4729_, v___x_4740_, v_currMacroScope_4730_);
v___x_4742_ = 0;
v___x_4743_ = l_Lean_mkIdentFrom(v___y_4725_, v___x_4741_, v___x_4742_);
v___x_4744_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_4745_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v_a_4733_);
if (v_isShared_4737_ == 0)
{
lean_ctor_set_tag(v___x_4736_, 2);
lean_ctor_set(v___x_4736_, 1, v___x_4745_);
v___x_4747_ = v___x_4736_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4733_);
lean_ctor_set(v_reuseFailAlloc_4760_, 1, v___x_4745_);
v___x_4747_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4748_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4749_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v_a_4733_, 2);
v___x_4750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4750_, 0, v_a_4733_);
lean_ctor_set(v___x_4750_, 1, v___x_4748_);
lean_ctor_set(v___x_4750_, 2, v___x_4749_);
v___x_4751_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc_ref(v___x_4750_);
v___x_4752_ = l_Lean_Syntax_node1(v_a_4733_, v___x_4751_, v___x_4750_);
if (lean_obj_tag(v_t_x3f_4726_) == 1)
{
lean_object* v_val_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v_val_4753_ = lean_ctor_get(v_t_x3f_4726_, 0);
lean_inc(v_val_4753_);
lean_dec_ref_known(v_t_x3f_4726_, 1);
v___x_4754_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4755_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v_a_4733_, 2);
v___x_4756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4756_, 0, v_a_4733_);
lean_ctor_set(v___x_4756_, 1, v___x_4755_);
v___x_4757_ = l_Lean_Syntax_node2(v_a_4733_, v___x_4754_, v___x_4756_, v_val_4753_);
v___x_4758_ = l_Array_mkArray1___redArg(v___x_4757_);
v___y_4679_ = v___x_4742_;
v___y_4680_ = v___y_4723_;
v___y_4681_ = v___x_4750_;
v___y_4682_ = v___x_4752_;
v___y_4683_ = v___x_4743_;
v___y_4684_ = v_a_4733_;
v___y_4685_ = v___x_4739_;
v___y_4686_ = v___x_4748_;
v___y_4687_ = v_ref_4731_;
v___y_4688_ = v___y_4724_;
v___y_4689_ = v___y_4727_;
v___y_4690_ = v_a_4734_;
v___y_4691_ = v___x_4744_;
v___y_4692_ = v___x_4747_;
v___y_4693_ = v___y_4725_;
v___y_4694_ = v___x_4749_;
v___y_4695_ = v___x_4758_;
goto v___jp_4678_;
}
else
{
lean_object* v___x_4759_; 
lean_dec(v_t_x3f_4726_);
v___x_4759_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4679_ = v___x_4742_;
v___y_4680_ = v___y_4723_;
v___y_4681_ = v___x_4750_;
v___y_4682_ = v___x_4752_;
v___y_4683_ = v___x_4743_;
v___y_4684_ = v_a_4733_;
v___y_4685_ = v___x_4739_;
v___y_4686_ = v___x_4748_;
v___y_4687_ = v_ref_4731_;
v___y_4688_ = v___y_4724_;
v___y_4689_ = v___y_4727_;
v___y_4690_ = v_a_4734_;
v___y_4691_ = v___x_4744_;
v___y_4692_ = v___x_4747_;
v___y_4693_ = v___y_4725_;
v___y_4694_ = v___x_4749_;
v___y_4695_ = v___x_4759_;
goto v___jp_4678_;
}
}
}
}
v___jp_4763_:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; uint8_t v___x_4770_; 
v___x_4767_ = lean_unsigned_to_nat(2u);
v___x_4768_ = l_Lean_Syntax_getArg(v_stx_4631_, v___x_4767_);
lean_dec(v_stx_4631_);
v___x_4769_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_4768_);
v___x_4770_ = l_Lean_Syntax_isOfKind(v___x_4768_, v___x_4769_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; 
lean_dec(v___x_4768_);
lean_dec(v_mutTk_x3f_4764_);
lean_dec(v_tk_4677_);
v___x_4771_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4766_);
return v___x_4771_;
}
else
{
lean_object* v___x_4772_; lean_object* v___x_4773_; uint8_t v___x_4774_; 
v___x_4772_ = l_Lean_Syntax_getArg(v___x_4768_, v___x_4676_);
v___x_4773_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4772_);
v___x_4774_ = l_Lean_Syntax_isOfKind(v___x_4772_, v___x_4773_);
if (v___x_4774_ == 0)
{
lean_object* v___x_4775_; 
lean_dec(v___x_4772_);
lean_dec(v___x_4768_);
lean_dec(v_mutTk_x3f_4764_);
lean_dec(v_tk_4677_);
v___x_4775_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4766_);
return v___x_4775_;
}
else
{
lean_object* v___x_4776_; uint8_t v___x_4777_; 
v___x_4776_ = l_Lean_Syntax_getArg(v___x_4768_, v___x_4762_);
v___x_4777_ = l_Lean_Syntax_isNone(v___x_4776_);
if (v___x_4777_ == 0)
{
uint8_t v___x_4778_; 
lean_inc(v___x_4776_);
v___x_4778_ = l_Lean_Syntax_matchesNull(v___x_4776_, v___x_4762_);
if (v___x_4778_ == 0)
{
lean_object* v___x_4779_; 
lean_dec(v___x_4776_);
lean_dec(v___x_4772_);
lean_dec(v___x_4768_);
lean_dec(v_mutTk_x3f_4764_);
lean_dec(v_tk_4677_);
v___x_4779_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4766_);
return v___x_4779_;
}
else
{
lean_object* v___x_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; 
v___x_4780_ = l_Lean_Syntax_getArg(v___x_4776_, v___x_4676_);
lean_dec(v___x_4776_);
v___x_4781_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4780_);
v___x_4782_ = l_Lean_Syntax_isOfKind(v___x_4780_, v___x_4781_);
if (v___x_4782_ == 0)
{
lean_object* v___x_4783_; 
lean_dec(v___x_4780_);
lean_dec(v___x_4772_);
lean_dec(v___x_4768_);
lean_dec(v_mutTk_x3f_4764_);
lean_dec(v_tk_4677_);
v___x_4783_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4766_);
return v___x_4783_;
}
else
{
lean_object* v_t_x3f_4784_; lean_object* v___x_4785_; 
v_t_x3f_4784_ = l_Lean_Syntax_getArg(v___x_4780_, v___x_4762_);
lean_dec(v___x_4780_);
v___x_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4785_, 0, v_t_x3f_4784_);
v___y_4722_ = v___x_4768_;
v___y_4723_ = v___x_4769_;
v___y_4724_ = v_mutTk_x3f_4764_;
v___y_4725_ = v___x_4772_;
v_t_x3f_4726_ = v___x_4785_;
v___y_4727_ = v___y_4765_;
v___y_4728_ = v___y_4766_;
goto v___jp_4721_;
}
}
}
else
{
lean_object* v___x_4786_; 
lean_dec(v___x_4776_);
v___x_4786_ = lean_box(0);
v___y_4722_ = v___x_4768_;
v___y_4723_ = v___x_4769_;
v___y_4724_ = v_mutTk_x3f_4764_;
v___y_4725_ = v___x_4772_;
v_t_x3f_4726_ = v___x_4786_;
v___y_4727_ = v___y_4765_;
v___y_4728_ = v___y_4766_;
goto v___jp_4721_;
}
}
}
}
}
v___jp_4634_:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
lean_inc_ref_n(v___y_4645_, 3);
v___x_4647_ = l_Array_append___redArg(v___y_4645_, v___y_4646_);
lean_dec_ref(v___y_4646_);
lean_inc_n(v___y_4639_, 5);
lean_inc_n(v___y_4640_, 5);
v___x_4648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4648_, 0, v___y_4640_);
lean_ctor_set(v___x_4648_, 1, v___y_4639_);
lean_ctor_set(v___x_4648_, 2, v___x_4647_);
v___x_4649_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_4650_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
v___x_4651_ = l_Lean_Syntax_node1(v___y_4640_, v___x_4650_, v___y_4644_);
v___x_4652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4652_, 0, v___y_4640_);
lean_ctor_set(v___x_4652_, 1, v___y_4639_);
lean_ctor_set(v___x_4652_, 2, v___y_4645_);
v___x_4653_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4654_, 0, v___y_4640_);
lean_ctor_set(v___x_4654_, 1, v___x_4653_);
lean_inc_ref(v___x_4652_);
v___x_4655_ = l_Lean_Syntax_node5(v___y_4640_, v___x_4649_, v___x_4651_, v___x_4652_, v___x_4652_, v___x_4654_, v___y_4643_);
lean_inc(v___y_4637_);
v___x_4656_ = l_Lean_Syntax_node3(v___y_4640_, v___y_4637_, v___y_4642_, v___x_4648_, v___x_4655_);
v___x_4657_ = l_Lean_SourceInfo_fromRef(v___y_4641_, v___y_4636_);
v___x_4658_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_4659_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
lean_inc_n(v___x_4657_, 8);
v___x_4660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4657_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
v___x_4661_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_4662_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_4663_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4657_);
lean_ctor_set(v___x_4664_, 1, v___x_4663_);
v___x_4665_ = l_Lean_Syntax_node1(v___x_4657_, v___y_4639_, v___x_4664_);
v___x_4666_ = l_Lean_Syntax_node2(v___x_4657_, v___x_4662_, v___y_4638_, v___x_4665_);
v___x_4667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4657_);
lean_ctor_set(v___x_4667_, 1, v___y_4639_);
lean_ctor_set(v___x_4667_, 2, v___y_4645_);
v___x_4668_ = l_Lean_Syntax_node2(v___x_4657_, v___x_4662_, v___x_4656_, v___x_4667_);
v___x_4669_ = l_Lean_Syntax_node2(v___x_4657_, v___y_4639_, v___x_4666_, v___x_4668_);
v___x_4670_ = l_Lean_Syntax_node1(v___x_4657_, v___x_4661_, v___x_4669_);
v___x_4671_ = l_Lean_Syntax_node2(v___x_4657_, v___x_4658_, v___x_4660_, v___x_4670_);
v___x_4672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4671_);
lean_ctor_set(v___x_4672_, 1, v___y_4635_);
return v___x_4672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___boxed(lean_object* v_stx_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l_Lean_Elab_Do_expandDoErasedArrow(v_stx_4794_, v_a_4795_, v_a_4796_);
lean_dec_ref(v_a_4795_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1(){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4805_ = l_Lean_Elab_macroAttribute;
v___x_4806_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
v___x_4807_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1));
v___x_4808_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoErasedArrow___boxed), 3, 0);
v___x_4809_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4805_, v___x_4806_, v___x_4807_, v___x_4808_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___boxed(lean_object* v_a_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1();
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4818_, lean_object* v_dec_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v___x_4828_; uint8_t v___x_4829_; 
v___x_4828_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
lean_inc(v_stx_4818_);
v___x_4829_ = l_Lean_Syntax_isOfKind(v_stx_4818_, v___x_4828_);
if (v___x_4829_ == 0)
{
lean_object* v___x_4830_; 
lean_dec_ref(v_dec_4819_);
lean_dec(v_stx_4818_);
v___x_4830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4830_;
}
else
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; uint8_t v___x_4834_; 
v___x_4831_ = lean_unsigned_to_nat(1u);
v___x_4832_ = l_Lean_Syntax_getArg(v_stx_4818_, v___x_4831_);
v___x_4833_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v___x_4832_);
v___x_4834_ = l_Lean_Syntax_isOfKind(v___x_4832_, v___x_4833_);
if (v___x_4834_ == 0)
{
lean_object* v___x_4835_; 
lean_dec(v___x_4832_);
lean_dec_ref(v_dec_4819_);
lean_dec(v_stx_4818_);
v___x_4835_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4835_;
}
else
{
lean_object* v___x_4836_; lean_object* v_decl_4837_; lean_object* v___x_4838_; uint8_t v___x_4839_; 
v___x_4836_ = lean_unsigned_to_nat(2u);
v_decl_4837_ = l_Lean_Syntax_getArg(v_stx_4818_, v___x_4836_);
v___x_4838_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4837_);
v___x_4839_ = l_Lean_Syntax_isOfKind(v_decl_4837_, v___x_4838_);
if (v___x_4839_ == 0)
{
lean_object* v___x_4840_; 
lean_dec(v_decl_4837_);
lean_dec(v___x_4832_);
lean_dec_ref(v_dec_4819_);
lean_dec(v_stx_4818_);
v___x_4840_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4840_;
}
else
{
lean_object* v___x_4841_; lean_object* v_tk_4842_; uint8_t v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4841_ = lean_unsigned_to_nat(0u);
v_tk_4842_ = l_Lean_Syntax_getArg(v_stx_4818_, v___x_4841_);
lean_dec(v_stx_4818_);
v___x_4843_ = 0;
v___x_4844_ = lean_box(0);
v___x_4845_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
lean_ctor_set_uint8(v___x_4845_, sizeof(void*)*1, v___x_4839_);
lean_ctor_set_uint8(v___x_4845_, sizeof(void*)*1 + 1, v___x_4843_);
lean_ctor_set_uint8(v___x_4845_, sizeof(void*)*1 + 2, v___x_4843_);
lean_ctor_set_uint8(v___x_4845_, sizeof(void*)*1 + 3, v___x_4843_);
lean_ctor_set_uint8(v___x_4845_, sizeof(void*)*1 + 4, v___x_4843_);
v___x_4846_ = l_Lean_Elab_Term_mkLetConfig(v___x_4832_, v___x_4845_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
lean_inc(v_a_4847_);
lean_dec_ref_known(v___x_4846_, 1);
v___x_4848_ = lean_box(1);
v___x_4849_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4847_, v___x_4848_, v_decl_4837_, v_tk_4842_, v_dec_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_);
return v___x_4849_;
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_dec(v_tk_4842_);
lean_dec(v_decl_4837_);
lean_dec_ref(v_dec_4819_);
v_a_4850_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4846_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4846_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4858_, lean_object* v_dec_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l_Lean_Elab_Do_elabDoHave(v_stx_4858_, v_dec_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_);
lean_dec(v_a_4866_);
lean_dec_ref(v_a_4865_);
lean_dec(v_a_4864_);
lean_dec_ref(v_a_4863_);
lean_dec(v_a_4862_);
lean_dec_ref(v_a_4861_);
lean_dec_ref(v_a_4860_);
return v_res_4868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4876_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4877_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
v___x_4878_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4879_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4880_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4876_, v___x_4877_, v___x_4878_, v___x_4879_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4885_, lean_object* v___x_4886_, lean_object* v___x_4887_, lean_object* v___x_4888_, lean_object* v_decls_4889_, lean_object* v_a_4890_, uint8_t v___x_4891_, lean_object* v_body_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
lean_object* v_ref_4901_; uint8_t v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v_ref_4901_ = lean_ctor_get(v___y_4898_, 2);
v___x_4902_ = 0;
v___x_4903_ = l_Lean_SourceInfo_fromRef(v_ref_4901_, v___x_4902_);
v___x_4904_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4905_ = l_Lean_Name_mkStr4(v___x_4885_, v___x_4886_, v___x_4887_, v___x_4904_);
v___x_4906_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4903_, 4);
v___x_4907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4903_);
lean_ctor_set(v___x_4907_, 1, v___x_4906_);
v___x_4908_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4909_, 0, v___x_4903_);
lean_ctor_set(v___x_4909_, 1, v___x_4908_);
v___x_4910_ = l_Lean_Syntax_node2(v___x_4903_, v___x_4888_, v___x_4907_, v___x_4909_);
v___x_4911_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4903_);
lean_ctor_set(v___x_4912_, 1, v___x_4911_);
v___x_4913_ = l_Lean_Syntax_node4(v___x_4903_, v___x_4905_, v___x_4910_, v_decls_4889_, v___x_4912_, v_body_4892_);
v___x_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4914_, 0, v_a_4890_);
v___x_4915_ = l_Lean_Elab_Term_elabTerm(v___x_4913_, v___x_4914_, v___x_4891_, v___x_4891_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4916_, lean_object* v___x_4917_, lean_object* v___x_4918_, lean_object* v___x_4919_, lean_object* v_decls_4920_, lean_object* v_a_4921_, lean_object* v___x_4922_, lean_object* v_body_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
uint8_t v___x_4496__boxed_4932_; lean_object* v_res_4933_; 
v___x_4496__boxed_4932_ = lean_unbox(v___x_4922_);
v_res_4933_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4916_, v___x_4917_, v___x_4918_, v___x_4919_, v_decls_4920_, v_a_4921_, v___x_4496__boxed_4932_, v_body_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
lean_dec(v___y_4930_);
lean_dec_ref(v___y_4929_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec_ref(v___y_4924_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4934_, lean_object* v_a_4935_){
_start:
{
if (lean_obj_tag(v_a_4934_) == 0)
{
lean_object* v___x_4936_; 
v___x_4936_ = l_List_reverse___redArg(v_a_4935_);
return v___x_4936_;
}
else
{
lean_object* v_head_4937_; lean_object* v_tail_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4947_; 
v_head_4937_ = lean_ctor_get(v_a_4934_, 0);
v_tail_4938_ = lean_ctor_get(v_a_4934_, 1);
v_isSharedCheck_4947_ = !lean_is_exclusive(v_a_4934_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4940_ = v_a_4934_;
v_isShared_4941_ = v_isSharedCheck_4947_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_tail_4938_);
lean_inc(v_head_4937_);
lean_dec(v_a_4934_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4947_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4942_; lean_object* v___x_4944_; 
v___x_4942_ = l_Lean_MessageData_ofSyntax(v_head_4937_);
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v_a_4935_);
lean_ctor_set(v___x_4940_, 0, v___x_4942_);
v___x_4944_ = v___x_4940_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v___x_4942_);
lean_ctor_set(v_reuseFailAlloc_4946_, 1, v_a_4935_);
v___x_4944_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
v_a_4934_ = v_tail_4938_;
v_a_4935_ = v___x_4944_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4964_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4965_ = l_Lean_stringToMessageData(v___x_4964_);
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4966_, lean_object* v_dec_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_){
_start:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; uint8_t v___x_4980_; 
v___x_4976_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4977_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4978_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4979_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4966_);
v___x_4980_ = l_Lean_Syntax_isOfKind(v_stx_4966_, v___x_4979_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; 
lean_dec_ref(v_dec_4967_);
lean_dec(v_stx_4966_);
v___x_4981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4981_;
}
else
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
v___x_4982_ = lean_unsigned_to_nat(0u);
v___x_4983_ = l_Lean_Syntax_getArg(v_stx_4966_, v___x_4982_);
v___x_4984_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_4983_);
v___x_4985_ = l_Lean_Syntax_isOfKind(v___x_4983_, v___x_4984_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; 
lean_dec(v___x_4983_);
lean_dec_ref(v_dec_4967_);
lean_dec(v_stx_4966_);
v___x_4986_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4986_;
}
else
{
lean_object* v___x_4987_; lean_object* v_decls_4988_; lean_object* v___x_4989_; uint8_t v___x_4990_; 
v___x_4987_ = lean_unsigned_to_nat(1u);
v_decls_4988_ = l_Lean_Syntax_getArg(v_stx_4966_, v___x_4987_);
lean_dec(v_stx_4966_);
v___x_4989_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4988_);
v___x_4990_ = l_Lean_Syntax_isOfKind(v_decls_4988_, v___x_4989_);
if (v___x_4990_ == 0)
{
lean_object* v___x_4991_; 
lean_dec(v_decls_4988_);
lean_dec(v___x_4983_);
lean_dec_ref(v_dec_4967_);
v___x_4991_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4991_;
}
else
{
lean_object* v_tk_4992_; lean_object* v___x_4993_; 
v_tk_4992_ = l_Lean_Syntax_getArg(v___x_4983_, v___x_4982_);
lean_dec(v___x_4983_);
v___x_4993_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4967_, v_tk_4992_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_);
lean_dec(v_tk_4992_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; lean_object* v___x_4995_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
lean_inc(v_a_4994_);
lean_dec_ref_known(v___x_4993_, 1);
lean_inc(v_decls_4988_);
v___x_4995_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4988_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v_doBlockResultType_4997_; lean_object* v___x_4998_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc(v_a_4996_);
lean_dec_ref_known(v___x_4995_, 1);
v_doBlockResultType_4997_ = lean_ctor_get(v_a_4968_, 3);
lean_inc_ref(v_doBlockResultType_4997_);
v___x_4998_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4997_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v_a_4999_; lean_object* v___x_5000_; lean_object* v___f_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
lean_inc(v_a_4999_);
lean_dec_ref_known(v___x_4998_, 1);
v___x_5000_ = lean_box(v___x_4990_);
v___f_5001_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_5001_, 0, v___x_4976_);
lean_closure_set(v___f_5001_, 1, v___x_4977_);
lean_closure_set(v___f_5001_, 2, v___x_4978_);
lean_closure_set(v___f_5001_, 3, v___x_4984_);
lean_closure_set(v___f_5001_, 4, v_decls_4988_);
lean_closure_set(v___f_5001_, 5, v_a_4999_);
lean_closure_set(v___f_5001_, 6, v___x_5000_);
v___x_5002_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_5003_ = lean_array_to_list(v_a_4996_);
v___x_5004_ = lean_box(0);
v___x_5005_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_5003_, v___x_5004_);
v___x_5006_ = l_Lean_MessageData_ofList(v___x_5005_);
v___x_5007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5002_);
lean_ctor_set(v___x_5007_, 1, v___x_5006_);
v___x_5008_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_5008_, 0, v_a_4994_);
v___x_5009_ = lean_box(0);
v___x_5010_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_5007_, v___x_5008_, v___f_5001_, v___x_5009_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_);
return v___x_5010_;
}
else
{
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_decls_4988_);
return v___x_4998_;
}
}
else
{
lean_object* v_a_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5018_; 
lean_dec(v_a_4994_);
lean_dec(v_decls_4988_);
v_a_5011_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5018_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_5013_ = v___x_4995_;
v_isShared_5014_ = v_isSharedCheck_5018_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_a_5011_);
lean_dec(v___x_4995_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5018_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
lean_object* v___x_5016_; 
if (v_isShared_5014_ == 0)
{
v___x_5016_ = v___x_5013_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_a_5011_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
}
}
else
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
lean_dec(v_decls_4988_);
v_a_5019_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_4993_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_4993_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_5027_, lean_object* v_dec_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_5027_, v_dec_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_);
lean_dec(v_a_5035_);
lean_dec_ref(v_a_5034_);
lean_dec(v_a_5033_);
lean_dec_ref(v_a_5032_);
lean_dec(v_a_5031_);
lean_dec_ref(v_a_5030_);
lean_dec_ref(v_a_5029_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5045_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5046_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_5047_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_5048_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_5049_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5045_, v___x_5046_, v___x_5047_, v___x_5048_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_5051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_5058_, lean_object* v_dec_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_){
_start:
{
lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; uint8_t v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___x_5101_; uint8_t v___x_5102_; 
v___x_5101_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
lean_inc(v_stx_5058_);
v___x_5102_ = l_Lean_Syntax_isOfKind(v_stx_5058_, v___x_5101_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; 
lean_dec_ref(v_dec_5059_);
lean_dec(v_stx_5058_);
v___x_5103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5103_;
}
else
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; uint8_t v___x_5107_; 
v___x_5104_ = lean_unsigned_to_nat(0u);
v___x_5105_ = l_Lean_Syntax_getArg(v_stx_5058_, v___x_5104_);
lean_dec(v_stx_5058_);
v___x_5106_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_5105_);
v___x_5107_ = l_Lean_Syntax_isOfKind(v___x_5105_, v___x_5106_);
if (v___x_5107_ == 0)
{
lean_object* v___x_5108_; uint8_t v___x_5109_; 
v___x_5108_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5105_);
v___x_5109_ = l_Lean_Syntax_isOfKind(v___x_5105_, v___x_5108_);
if (v___x_5109_ == 0)
{
lean_object* v___x_5110_; 
lean_dec(v___x_5105_);
lean_dec_ref(v_dec_5059_);
v___x_5110_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5110_;
}
else
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v_decl_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5111_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5112_ = lean_unsigned_to_nat(1u);
v___x_5113_ = lean_mk_empty_array_with_capacity(v___x_5112_);
v___x_5114_ = lean_array_push(v___x_5113_, v___x_5105_);
v___x_5115_ = lean_box(2);
v_decl_5116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5116_, 0, v___x_5115_);
lean_ctor_set(v_decl_5116_, 1, v___x_5111_);
lean_ctor_set(v_decl_5116_, 2, v___x_5114_);
v___x_5117_ = lean_box(0);
v___x_5118_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5118_, 0, v___x_5117_);
lean_ctor_set_uint8(v___x_5118_, sizeof(void*)*1, v___x_5107_);
lean_ctor_set_uint8(v___x_5118_, sizeof(void*)*1 + 1, v___x_5107_);
lean_ctor_set_uint8(v___x_5118_, sizeof(void*)*1 + 2, v___x_5107_);
lean_ctor_set_uint8(v___x_5118_, sizeof(void*)*1 + 3, v___x_5107_);
lean_ctor_set_uint8(v___x_5118_, sizeof(void*)*1 + 4, v___x_5107_);
v___x_5119_ = lean_box(2);
lean_inc_ref(v_decl_5116_);
v___x_5120_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5118_, v___x_5119_, v_decl_5116_, v_decl_5116_, v_dec_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_);
return v___x_5120_;
}
}
else
{
lean_object* v___x_5121_; lean_object* v___x_5122_; uint8_t v___x_5123_; 
v___x_5121_ = l_Lean_Syntax_getArg(v___x_5105_, v___x_5104_);
v___x_5122_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5121_);
v___x_5123_ = l_Lean_Syntax_isOfKind(v___x_5121_, v___x_5122_);
if (v___x_5123_ == 0)
{
lean_object* v___x_5124_; 
lean_dec(v___x_5121_);
lean_dec(v___x_5105_);
lean_dec_ref(v_dec_5059_);
v___x_5124_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5124_;
}
else
{
lean_object* v___x_5125_; lean_object* v_xType_x3f_5127_; lean_object* v___y_5128_; lean_object* v___y_5129_; lean_object* v___y_5130_; lean_object* v___y_5131_; lean_object* v___y_5132_; lean_object* v___y_5133_; lean_object* v___y_5134_; lean_object* v___x_5154_; uint8_t v___x_5155_; 
v___x_5125_ = l_Lean_Syntax_getArg(v___x_5121_, v___x_5104_);
lean_dec(v___x_5121_);
v___x_5154_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5125_);
v___x_5155_ = l_Lean_Syntax_isOfKind(v___x_5125_, v___x_5154_);
if (v___x_5155_ == 0)
{
lean_object* v___x_5156_; 
lean_dec(v___x_5125_);
lean_dec(v___x_5105_);
lean_dec_ref(v_dec_5059_);
v___x_5156_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5156_;
}
else
{
lean_object* v___x_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; 
v___x_5157_ = lean_unsigned_to_nat(1u);
v___x_5158_ = l_Lean_Syntax_getArg(v___x_5105_, v___x_5157_);
v___x_5159_ = l_Lean_Syntax_matchesNull(v___x_5158_, v___x_5104_);
if (v___x_5159_ == 0)
{
lean_object* v___x_5160_; 
lean_dec(v___x_5125_);
lean_dec(v___x_5105_);
lean_dec_ref(v_dec_5059_);
v___x_5160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5160_;
}
else
{
lean_object* v___x_5161_; lean_object* v___x_5162_; uint8_t v___x_5163_; 
v___x_5161_ = lean_unsigned_to_nat(2u);
v___x_5162_ = l_Lean_Syntax_getArg(v___x_5105_, v___x_5161_);
v___x_5163_ = l_Lean_Syntax_isNone(v___x_5162_);
if (v___x_5163_ == 0)
{
uint8_t v___x_5164_; 
lean_inc(v___x_5162_);
v___x_5164_ = l_Lean_Syntax_matchesNull(v___x_5162_, v___x_5157_);
if (v___x_5164_ == 0)
{
lean_object* v___x_5165_; 
lean_dec(v___x_5162_);
lean_dec(v___x_5125_);
lean_dec(v___x_5105_);
lean_dec_ref(v_dec_5059_);
v___x_5165_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5165_;
}
else
{
lean_object* v___x_5166_; lean_object* v___x_5167_; uint8_t v___x_5168_; 
v___x_5166_ = l_Lean_Syntax_getArg(v___x_5162_, v___x_5104_);
lean_dec(v___x_5162_);
v___x_5167_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5166_);
v___x_5168_ = l_Lean_Syntax_isOfKind(v___x_5166_, v___x_5167_);
if (v___x_5168_ == 0)
{
lean_object* v___x_5169_; 
lean_dec(v___x_5166_);
lean_dec(v___x_5125_);
lean_dec(v___x_5105_);
lean_dec_ref(v_dec_5059_);
v___x_5169_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5169_;
}
else
{
lean_object* v_xType_x3f_5170_; lean_object* v___x_5171_; 
v_xType_x3f_5170_ = l_Lean_Syntax_getArg(v___x_5166_, v___x_5157_);
lean_dec(v___x_5166_);
v___x_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5171_, 0, v_xType_x3f_5170_);
v_xType_x3f_5127_ = v___x_5171_;
v___y_5128_ = v_a_5060_;
v___y_5129_ = v_a_5061_;
v___y_5130_ = v_a_5062_;
v___y_5131_ = v_a_5063_;
v___y_5132_ = v_a_5064_;
v___y_5133_ = v_a_5065_;
v___y_5134_ = v_a_5066_;
goto v___jp_5126_;
}
}
}
else
{
lean_object* v___x_5172_; 
lean_dec(v___x_5162_);
v___x_5172_ = lean_box(0);
v_xType_x3f_5127_ = v___x_5172_;
v___y_5128_ = v_a_5060_;
v___y_5129_ = v_a_5061_;
v___y_5130_ = v_a_5062_;
v___y_5131_ = v_a_5063_;
v___y_5132_ = v_a_5064_;
v___y_5133_ = v_a_5065_;
v___y_5134_ = v_a_5066_;
goto v___jp_5126_;
}
}
}
v___jp_5126_:
{
lean_object* v_ref_5135_; lean_object* v___x_5136_; lean_object* v_tk_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; uint8_t v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; 
v_ref_5135_ = lean_ctor_get(v___y_5133_, 2);
v___x_5136_ = lean_unsigned_to_nat(3u);
v_tk_5137_ = l_Lean_Syntax_getArg(v___x_5105_, v___x_5136_);
v___x_5138_ = lean_unsigned_to_nat(4u);
v___x_5139_ = l_Lean_Syntax_getArg(v___x_5105_, v___x_5138_);
lean_dec(v___x_5105_);
v___x_5140_ = 0;
v___x_5141_ = l_Lean_SourceInfo_fromRef(v_ref_5135_, v___x_5140_);
v___x_5142_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5141_, 2);
v___x_5143_ = l_Lean_Syntax_node1(v___x_5141_, v___x_5122_, v___x_5125_);
v___x_5144_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5145_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5146_, 0, v___x_5141_);
lean_ctor_set(v___x_5146_, 1, v___x_5144_);
lean_ctor_set(v___x_5146_, 2, v___x_5145_);
if (lean_obj_tag(v_xType_x3f_5127_) == 1)
{
lean_object* v_val_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v_val_5147_ = lean_ctor_get(v_xType_x3f_5127_, 0);
lean_inc(v_val_5147_);
lean_dec_ref_known(v_xType_x3f_5127_, 1);
v___x_5148_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5149_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5141_, 2);
v___x_5150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5150_, 0, v___x_5141_);
lean_ctor_set(v___x_5150_, 1, v___x_5149_);
v___x_5151_ = l_Lean_Syntax_node2(v___x_5141_, v___x_5148_, v___x_5150_, v_val_5147_);
v___x_5152_ = l_Array_mkArray1___redArg(v___x_5151_);
v___y_5069_ = v___x_5142_;
v___y_5070_ = v_tk_5137_;
v___y_5071_ = v___x_5143_;
v___y_5072_ = v___x_5144_;
v___y_5073_ = v___x_5141_;
v___y_5074_ = v___y_5134_;
v___y_5075_ = v___x_5146_;
v___y_5076_ = v___x_5139_;
v___y_5077_ = v___y_5131_;
v___y_5078_ = v___x_5140_;
v___y_5079_ = v___y_5129_;
v___y_5080_ = v___y_5132_;
v___y_5081_ = v___y_5130_;
v___y_5082_ = v___y_5128_;
v___y_5083_ = v___y_5133_;
v___y_5084_ = v___x_5145_;
v___y_5085_ = v___x_5152_;
goto v___jp_5068_;
}
else
{
lean_object* v___x_5153_; 
lean_dec(v_xType_x3f_5127_);
v___x_5153_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_5069_ = v___x_5142_;
v___y_5070_ = v_tk_5137_;
v___y_5071_ = v___x_5143_;
v___y_5072_ = v___x_5144_;
v___y_5073_ = v___x_5141_;
v___y_5074_ = v___y_5134_;
v___y_5075_ = v___x_5146_;
v___y_5076_ = v___x_5139_;
v___y_5077_ = v___y_5131_;
v___y_5078_ = v___x_5140_;
v___y_5079_ = v___y_5129_;
v___y_5080_ = v___y_5132_;
v___y_5081_ = v___y_5130_;
v___y_5082_ = v___y_5128_;
v___y_5083_ = v___y_5133_;
v___y_5084_ = v___x_5145_;
v___y_5085_ = v___x_5153_;
goto v___jp_5068_;
}
}
}
}
}
v___jp_5068_:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
lean_inc_ref(v___y_5084_);
v___x_5086_ = l_Array_append___redArg(v___y_5084_, v___y_5085_);
lean_dec_ref(v___y_5085_);
lean_inc(v___y_5072_);
lean_inc_n(v___y_5073_, 2);
v___x_5087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5087_, 0, v___y_5073_);
lean_ctor_set(v___x_5087_, 1, v___y_5072_);
lean_ctor_set(v___x_5087_, 2, v___x_5086_);
v___x_5088_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5089_, 0, v___y_5073_);
lean_ctor_set(v___x_5089_, 1, v___x_5088_);
lean_inc(v___y_5069_);
v___x_5090_ = l_Lean_Syntax_node5(v___y_5073_, v___y_5069_, v___y_5071_, v___y_5075_, v___x_5087_, v___x_5089_, v___y_5076_);
v___x_5091_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5092_ = lean_unsigned_to_nat(1u);
v___x_5093_ = lean_mk_empty_array_with_capacity(v___x_5092_);
v___x_5094_ = lean_array_push(v___x_5093_, v___x_5090_);
v___x_5095_ = lean_box(2);
v___x_5096_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5096_, 0, v___x_5095_);
lean_ctor_set(v___x_5096_, 1, v___x_5091_);
lean_ctor_set(v___x_5096_, 2, v___x_5094_);
v___x_5097_ = lean_box(0);
v___x_5098_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5098_, 0, v___x_5097_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1, v___y_5078_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 1, v___y_5078_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 2, v___y_5078_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 3, v___y_5078_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 4, v___y_5078_);
v___x_5099_ = lean_box(2);
v___x_5100_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5098_, v___x_5099_, v___x_5096_, v___y_5070_, v_dec_5059_, v___y_5082_, v___y_5079_, v___y_5081_, v___y_5077_, v___y_5080_, v___y_5083_, v___y_5074_);
return v___x_5100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5173_, lean_object* v_dec_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_){
_start:
{
lean_object* v_res_5183_; 
v_res_5183_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5173_, v_dec_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_);
lean_dec(v_a_5181_);
lean_dec_ref(v_a_5180_);
lean_dec(v_a_5179_);
lean_dec_ref(v_a_5178_);
lean_dec(v_a_5177_);
lean_dec_ref(v_a_5176_);
lean_dec_ref(v_a_5175_);
return v_res_5183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v___x_5191_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5192_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_5193_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5194_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5195_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5191_, v___x_5192_, v___x_5193_, v___x_5194_);
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
uint8_t v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; 
v___x_5207_ = 0;
v___x_5208_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5198_, v___x_5207_);
v___x_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5209_, 0, v___x_5208_);
return v___x_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v_____do__lift_5210_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5220_, size_t v_sz_5221_, size_t v_i_5222_, lean_object* v_b_5223_, lean_object* v___y_5224_){
_start:
{
uint8_t v___x_5226_; 
v___x_5226_ = lean_usize_dec_lt(v_i_5222_, v_sz_5221_);
if (v___x_5226_ == 0)
{
lean_object* v___x_5227_; 
v___x_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5227_, 0, v_b_5223_);
return v___x_5227_;
}
else
{
lean_object* v_ref_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v_a_5231_; uint8_t v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; size_t v___x_5265_; size_t v___x_5266_; 
v_ref_5228_ = lean_ctor_get(v___y_5224_, 2);
v___x_5229_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5230_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5231_ = lean_array_uget_borrowed(v_as_5220_, v_i_5222_);
v___x_5232_ = 0;
v___x_5233_ = l_Lean_SourceInfo_fromRef(v_ref_5228_, v___x_5232_);
v___x_5234_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5235_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5236_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5237_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5233_, 17);
v___x_5238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5233_);
lean_ctor_set(v___x_5238_, 1, v___x_5237_);
v___x_5239_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5233_);
lean_ctor_set(v___x_5240_, 1, v___x_5239_);
v___x_5241_ = l_Lean_Syntax_node1(v___x_5233_, v___x_5234_, v___x_5240_);
v___x_5242_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5233_);
lean_ctor_set(v___x_5243_, 1, v___x_5234_);
lean_ctor_set(v___x_5243_, 2, v___x_5242_);
lean_inc_ref_n(v___x_5243_, 3);
v___x_5244_ = l_Lean_Syntax_node1(v___x_5233_, v___x_5229_, v___x_5243_);
v___x_5245_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5246_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5247_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5231_, 2);
v___x_5248_ = l_Lean_Syntax_node1(v___x_5233_, v___x_5247_, v_a_5231_);
v___x_5249_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5233_);
lean_ctor_set(v___x_5250_, 1, v___x_5249_);
v___x_5251_ = l_Lean_Syntax_node5(v___x_5233_, v___x_5246_, v___x_5248_, v___x_5243_, v___x_5243_, v___x_5250_, v_a_5231_);
v___x_5252_ = l_Lean_Syntax_node1(v___x_5233_, v___x_5245_, v___x_5251_);
v___x_5253_ = l_Lean_Syntax_node4(v___x_5233_, v___x_5236_, v___x_5238_, v___x_5241_, v___x_5244_, v___x_5252_);
v___x_5254_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5255_, 0, v___x_5233_);
lean_ctor_set(v___x_5255_, 1, v___x_5254_);
v___x_5256_ = l_Lean_Syntax_node1(v___x_5233_, v___x_5234_, v___x_5255_);
v___x_5257_ = l_Lean_Syntax_node2(v___x_5233_, v___x_5235_, v___x_5253_, v___x_5256_);
v___x_5258_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5259_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5233_);
lean_ctor_set(v___x_5260_, 1, v___x_5259_);
v___x_5261_ = l_Lean_Syntax_node2(v___x_5233_, v___x_5258_, v___x_5260_, v_b_5223_);
v___x_5262_ = l_Lean_Syntax_node2(v___x_5233_, v___x_5235_, v___x_5261_, v___x_5243_);
v___x_5263_ = l_Lean_Syntax_node2(v___x_5233_, v___x_5234_, v___x_5257_, v___x_5262_);
v___x_5264_ = l_Lean_Syntax_node1(v___x_5233_, v___x_5230_, v___x_5263_);
v___x_5265_ = ((size_t)1ULL);
v___x_5266_ = lean_usize_add(v_i_5222_, v___x_5265_);
v_i_5222_ = v___x_5266_;
v_b_5223_ = v___x_5264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5268_, lean_object* v_sz_5269_, lean_object* v_i_5270_, lean_object* v_b_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
size_t v_sz_boxed_5274_; size_t v_i_boxed_5275_; lean_object* v_res_5276_; 
v_sz_boxed_5274_ = lean_unbox_usize(v_sz_5269_);
lean_dec(v_sz_5269_);
v_i_boxed_5275_ = lean_unbox_usize(v_i_5270_);
lean_dec(v_i_5270_);
v_res_5276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5268_, v_sz_boxed_5274_, v_i_boxed_5275_, v_b_5271_, v___y_5272_);
lean_dec_ref(v___y_5272_);
lean_dec_ref(v_as_5268_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5277_, size_t v_sz_5278_, size_t v_i_5279_, lean_object* v_b_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_){
_start:
{
uint8_t v___x_5289_; 
v___x_5289_ = lean_usize_dec_lt(v_i_5279_, v_sz_5278_);
if (v___x_5289_ == 0)
{
lean_object* v___x_5290_; 
v___x_5290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5290_, 0, v_b_5280_);
return v___x_5290_;
}
else
{
lean_object* v_ref_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v_a_5294_; uint8_t v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; size_t v___x_5328_; size_t v___x_5329_; lean_object* v___x_5330_; 
v_ref_5291_ = lean_ctor_get(v___y_5286_, 2);
v___x_5292_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5293_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5294_ = lean_array_uget_borrowed(v_as_5277_, v_i_5279_);
v___x_5295_ = 0;
v___x_5296_ = l_Lean_SourceInfo_fromRef(v_ref_5291_, v___x_5295_);
v___x_5297_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5298_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5299_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5300_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5296_, 17);
v___x_5301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5301_, 0, v___x_5296_);
lean_ctor_set(v___x_5301_, 1, v___x_5300_);
v___x_5302_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5303_, 0, v___x_5296_);
lean_ctor_set(v___x_5303_, 1, v___x_5302_);
v___x_5304_ = l_Lean_Syntax_node1(v___x_5296_, v___x_5297_, v___x_5303_);
v___x_5305_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5296_);
lean_ctor_set(v___x_5306_, 1, v___x_5297_);
lean_ctor_set(v___x_5306_, 2, v___x_5305_);
lean_inc_ref_n(v___x_5306_, 3);
v___x_5307_ = l_Lean_Syntax_node1(v___x_5296_, v___x_5292_, v___x_5306_);
v___x_5308_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5309_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5310_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5294_, 2);
v___x_5311_ = l_Lean_Syntax_node1(v___x_5296_, v___x_5310_, v_a_5294_);
v___x_5312_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5313_, 0, v___x_5296_);
lean_ctor_set(v___x_5313_, 1, v___x_5312_);
v___x_5314_ = l_Lean_Syntax_node5(v___x_5296_, v___x_5309_, v___x_5311_, v___x_5306_, v___x_5306_, v___x_5313_, v_a_5294_);
v___x_5315_ = l_Lean_Syntax_node1(v___x_5296_, v___x_5308_, v___x_5314_);
v___x_5316_ = l_Lean_Syntax_node4(v___x_5296_, v___x_5299_, v___x_5301_, v___x_5304_, v___x_5307_, v___x_5315_);
v___x_5317_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5296_);
lean_ctor_set(v___x_5318_, 1, v___x_5317_);
v___x_5319_ = l_Lean_Syntax_node1(v___x_5296_, v___x_5297_, v___x_5318_);
v___x_5320_ = l_Lean_Syntax_node2(v___x_5296_, v___x_5298_, v___x_5316_, v___x_5319_);
v___x_5321_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5322_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5323_, 0, v___x_5296_);
lean_ctor_set(v___x_5323_, 1, v___x_5322_);
v___x_5324_ = l_Lean_Syntax_node2(v___x_5296_, v___x_5321_, v___x_5323_, v_b_5280_);
v___x_5325_ = l_Lean_Syntax_node2(v___x_5296_, v___x_5298_, v___x_5324_, v___x_5306_);
v___x_5326_ = l_Lean_Syntax_node2(v___x_5296_, v___x_5297_, v___x_5320_, v___x_5325_);
v___x_5327_ = l_Lean_Syntax_node1(v___x_5296_, v___x_5293_, v___x_5326_);
v___x_5328_ = ((size_t)1ULL);
v___x_5329_ = lean_usize_add(v_i_5279_, v___x_5328_);
v___x_5330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5277_, v_sz_5278_, v___x_5329_, v___x_5327_, v___y_5286_);
return v___x_5330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5331_, lean_object* v_sz_5332_, lean_object* v_i_5333_, lean_object* v_b_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_){
_start:
{
size_t v_sz_boxed_5343_; size_t v_i_boxed_5344_; lean_object* v_res_5345_; 
v_sz_boxed_5343_ = lean_unbox_usize(v_sz_5332_);
lean_dec(v_sz_5332_);
v_i_boxed_5344_ = lean_unbox_usize(v_i_5333_);
lean_dec(v_i_5333_);
v_res_5345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5331_, v_sz_boxed_5343_, v_i_boxed_5344_, v_b_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec_ref(v___y_5335_);
lean_dec_ref(v_as_5331_);
return v_res_5345_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5385_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5386_ = l_String_toRawSubstring_x27(v___x_5385_);
return v___x_5386_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5400_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5401_ = l_String_toRawSubstring_x27(v___x_5400_);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5418_, lean_object* v_dec_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_){
_start:
{
lean_object* v___x_5428_; uint8_t v___x_5429_; 
v___x_5428_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
lean_inc(v_stx_5418_);
v___x_5429_ = l_Lean_Syntax_isOfKind(v_stx_5418_, v___x_5428_);
if (v___x_5429_ == 0)
{
lean_object* v___x_5430_; 
lean_dec_ref(v_dec_5419_);
lean_dec(v_stx_5418_);
v___x_5430_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5430_;
}
else
{
lean_object* v___y_5432_; lean_object* v___y_5433_; lean_object* v___y_5434_; uint8_t v___y_5435_; lean_object* v___y_5436_; lean_object* v_body_5437_; lean_object* v___y_5438_; lean_object* v___y_5439_; lean_object* v___y_5440_; lean_object* v___y_5441_; lean_object* v___y_5442_; lean_object* v___y_5443_; lean_object* v___y_5444_; lean_object* v___y_5518_; lean_object* v___y_5519_; lean_object* v___y_5520_; lean_object* v___y_5521_; uint8_t v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v___y_5529_; lean_object* v___y_5530_; lean_object* v___y_5531_; lean_object* v_a_5532_; lean_object* v___y_5546_; lean_object* v___y_5547_; lean_object* v___y_5548_; lean_object* v___y_5549_; lean_object* v___y_5550_; lean_object* v___y_5551_; lean_object* v___y_5552_; lean_object* v___y_5553_; lean_object* v___y_5554_; lean_object* v___y_5555_; lean_object* v___y_5556_; lean_object* v___y_5557_; lean_object* v___y_5558_; lean_object* v_mutTk_x3f_5631_; lean_object* v___y_5632_; lean_object* v___y_5633_; lean_object* v___y_5634_; lean_object* v___y_5635_; lean_object* v___y_5636_; lean_object* v___y_5637_; lean_object* v___y_5638_; lean_object* v___x_5662_; lean_object* v___x_5663_; uint8_t v___x_5664_; 
v___x_5662_ = lean_unsigned_to_nat(1u);
v___x_5663_ = l_Lean_Syntax_getArg(v_stx_5418_, v___x_5662_);
v___x_5664_ = l_Lean_Syntax_isNone(v___x_5663_);
if (v___x_5664_ == 0)
{
uint8_t v___x_5665_; 
lean_inc(v___x_5663_);
v___x_5665_ = l_Lean_Syntax_matchesNull(v___x_5663_, v___x_5662_);
if (v___x_5665_ == 0)
{
lean_object* v___x_5666_; 
lean_dec(v___x_5663_);
lean_dec_ref(v_dec_5419_);
lean_dec(v_stx_5418_);
v___x_5666_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5666_;
}
else
{
lean_object* v___x_5667_; lean_object* v_mutTk_x3f_5668_; lean_object* v___x_5669_; 
v___x_5667_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5668_ = l_Lean_Syntax_getArg(v___x_5663_, v___x_5667_);
lean_dec(v___x_5663_);
v___x_5669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5669_, 0, v_mutTk_x3f_5668_);
v_mutTk_x3f_5631_ = v___x_5669_;
v___y_5632_ = v_a_5420_;
v___y_5633_ = v_a_5421_;
v___y_5634_ = v_a_5422_;
v___y_5635_ = v_a_5423_;
v___y_5636_ = v_a_5424_;
v___y_5637_ = v_a_5425_;
v___y_5638_ = v_a_5426_;
goto v___jp_5630_;
}
}
else
{
lean_object* v___x_5670_; 
lean_dec(v___x_5663_);
v___x_5670_ = lean_box(0);
v_mutTk_x3f_5631_ = v___x_5670_;
v___y_5632_ = v_a_5420_;
v___y_5633_ = v_a_5421_;
v___y_5634_ = v_a_5422_;
v___y_5635_ = v_a_5423_;
v___y_5636_ = v_a_5424_;
v___y_5637_ = v_a_5425_;
v___y_5638_ = v_a_5426_;
goto v___jp_5630_;
}
v___jp_5431_:
{
lean_object* v_eq_x3f_5445_; 
v_eq_x3f_5445_ = lean_ctor_get(v___y_5433_, 0);
lean_inc(v_eq_x3f_5445_);
lean_dec_ref(v___y_5433_);
if (lean_obj_tag(v_eq_x3f_5445_) == 1)
{
lean_object* v_val_5446_; lean_object* v_ref_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; 
v_val_5446_ = lean_ctor_get(v_eq_x3f_5445_, 0);
lean_inc(v_val_5446_);
lean_dec_ref_known(v_eq_x3f_5445_, 1);
v_ref_5447_ = lean_ctor_get(v___y_5443_, 2);
v___x_5448_ = l_Lean_SourceInfo_fromRef(v_ref_5447_, v___y_5435_);
v___x_5449_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5450_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
lean_inc_n(v___x_5448_, 19);
v___x_5451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5451_, 0, v___x_5448_);
lean_ctor_set(v___x_5451_, 1, v___x_5450_);
v___x_5452_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5453_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5454_, 0, v___x_5448_);
lean_ctor_set(v___x_5454_, 1, v___x_5452_);
lean_ctor_set(v___x_5454_, 2, v___x_5453_);
v___x_5455_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5456_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5448_);
lean_ctor_set(v___x_5457_, 1, v___x_5456_);
v___x_5458_ = l_Lean_Syntax_node2(v___x_5448_, v___x_5452_, v_val_5446_, v___x_5457_);
v___x_5459_ = l_Lean_Syntax_node2(v___x_5448_, v___x_5455_, v___x_5458_, v___y_5432_);
v___x_5460_ = l_Lean_Syntax_node1(v___x_5448_, v___x_5452_, v___x_5459_);
v___x_5461_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5462_, 0, v___x_5448_);
lean_ctor_set(v___x_5462_, 1, v___x_5461_);
v___x_5463_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5464_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5465_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5466_, 0, v___x_5448_);
lean_ctor_set(v___x_5466_, 1, v___x_5465_);
v___x_5467_ = l_Lean_Syntax_node1(v___x_5448_, v___x_5452_, v___y_5434_);
v___x_5468_ = l_Lean_Syntax_node1(v___x_5448_, v___x_5452_, v___x_5467_);
v___x_5469_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5470_, 0, v___x_5448_);
lean_ctor_set(v___x_5470_, 1, v___x_5469_);
lean_inc_ref(v___x_5470_);
lean_inc_ref(v___x_5466_);
v___x_5471_ = l_Lean_Syntax_node4(v___x_5448_, v___x_5464_, v___x_5466_, v___x_5468_, v___x_5470_, v_body_5437_);
v___x_5472_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5473_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5448_);
lean_ctor_set(v___x_5474_, 1, v___x_5473_);
v___x_5475_ = l_Lean_Syntax_node1(v___x_5448_, v___x_5472_, v___x_5474_);
v___x_5476_ = l_Lean_Syntax_node1(v___x_5448_, v___x_5452_, v___x_5475_);
v___x_5477_ = l_Lean_Syntax_node1(v___x_5448_, v___x_5452_, v___x_5476_);
v___x_5478_ = l_Lean_Syntax_node4(v___x_5448_, v___x_5464_, v___x_5466_, v___x_5477_, v___x_5470_, v___y_5436_);
v___x_5479_ = l_Lean_Syntax_node2(v___x_5448_, v___x_5452_, v___x_5471_, v___x_5478_);
v___x_5480_ = l_Lean_Syntax_node1(v___x_5448_, v___x_5463_, v___x_5479_);
lean_inc_ref_n(v___x_5454_, 2);
v___x_5481_ = l_Lean_Syntax_node7(v___x_5448_, v___x_5449_, v___x_5451_, v___x_5454_, v___x_5454_, v___x_5454_, v___x_5460_, v___x_5462_, v___x_5480_);
v___x_5482_ = l_Lean_Elab_Do_elabDoElem(v___x_5481_, v_dec_5419_, v___x_5429_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_);
return v___x_5482_;
}
else
{
lean_object* v_ref_5483_; lean_object* v___x_5484_; lean_object* v_a_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; 
lean_dec(v_eq_x3f_5445_);
v_ref_5483_ = lean_ctor_get(v___y_5443_, 2);
v___x_5484_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5483_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_);
v_a_5485_ = lean_ctor_get(v___x_5484_, 0);
lean_inc_n(v_a_5485_, 18);
lean_dec_ref(v___x_5484_);
v___x_5486_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5487_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_5488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5488_, 0, v_a_5485_);
lean_ctor_set(v___x_5488_, 1, v___x_5487_);
v___x_5489_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5490_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5491_, 0, v_a_5485_);
lean_ctor_set(v___x_5491_, 1, v___x_5489_);
lean_ctor_set(v___x_5491_, 2, v___x_5490_);
v___x_5492_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
lean_inc_ref_n(v___x_5491_, 3);
v___x_5493_ = l_Lean_Syntax_node2(v_a_5485_, v___x_5492_, v___x_5491_, v___y_5432_);
v___x_5494_ = l_Lean_Syntax_node1(v_a_5485_, v___x_5489_, v___x_5493_);
v___x_5495_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5496_, 0, v_a_5485_);
lean_ctor_set(v___x_5496_, 1, v___x_5495_);
v___x_5497_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5498_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5499_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5500_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5500_, 0, v_a_5485_);
lean_ctor_set(v___x_5500_, 1, v___x_5499_);
v___x_5501_ = l_Lean_Syntax_node1(v_a_5485_, v___x_5489_, v___y_5434_);
v___x_5502_ = l_Lean_Syntax_node1(v_a_5485_, v___x_5489_, v___x_5501_);
v___x_5503_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5504_, 0, v_a_5485_);
lean_ctor_set(v___x_5504_, 1, v___x_5503_);
lean_inc_ref(v___x_5504_);
lean_inc_ref(v___x_5500_);
v___x_5505_ = l_Lean_Syntax_node4(v_a_5485_, v___x_5498_, v___x_5500_, v___x_5502_, v___x_5504_, v_body_5437_);
v___x_5506_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5507_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5508_, 0, v_a_5485_);
lean_ctor_set(v___x_5508_, 1, v___x_5507_);
v___x_5509_ = l_Lean_Syntax_node1(v_a_5485_, v___x_5506_, v___x_5508_);
v___x_5510_ = l_Lean_Syntax_node1(v_a_5485_, v___x_5489_, v___x_5509_);
v___x_5511_ = l_Lean_Syntax_node1(v_a_5485_, v___x_5489_, v___x_5510_);
v___x_5512_ = l_Lean_Syntax_node4(v_a_5485_, v___x_5498_, v___x_5500_, v___x_5511_, v___x_5504_, v___y_5436_);
v___x_5513_ = l_Lean_Syntax_node2(v_a_5485_, v___x_5489_, v___x_5505_, v___x_5512_);
v___x_5514_ = l_Lean_Syntax_node1(v_a_5485_, v___x_5497_, v___x_5513_);
v___x_5515_ = l_Lean_Syntax_node7(v_a_5485_, v___x_5486_, v___x_5488_, v___x_5491_, v___x_5491_, v___x_5491_, v___x_5494_, v___x_5496_, v___x_5514_);
v___x_5516_ = l_Lean_Elab_Do_elabDoElem(v___x_5515_, v_dec_5419_, v___x_5429_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_);
return v___x_5516_;
}
}
v___jp_5517_:
{
if (lean_obj_tag(v___y_5518_) == 0)
{
lean_dec_ref(v___y_5531_);
v___y_5432_ = v___y_5519_;
v___y_5433_ = v___y_5524_;
v___y_5434_ = v___y_5521_;
v___y_5435_ = v___y_5522_;
v___y_5436_ = v___y_5528_;
v_body_5437_ = v_a_5532_;
v___y_5438_ = v___y_5523_;
v___y_5439_ = v___y_5529_;
v___y_5440_ = v___y_5525_;
v___y_5441_ = v___y_5530_;
v___y_5442_ = v___y_5526_;
v___y_5443_ = v___y_5520_;
v___y_5444_ = v___y_5527_;
goto v___jp_5431_;
}
else
{
size_t v_sz_5533_; size_t v___x_5534_; lean_object* v___x_5535_; 
lean_dec_ref_known(v___y_5518_, 1);
v_sz_5533_ = lean_array_size(v___y_5531_);
v___x_5534_ = ((size_t)0ULL);
v___x_5535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5531_, v_sz_5533_, v___x_5534_, v_a_5532_, v___y_5523_, v___y_5529_, v___y_5525_, v___y_5530_, v___y_5526_, v___y_5520_, v___y_5527_);
lean_dec_ref(v___y_5531_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
lean_inc(v_a_5536_);
lean_dec_ref_known(v___x_5535_, 1);
v___y_5432_ = v___y_5519_;
v___y_5433_ = v___y_5524_;
v___y_5434_ = v___y_5521_;
v___y_5435_ = v___y_5522_;
v___y_5436_ = v___y_5528_;
v_body_5437_ = v_a_5536_;
v___y_5438_ = v___y_5523_;
v___y_5439_ = v___y_5529_;
v___y_5440_ = v___y_5525_;
v___y_5441_ = v___y_5530_;
v___y_5442_ = v___y_5526_;
v___y_5443_ = v___y_5520_;
v___y_5444_ = v___y_5527_;
goto v___jp_5431_;
}
else
{
lean_object* v_a_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5544_; 
lean_dec(v___y_5528_);
lean_dec_ref(v___y_5524_);
lean_dec(v___y_5521_);
lean_dec(v___y_5519_);
lean_dec_ref(v_dec_5419_);
v_a_5537_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5539_ = v___x_5535_;
v_isShared_5540_ = v_isSharedCheck_5544_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_a_5537_);
lean_dec(v___x_5535_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5544_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5542_; 
if (v_isShared_5540_ == 0)
{
v___x_5542_ = v___x_5539_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_a_5537_);
v___x_5542_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
return v___x_5542_;
}
}
}
}
}
v___jp_5545_:
{
lean_object* v___x_5559_; uint8_t v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; 
v___x_5559_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_5560_ = 0;
v___x_5561_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_5562_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v___y_5551_, v___y_5546_, v___x_5561_, v___y_5550_, v___y_5556_, v___y_5552_, v___y_5557_, v___y_5553_, v___y_5548_, v___y_5554_);
if (lean_obj_tag(v___x_5562_) == 0)
{
lean_object* v_a_5563_; lean_object* v___x_5564_; 
v_a_5563_ = lean_ctor_get(v___x_5562_, 0);
lean_inc(v_a_5563_);
lean_dec_ref_known(v___x_5562_, 1);
v___x_5564_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_5563_, v___y_5557_, v___y_5553_, v___y_5548_, v___y_5554_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v___x_5565_; lean_object* v___x_5566_; 
lean_dec_ref_known(v___x_5564_, 1);
lean_inc(v___y_5546_);
v___x_5565_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5565_, 0, v___y_5546_);
lean_ctor_set_uint8(v___x_5565_, sizeof(void*)*1, v___x_5560_);
lean_inc(v___y_5549_);
v___x_5566_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5549_, v___y_5556_, v___y_5552_, v___y_5557_, v___y_5553_, v___y_5548_, v___y_5554_);
if (lean_obj_tag(v___x_5566_) == 0)
{
lean_object* v_a_5567_; lean_object* v___x_5568_; 
v_a_5567_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_a_5567_);
lean_dec_ref_known(v___x_5566_, 1);
v___x_5568_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5565_, v_a_5567_, v___y_5550_, v___y_5556_, v___y_5552_, v___y_5557_, v___y_5553_, v___y_5548_, v___y_5554_);
lean_dec_ref_known(v___x_5565_, 1);
if (lean_obj_tag(v___x_5568_) == 0)
{
lean_dec_ref_known(v___x_5568_, 1);
if (lean_obj_tag(v___y_5558_) == 0)
{
lean_object* v_toCold_5569_; lean_object* v_ref_5570_; lean_object* v___x_5571_; lean_object* v_a_5572_; lean_object* v_quotContext_5573_; lean_object* v_currMacroScope_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; 
v_toCold_5569_ = lean_ctor_get(v___y_5548_, 0);
v_ref_5570_ = lean_ctor_get(v___y_5548_, 2);
v___x_5571_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5570_, v___y_5550_, v___y_5556_, v___y_5552_, v___y_5557_, v___y_5553_, v___y_5548_, v___y_5554_);
v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
lean_inc_n(v_a_5572_, 9);
lean_dec_ref(v___x_5571_);
v_quotContext_5573_ = lean_ctor_get(v_toCold_5569_, 8);
v_currMacroScope_5574_ = lean_ctor_get(v_toCold_5569_, 9);
v___x_5575_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5576_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5577_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5578_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1));
v___x_5579_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5580_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5574_, 2);
lean_inc_n(v_quotContext_5573_, 2);
v___x_5581_ = l_Lean_addMacroScope(v_quotContext_5573_, v___x_5580_, v_currMacroScope_5574_);
v___x_5582_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5583_, 0, v_a_5572_);
lean_ctor_set(v___x_5583_, 1, v___x_5579_);
lean_ctor_set(v___x_5583_, 2, v___x_5581_);
lean_ctor_set(v___x_5583_, 3, v___x_5582_);
v___x_5584_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5585_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5586_ = l_Lean_addMacroScope(v_quotContext_5573_, v___x_5585_, v_currMacroScope_5574_);
v___x_5587_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5588_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5588_, 0, v_a_5572_);
lean_ctor_set(v___x_5588_, 1, v___x_5584_);
lean_ctor_set(v___x_5588_, 2, v___x_5586_);
lean_ctor_set(v___x_5588_, 3, v___x_5587_);
v___x_5589_ = l_Lean_Syntax_node1(v_a_5572_, v___x_5575_, v___x_5588_);
v___x_5590_ = l_Lean_Syntax_node2(v_a_5572_, v___x_5578_, v___x_5583_, v___x_5589_);
v___x_5591_ = l_Lean_Syntax_node1(v_a_5572_, v___x_5577_, v___x_5590_);
v___x_5592_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5593_, 0, v_a_5572_);
lean_ctor_set(v___x_5593_, 1, v___x_5575_);
lean_ctor_set(v___x_5593_, 2, v___x_5592_);
v___x_5594_ = l_Lean_Syntax_node2(v_a_5572_, v___x_5576_, v___x_5591_, v___x_5593_);
v___x_5595_ = l_Lean_Syntax_node1(v_a_5572_, v___x_5575_, v___x_5594_);
v___x_5596_ = l_Lean_Syntax_node1(v_a_5572_, v___x_5559_, v___x_5595_);
v___y_5518_ = v___y_5546_;
v___y_5519_ = v___y_5547_;
v___y_5520_ = v___y_5548_;
v___y_5521_ = v___y_5549_;
v___y_5522_ = v___x_5560_;
v___y_5523_ = v___y_5550_;
v___y_5524_ = v_a_5563_;
v___y_5525_ = v___y_5552_;
v___y_5526_ = v___y_5553_;
v___y_5527_ = v___y_5554_;
v___y_5528_ = v___y_5555_;
v___y_5529_ = v___y_5556_;
v___y_5530_ = v___y_5557_;
v___y_5531_ = v_a_5567_;
v_a_5532_ = v___x_5596_;
goto v___jp_5517_;
}
else
{
lean_object* v_val_5597_; 
v_val_5597_ = lean_ctor_get(v___y_5558_, 0);
lean_inc(v_val_5597_);
lean_dec_ref_known(v___y_5558_, 1);
v___y_5518_ = v___y_5546_;
v___y_5519_ = v___y_5547_;
v___y_5520_ = v___y_5548_;
v___y_5521_ = v___y_5549_;
v___y_5522_ = v___x_5560_;
v___y_5523_ = v___y_5550_;
v___y_5524_ = v_a_5563_;
v___y_5525_ = v___y_5552_;
v___y_5526_ = v___y_5553_;
v___y_5527_ = v___y_5554_;
v___y_5528_ = v___y_5555_;
v___y_5529_ = v___y_5556_;
v___y_5530_ = v___y_5557_;
v___y_5531_ = v_a_5567_;
v_a_5532_ = v_val_5597_;
goto v___jp_5517_;
}
}
else
{
lean_object* v_a_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5605_; 
lean_dec(v_a_5567_);
lean_dec(v_a_5563_);
lean_dec(v___y_5558_);
lean_dec(v___y_5555_);
lean_dec(v___y_5549_);
lean_dec(v___y_5547_);
lean_dec(v___y_5546_);
lean_dec_ref(v_dec_5419_);
v_a_5598_ = lean_ctor_get(v___x_5568_, 0);
v_isSharedCheck_5605_ = !lean_is_exclusive(v___x_5568_);
if (v_isSharedCheck_5605_ == 0)
{
v___x_5600_ = v___x_5568_;
v_isShared_5601_ = v_isSharedCheck_5605_;
goto v_resetjp_5599_;
}
else
{
lean_inc(v_a_5598_);
lean_dec(v___x_5568_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5605_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
lean_object* v___x_5603_; 
if (v_isShared_5601_ == 0)
{
v___x_5603_ = v___x_5600_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_a_5598_);
v___x_5603_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
return v___x_5603_;
}
}
}
}
else
{
lean_object* v_a_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5613_; 
lean_dec_ref_known(v___x_5565_, 1);
lean_dec(v_a_5563_);
lean_dec(v___y_5558_);
lean_dec(v___y_5555_);
lean_dec(v___y_5549_);
lean_dec(v___y_5547_);
lean_dec(v___y_5546_);
lean_dec_ref(v_dec_5419_);
v_a_5606_ = lean_ctor_get(v___x_5566_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5566_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5608_ = v___x_5566_;
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5566_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5611_; 
if (v_isShared_5609_ == 0)
{
v___x_5611_ = v___x_5608_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
v___x_5611_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
return v___x_5611_;
}
}
}
}
else
{
lean_object* v_a_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5621_; 
lean_dec(v_a_5563_);
lean_dec(v___y_5558_);
lean_dec(v___y_5555_);
lean_dec(v___y_5549_);
lean_dec(v___y_5547_);
lean_dec(v___y_5546_);
lean_dec_ref(v_dec_5419_);
v_a_5614_ = lean_ctor_get(v___x_5564_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5616_ = v___x_5564_;
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_a_5614_);
lean_dec(v___x_5564_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v___x_5619_; 
if (v_isShared_5617_ == 0)
{
v___x_5619_ = v___x_5616_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
}
}
else
{
lean_object* v_a_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5629_; 
lean_dec(v___y_5558_);
lean_dec(v___y_5555_);
lean_dec(v___y_5549_);
lean_dec(v___y_5547_);
lean_dec(v___y_5546_);
lean_dec_ref(v_dec_5419_);
v_a_5622_ = lean_ctor_get(v___x_5562_, 0);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5562_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5624_ = v___x_5562_;
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5562_);
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
v___jp_5630_:
{
lean_object* v___x_5639_; lean_object* v_cfg_5640_; lean_object* v___x_5641_; uint8_t v___x_5642_; 
v___x_5639_ = lean_unsigned_to_nat(2u);
v_cfg_5640_ = l_Lean_Syntax_getArg(v_stx_5418_, v___x_5639_);
v___x_5641_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_5640_);
v___x_5642_ = l_Lean_Syntax_isOfKind(v_cfg_5640_, v___x_5641_);
if (v___x_5642_ == 0)
{
lean_object* v___x_5643_; 
lean_dec(v_cfg_5640_);
lean_dec(v_mutTk_x3f_5631_);
lean_dec_ref(v_dec_5419_);
lean_dec(v_stx_5418_);
v___x_5643_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5643_;
}
else
{
lean_object* v___x_5644_; lean_object* v_pattern_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; 
v___x_5644_ = lean_unsigned_to_nat(3u);
v_pattern_5645_ = l_Lean_Syntax_getArg(v_stx_5418_, v___x_5644_);
v___x_5646_ = lean_unsigned_to_nat(5u);
v___x_5647_ = l_Lean_Syntax_getArg(v_stx_5418_, v___x_5646_);
v___x_5648_ = lean_unsigned_to_nat(7u);
v___x_5649_ = l_Lean_Syntax_getArg(v_stx_5418_, v___x_5648_);
v___x_5650_ = lean_unsigned_to_nat(8u);
v___x_5651_ = l_Lean_Syntax_getArg(v_stx_5418_, v___x_5650_);
lean_dec(v_stx_5418_);
v___x_5652_ = l_Lean_Syntax_getOptional_x3f(v___x_5651_);
lean_dec(v___x_5651_);
if (lean_obj_tag(v___x_5652_) == 0)
{
lean_object* v___x_5653_; 
v___x_5653_ = lean_box(0);
v___y_5546_ = v_mutTk_x3f_5631_;
v___y_5547_ = v___x_5647_;
v___y_5548_ = v___y_5637_;
v___y_5549_ = v_pattern_5645_;
v___y_5550_ = v___y_5632_;
v___y_5551_ = v_cfg_5640_;
v___y_5552_ = v___y_5634_;
v___y_5553_ = v___y_5636_;
v___y_5554_ = v___y_5638_;
v___y_5555_ = v___x_5649_;
v___y_5556_ = v___y_5633_;
v___y_5557_ = v___y_5635_;
v___y_5558_ = v___x_5653_;
goto v___jp_5545_;
}
else
{
lean_object* v_val_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5661_; 
v_val_5654_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5661_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5656_ = v___x_5652_;
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_val_5654_);
lean_dec(v___x_5652_);
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
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_val_5654_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
v___y_5546_ = v_mutTk_x3f_5631_;
v___y_5547_ = v___x_5647_;
v___y_5548_ = v___y_5637_;
v___y_5549_ = v_pattern_5645_;
v___y_5550_ = v___y_5632_;
v___y_5551_ = v_cfg_5640_;
v___y_5552_ = v___y_5634_;
v___y_5553_ = v___y_5636_;
v___y_5554_ = v___y_5638_;
v___y_5555_ = v___x_5649_;
v___y_5556_ = v___y_5633_;
v___y_5557_ = v___y_5635_;
v___y_5558_ = v___x_5659_;
goto v___jp_5545_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5671_, lean_object* v_dec_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_){
_start:
{
lean_object* v_res_5681_; 
v_res_5681_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5671_, v_dec_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_);
lean_dec(v_a_5679_);
lean_dec_ref(v_a_5678_);
lean_dec(v_a_5677_);
lean_dec_ref(v_a_5676_);
lean_dec(v_a_5675_);
lean_dec_ref(v_a_5674_);
lean_dec_ref(v_a_5673_);
return v_res_5681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5682_, size_t v_sz_5683_, size_t v_i_5684_, lean_object* v_b_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
lean_object* v___x_5694_; 
v___x_5694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5682_, v_sz_5683_, v_i_5684_, v_b_5685_, v___y_5691_);
return v___x_5694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5695_, lean_object* v_sz_5696_, lean_object* v_i_5697_, lean_object* v_b_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_){
_start:
{
size_t v_sz_boxed_5707_; size_t v_i_boxed_5708_; lean_object* v_res_5709_; 
v_sz_boxed_5707_ = lean_unbox_usize(v_sz_5696_);
lean_dec(v_sz_5696_);
v_i_boxed_5708_ = lean_unbox_usize(v_i_5697_);
lean_dec(v_i_5697_);
v_res_5709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5695_, v_sz_boxed_5707_, v_i_boxed_5708_, v_b_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_);
lean_dec(v___y_5705_);
lean_dec_ref(v___y_5704_);
lean_dec(v___y_5703_);
lean_dec_ref(v___y_5702_);
lean_dec(v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec_ref(v___y_5699_);
lean_dec_ref(v_as_5695_);
return v_res_5709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; 
v___x_5717_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5718_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
v___x_5719_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5720_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5721_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5717_, v___x_5718_, v___x_5719_, v___x_5720_);
return v___x_5721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5722_){
_start:
{
lean_object* v_res_5723_; 
v_res_5723_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0(lean_object* v_otherwise_x3f_5724_, uint8_t v___x_5725_, lean_object* v___x_5726_, lean_object* v___x_5727_, lean_object* v___x_5728_, lean_object* v___x_5729_, lean_object* v___x_5730_, lean_object* v___x_5731_, lean_object* v_dec_5732_, uint8_t v___x_5733_, lean_object* v_mutTk_x3f_5734_, lean_object* v___x_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5724_) == 0)
{
lean_object* v_ref_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___y_5754_; 
lean_dec(v___y_5736_);
v_ref_5745_ = lean_ctor_get(v___y_5742_, 2);
v___x_5746_ = l_Lean_SourceInfo_fromRef(v_ref_5745_, v___x_5725_);
v___x_5747_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5728_);
lean_inc_ref(v___x_5727_);
lean_inc_ref(v___x_5726_);
v___x_5748_ = l_Lean_Name_mkStr4(v___x_5726_, v___x_5727_, v___x_5728_, v___x_5747_);
v___x_5749_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5746_);
v___x_5750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5746_);
lean_ctor_set(v___x_5750_, 1, v___x_5749_);
v___x_5751_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5752_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5734_) == 1)
{
lean_object* v_val_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; 
v_val_5769_ = lean_ctor_get(v_mutTk_x3f_5734_, 0);
v___x_5770_ = l_Lean_SourceInfo_fromRef(v_val_5769_, v___x_5733_);
v___x_5771_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5770_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = l_Array_mkArray1___redArg(v___x_5772_);
v___y_5754_ = v___x_5773_;
goto v___jp_5753_;
}
else
{
lean_object* v___x_5774_; 
v___x_5774_ = lean_mk_empty_array_with_capacity(v___x_5735_);
v___y_5754_ = v___x_5774_;
goto v___jp_5753_;
}
v___jp_5753_:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; 
v___x_5755_ = l_Array_append___redArg(v___x_5752_, v___y_5754_);
lean_dec_ref(v___y_5754_);
lean_inc_n(v___x_5746_, 6);
v___x_5756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5746_);
lean_ctor_set(v___x_5756_, 1, v___x_5751_);
lean_ctor_set(v___x_5756_, 2, v___x_5755_);
v___x_5757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5746_);
lean_ctor_set(v___x_5757_, 1, v___x_5751_);
lean_ctor_set(v___x_5757_, 2, v___x_5752_);
lean_inc_ref_n(v___x_5757_, 2);
v___x_5758_ = l_Lean_Syntax_node1(v___x_5746_, v___x_5729_, v___x_5757_);
v___x_5759_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5728_);
lean_inc_ref(v___x_5727_);
lean_inc_ref(v___x_5726_);
v___x_5760_ = l_Lean_Name_mkStr4(v___x_5726_, v___x_5727_, v___x_5728_, v___x_5759_);
v___x_5761_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5762_ = l_Lean_Name_mkStr4(v___x_5726_, v___x_5727_, v___x_5728_, v___x_5761_);
v___x_5763_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5764_, 0, v___x_5746_);
lean_ctor_set(v___x_5764_, 1, v___x_5763_);
v___x_5765_ = l_Lean_Syntax_node5(v___x_5746_, v___x_5762_, v___x_5730_, v___x_5757_, v___x_5757_, v___x_5764_, v___x_5731_);
v___x_5766_ = l_Lean_Syntax_node1(v___x_5746_, v___x_5760_, v___x_5765_);
v___x_5767_ = l_Lean_Syntax_node4(v___x_5746_, v___x_5748_, v___x_5750_, v___x_5756_, v___x_5758_, v___x_5766_);
v___x_5768_ = l_Lean_Elab_Do_elabDoElem(v___x_5767_, v_dec_5732_, v___x_5733_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
return v___x_5768_;
}
}
else
{
lean_object* v_val_5775_; lean_object* v_ref_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___y_5785_; lean_object* v___y_5786_; lean_object* v___y_5787_; lean_object* v___y_5788_; lean_object* v___y_5789_; lean_object* v___y_5806_; 
v_val_5775_ = lean_ctor_get(v_otherwise_x3f_5724_, 0);
lean_inc(v_val_5775_);
lean_dec_ref_known(v_otherwise_x3f_5724_, 1);
v_ref_5776_ = lean_ctor_get(v___y_5742_, 2);
v___x_5777_ = l_Lean_SourceInfo_fromRef(v_ref_5776_, v___x_5725_);
v___x_5778_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5779_ = l_Lean_Name_mkStr4(v___x_5726_, v___x_5727_, v___x_5728_, v___x_5778_);
v___x_5780_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5777_);
v___x_5781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5781_, 0, v___x_5777_);
lean_ctor_set(v___x_5781_, 1, v___x_5780_);
v___x_5782_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5783_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5734_) == 1)
{
lean_object* v_val_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; 
v_val_5819_ = lean_ctor_get(v_mutTk_x3f_5734_, 0);
v___x_5820_ = l_Lean_SourceInfo_fromRef(v_val_5819_, v___x_5733_);
v___x_5821_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5822_, 0, v___x_5820_);
lean_ctor_set(v___x_5822_, 1, v___x_5821_);
v___x_5823_ = l_Array_mkArray1___redArg(v___x_5822_);
v___y_5806_ = v___x_5823_;
goto v___jp_5805_;
}
else
{
lean_object* v___x_5824_; 
v___x_5824_ = lean_mk_empty_array_with_capacity(v___x_5735_);
v___y_5806_ = v___x_5824_;
goto v___jp_5805_;
}
v___jp_5784_:
{
lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; 
v___x_5790_ = l_Array_append___redArg(v___x_5783_, v___y_5789_);
lean_dec_ref(v___y_5789_);
lean_inc(v___x_5777_);
v___x_5791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5791_, 0, v___x_5777_);
lean_ctor_set(v___x_5791_, 1, v___x_5782_);
lean_ctor_set(v___x_5791_, 2, v___x_5790_);
v___x_5792_ = lean_unsigned_to_nat(9u);
v___x_5793_ = lean_mk_empty_array_with_capacity(v___x_5792_);
v___x_5794_ = lean_array_push(v___x_5793_, v___x_5781_);
v___x_5795_ = lean_array_push(v___x_5794_, v___y_5787_);
v___x_5796_ = lean_array_push(v___x_5795_, v___y_5786_);
v___x_5797_ = lean_array_push(v___x_5796_, v___x_5730_);
v___x_5798_ = lean_array_push(v___x_5797_, v___y_5785_);
v___x_5799_ = lean_array_push(v___x_5798_, v___x_5731_);
v___x_5800_ = lean_array_push(v___x_5799_, v___y_5788_);
v___x_5801_ = lean_array_push(v___x_5800_, v_val_5775_);
v___x_5802_ = lean_array_push(v___x_5801_, v___x_5791_);
v___x_5803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5803_, 0, v___x_5777_);
lean_ctor_set(v___x_5803_, 1, v___x_5779_);
lean_ctor_set(v___x_5803_, 2, v___x_5802_);
v___x_5804_ = l_Lean_Elab_Do_elabDoElem(v___x_5803_, v_dec_5732_, v___x_5733_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
return v___x_5804_;
}
v___jp_5805_:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; 
v___x_5807_ = l_Array_append___redArg(v___x_5783_, v___y_5806_);
lean_dec_ref(v___y_5806_);
lean_inc_n(v___x_5777_, 5);
v___x_5808_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5808_, 0, v___x_5777_);
lean_ctor_set(v___x_5808_, 1, v___x_5782_);
lean_ctor_set(v___x_5808_, 2, v___x_5807_);
v___x_5809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5809_, 0, v___x_5777_);
lean_ctor_set(v___x_5809_, 1, v___x_5782_);
lean_ctor_set(v___x_5809_, 2, v___x_5783_);
v___x_5810_ = l_Lean_Syntax_node1(v___x_5777_, v___x_5729_, v___x_5809_);
v___x_5811_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5812_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5812_, 0, v___x_5777_);
lean_ctor_set(v___x_5812_, 1, v___x_5811_);
v___x_5813_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5814_, 0, v___x_5777_);
lean_ctor_set(v___x_5814_, 1, v___x_5813_);
if (lean_obj_tag(v___y_5736_) == 0)
{
lean_object* v___x_5815_; 
v___x_5815_ = lean_mk_empty_array_with_capacity(v___x_5735_);
v___y_5785_ = v___x_5812_;
v___y_5786_ = v___x_5810_;
v___y_5787_ = v___x_5808_;
v___y_5788_ = v___x_5814_;
v___y_5789_ = v___x_5815_;
goto v___jp_5784_;
}
else
{
lean_object* v_val_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; 
v_val_5816_ = lean_ctor_get(v___y_5736_, 0);
lean_inc(v_val_5816_);
lean_dec_ref_known(v___y_5736_, 1);
v___x_5817_ = lean_mk_empty_array_with_capacity(v___x_5735_);
v___x_5818_ = lean_array_push(v___x_5817_, v_val_5816_);
v___y_5785_ = v___x_5812_;
v___y_5786_ = v___x_5810_;
v___y_5787_ = v___x_5808_;
v___y_5788_ = v___x_5814_;
v___y_5789_ = v___x_5818_;
goto v___jp_5784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_5825_ = _args[0];
lean_object* v___x_5826_ = _args[1];
lean_object* v___x_5827_ = _args[2];
lean_object* v___x_5828_ = _args[3];
lean_object* v___x_5829_ = _args[4];
lean_object* v___x_5830_ = _args[5];
lean_object* v___x_5831_ = _args[6];
lean_object* v___x_5832_ = _args[7];
lean_object* v_dec_5833_ = _args[8];
lean_object* v___x_5834_ = _args[9];
lean_object* v_mutTk_x3f_5835_ = _args[10];
lean_object* v___x_5836_ = _args[11];
lean_object* v___y_5837_ = _args[12];
lean_object* v___y_5838_ = _args[13];
lean_object* v___y_5839_ = _args[14];
lean_object* v___y_5840_ = _args[15];
lean_object* v___y_5841_ = _args[16];
lean_object* v___y_5842_ = _args[17];
lean_object* v___y_5843_ = _args[18];
lean_object* v___y_5844_ = _args[19];
lean_object* v___y_5845_ = _args[20];
_start:
{
uint8_t v___x_22833__boxed_5846_; uint8_t v___x_22840__boxed_5847_; lean_object* v_res_5848_; 
v___x_22833__boxed_5846_ = lean_unbox(v___x_5826_);
v___x_22840__boxed_5847_ = lean_unbox(v___x_5834_);
v_res_5848_ = l_Lean_Elab_Do_elabDoLetArrow___lam__0(v_otherwise_x3f_5825_, v___x_22833__boxed_5846_, v___x_5827_, v___x_5828_, v___x_5829_, v___x_5830_, v___x_5831_, v___x_5832_, v_dec_5833_, v___x_22840__boxed_5847_, v_mutTk_x3f_5835_, v___x_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
lean_dec(v___y_5844_);
lean_dec_ref(v___y_5843_);
lean_dec(v___y_5842_);
lean_dec_ref(v___y_5841_);
lean_dec(v___y_5840_);
lean_dec_ref(v___y_5839_);
lean_dec_ref(v___y_5838_);
lean_dec(v___x_5836_);
lean_dec(v_mutTk_x3f_5835_);
return v_res_5848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1(lean_object* v_otherwise_x3f_5849_, uint8_t v___x_5850_, lean_object* v___x_5851_, lean_object* v___x_5852_, lean_object* v___x_5853_, lean_object* v___x_5854_, lean_object* v___x_5855_, lean_object* v___x_5856_, lean_object* v_dec_5857_, uint8_t v___x_5858_, lean_object* v_mutTk_x3f_5859_, lean_object* v___x_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5849_) == 0)
{
lean_object* v_ref_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___y_5879_; 
lean_dec(v___y_5861_);
v_ref_5870_ = lean_ctor_get(v___y_5867_, 2);
v___x_5871_ = l_Lean_SourceInfo_fromRef(v_ref_5870_, v___x_5850_);
v___x_5872_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5853_);
lean_inc_ref(v___x_5852_);
lean_inc_ref(v___x_5851_);
v___x_5873_ = l_Lean_Name_mkStr4(v___x_5851_, v___x_5852_, v___x_5853_, v___x_5872_);
v___x_5874_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5871_);
v___x_5875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5871_);
lean_ctor_set(v___x_5875_, 1, v___x_5874_);
v___x_5876_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5877_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5859_) == 1)
{
lean_object* v_val_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; 
v_val_5894_ = lean_ctor_get(v_mutTk_x3f_5859_, 0);
v___x_5895_ = l_Lean_SourceInfo_fromRef(v_val_5894_, v___x_5858_);
v___x_5896_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5897_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5895_);
lean_ctor_set(v___x_5897_, 1, v___x_5896_);
v___x_5898_ = l_Array_mkArray1___redArg(v___x_5897_);
v___y_5879_ = v___x_5898_;
goto v___jp_5878_;
}
else
{
lean_object* v___x_5899_; 
v___x_5899_ = lean_mk_empty_array_with_capacity(v___x_5860_);
v___y_5879_ = v___x_5899_;
goto v___jp_5878_;
}
v___jp_5878_:
{
lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; 
v___x_5880_ = l_Array_append___redArg(v___x_5877_, v___y_5879_);
lean_dec_ref(v___y_5879_);
lean_inc_n(v___x_5871_, 6);
v___x_5881_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5881_, 0, v___x_5871_);
lean_ctor_set(v___x_5881_, 1, v___x_5876_);
lean_ctor_set(v___x_5881_, 2, v___x_5880_);
v___x_5882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5882_, 0, v___x_5871_);
lean_ctor_set(v___x_5882_, 1, v___x_5876_);
lean_ctor_set(v___x_5882_, 2, v___x_5877_);
lean_inc_ref_n(v___x_5882_, 2);
v___x_5883_ = l_Lean_Syntax_node1(v___x_5871_, v___x_5854_, v___x_5882_);
v___x_5884_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5853_);
lean_inc_ref(v___x_5852_);
lean_inc_ref(v___x_5851_);
v___x_5885_ = l_Lean_Name_mkStr4(v___x_5851_, v___x_5852_, v___x_5853_, v___x_5884_);
v___x_5886_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5887_ = l_Lean_Name_mkStr4(v___x_5851_, v___x_5852_, v___x_5853_, v___x_5886_);
v___x_5888_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5889_, 0, v___x_5871_);
lean_ctor_set(v___x_5889_, 1, v___x_5888_);
v___x_5890_ = l_Lean_Syntax_node5(v___x_5871_, v___x_5887_, v___x_5855_, v___x_5882_, v___x_5882_, v___x_5889_, v___x_5856_);
v___x_5891_ = l_Lean_Syntax_node1(v___x_5871_, v___x_5885_, v___x_5890_);
v___x_5892_ = l_Lean_Syntax_node4(v___x_5871_, v___x_5873_, v___x_5875_, v___x_5881_, v___x_5883_, v___x_5891_);
v___x_5893_ = l_Lean_Elab_Do_elabDoElem(v___x_5892_, v_dec_5857_, v___x_5858_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_);
return v___x_5893_;
}
}
else
{
lean_object* v_val_5900_; lean_object* v_ref_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___y_5910_; lean_object* v___y_5911_; lean_object* v___y_5912_; lean_object* v___y_5913_; lean_object* v___y_5914_; lean_object* v___y_5931_; 
v_val_5900_ = lean_ctor_get(v_otherwise_x3f_5849_, 0);
lean_inc(v_val_5900_);
lean_dec_ref_known(v_otherwise_x3f_5849_, 1);
v_ref_5901_ = lean_ctor_get(v___y_5867_, 2);
v___x_5902_ = l_Lean_SourceInfo_fromRef(v_ref_5901_, v___x_5850_);
v___x_5903_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5904_ = l_Lean_Name_mkStr4(v___x_5851_, v___x_5852_, v___x_5853_, v___x_5903_);
v___x_5905_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5902_);
v___x_5906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5902_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v___x_5907_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5908_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5859_) == 1)
{
lean_object* v_val_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; 
v_val_5944_ = lean_ctor_get(v_mutTk_x3f_5859_, 0);
v___x_5945_ = l_Lean_SourceInfo_fromRef(v_val_5944_, v___x_5858_);
v___x_5946_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5945_);
lean_ctor_set(v___x_5947_, 1, v___x_5946_);
v___x_5948_ = l_Array_mkArray1___redArg(v___x_5947_);
v___y_5931_ = v___x_5948_;
goto v___jp_5930_;
}
else
{
lean_object* v___x_5949_; 
v___x_5949_ = lean_mk_empty_array_with_capacity(v___x_5860_);
v___y_5931_ = v___x_5949_;
goto v___jp_5930_;
}
v___jp_5909_:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5915_ = l_Array_append___redArg(v___x_5908_, v___y_5914_);
lean_dec_ref(v___y_5914_);
lean_inc(v___x_5902_);
v___x_5916_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5902_);
lean_ctor_set(v___x_5916_, 1, v___x_5907_);
lean_ctor_set(v___x_5916_, 2, v___x_5915_);
v___x_5917_ = lean_unsigned_to_nat(9u);
v___x_5918_ = lean_mk_empty_array_with_capacity(v___x_5917_);
v___x_5919_ = lean_array_push(v___x_5918_, v___x_5906_);
v___x_5920_ = lean_array_push(v___x_5919_, v___y_5912_);
v___x_5921_ = lean_array_push(v___x_5920_, v___y_5910_);
v___x_5922_ = lean_array_push(v___x_5921_, v___x_5855_);
v___x_5923_ = lean_array_push(v___x_5922_, v___y_5911_);
v___x_5924_ = lean_array_push(v___x_5923_, v___x_5856_);
v___x_5925_ = lean_array_push(v___x_5924_, v___y_5913_);
v___x_5926_ = lean_array_push(v___x_5925_, v_val_5900_);
v___x_5927_ = lean_array_push(v___x_5926_, v___x_5916_);
v___x_5928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5902_);
lean_ctor_set(v___x_5928_, 1, v___x_5904_);
lean_ctor_set(v___x_5928_, 2, v___x_5927_);
v___x_5929_ = l_Lean_Elab_Do_elabDoElem(v___x_5928_, v_dec_5857_, v___x_5858_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_);
return v___x_5929_;
}
v___jp_5930_:
{
lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; 
v___x_5932_ = l_Array_append___redArg(v___x_5908_, v___y_5931_);
lean_dec_ref(v___y_5931_);
lean_inc_n(v___x_5902_, 5);
v___x_5933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5902_);
lean_ctor_set(v___x_5933_, 1, v___x_5907_);
lean_ctor_set(v___x_5933_, 2, v___x_5932_);
v___x_5934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5902_);
lean_ctor_set(v___x_5934_, 1, v___x_5907_);
lean_ctor_set(v___x_5934_, 2, v___x_5908_);
v___x_5935_ = l_Lean_Syntax_node1(v___x_5902_, v___x_5854_, v___x_5934_);
v___x_5936_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5902_);
lean_ctor_set(v___x_5937_, 1, v___x_5936_);
v___x_5938_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5939_, 0, v___x_5902_);
lean_ctor_set(v___x_5939_, 1, v___x_5938_);
if (lean_obj_tag(v___y_5861_) == 0)
{
lean_object* v___x_5940_; 
v___x_5940_ = lean_mk_empty_array_with_capacity(v___x_5860_);
v___y_5910_ = v___x_5935_;
v___y_5911_ = v___x_5937_;
v___y_5912_ = v___x_5933_;
v___y_5913_ = v___x_5939_;
v___y_5914_ = v___x_5940_;
goto v___jp_5909_;
}
else
{
lean_object* v_val_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; 
v_val_5941_ = lean_ctor_get(v___y_5861_, 0);
lean_inc(v_val_5941_);
lean_dec_ref_known(v___y_5861_, 1);
v___x_5942_ = lean_mk_empty_array_with_capacity(v___x_5860_);
v___x_5943_ = lean_array_push(v___x_5942_, v_val_5941_);
v___y_5910_ = v___x_5935_;
v___y_5911_ = v___x_5937_;
v___y_5912_ = v___x_5933_;
v___y_5913_ = v___x_5939_;
v___y_5914_ = v___x_5943_;
goto v___jp_5909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_5950_ = _args[0];
lean_object* v___x_5951_ = _args[1];
lean_object* v___x_5952_ = _args[2];
lean_object* v___x_5953_ = _args[3];
lean_object* v___x_5954_ = _args[4];
lean_object* v___x_5955_ = _args[5];
lean_object* v___x_5956_ = _args[6];
lean_object* v___x_5957_ = _args[7];
lean_object* v_dec_5958_ = _args[8];
lean_object* v___x_5959_ = _args[9];
lean_object* v_mutTk_x3f_5960_ = _args[10];
lean_object* v___x_5961_ = _args[11];
lean_object* v___y_5962_ = _args[12];
lean_object* v___y_5963_ = _args[13];
lean_object* v___y_5964_ = _args[14];
lean_object* v___y_5965_ = _args[15];
lean_object* v___y_5966_ = _args[16];
lean_object* v___y_5967_ = _args[17];
lean_object* v___y_5968_ = _args[18];
lean_object* v___y_5969_ = _args[19];
lean_object* v___y_5970_ = _args[20];
_start:
{
uint8_t v___x_23064__boxed_5971_; uint8_t v___x_23071__boxed_5972_; lean_object* v_res_5973_; 
v___x_23064__boxed_5971_ = lean_unbox(v___x_5951_);
v___x_23071__boxed_5972_ = lean_unbox(v___x_5959_);
v_res_5973_ = l_Lean_Elab_Do_elabDoLetArrow___lam__1(v_otherwise_x3f_5950_, v___x_23064__boxed_5971_, v___x_5952_, v___x_5953_, v___x_5954_, v___x_5955_, v___x_5956_, v___x_5957_, v_dec_5958_, v___x_23071__boxed_5972_, v_mutTk_x3f_5960_, v___x_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
lean_dec(v___y_5969_);
lean_dec_ref(v___y_5968_);
lean_dec(v___y_5967_);
lean_dec_ref(v___y_5966_);
lean_dec(v___y_5965_);
lean_dec_ref(v___y_5964_);
lean_dec_ref(v___y_5963_);
lean_dec(v___x_5961_);
lean_dec(v_mutTk_x3f_5960_);
return v_res_5973_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1(void){
_start:
{
lean_object* v___x_5975_; lean_object* v___x_5976_; 
v___x_5975_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__0));
v___x_5976_ = l_Lean_stringToMessageData(v___x_5975_);
return v___x_5976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5983_, lean_object* v_dec_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_){
_start:
{
lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; uint8_t v___x_5997_; 
v___x_5993_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_5994_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_5995_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_5996_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
lean_inc(v_stx_5983_);
v___x_5997_ = l_Lean_Syntax_isOfKind(v_stx_5983_, v___x_5996_);
if (v___x_5997_ == 0)
{
lean_object* v___x_5998_; 
lean_dec_ref(v_dec_5984_);
lean_dec(v_stx_5983_);
v___x_5998_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5998_;
}
else
{
lean_object* v___x_5999_; lean_object* v___y_6001_; lean_object* v___y_6002_; lean_object* v___y_6003_; lean_object* v___y_6004_; lean_object* v___y_6005_; lean_object* v___y_6006_; lean_object* v___y_6007_; lean_object* v___y_6008_; lean_object* v___y_6009_; uint8_t v___y_6010_; uint8_t v___y_6011_; lean_object* v___y_6012_; lean_object* v___y_6013_; lean_object* v___y_6014_; lean_object* v___y_6015_; lean_object* v___y_6016_; lean_object* v___y_6017_; uint8_t v___y_6036_; lean_object* v___y_6037_; lean_object* v___y_6038_; lean_object* v___y_6039_; lean_object* v___y_6040_; lean_object* v___y_6041_; lean_object* v___y_6042_; lean_object* v___y_6043_; lean_object* v___y_6044_; lean_object* v___y_6045_; lean_object* v___y_6046_; lean_object* v___y_6047_; lean_object* v___y_6048_; lean_object* v___y_6049_; lean_object* v___y_6050_; uint8_t v___y_6051_; lean_object* v___y_6052_; lean_object* v___y_6055_; lean_object* v___y_6056_; lean_object* v___y_6057_; lean_object* v___y_6058_; uint8_t v___y_6059_; lean_object* v___y_6060_; lean_object* v___y_6061_; lean_object* v___y_6062_; uint8_t v___y_6063_; lean_object* v___y_6064_; lean_object* v___y_6065_; lean_object* v___y_6066_; lean_object* v___y_6067_; lean_object* v___y_6068_; lean_object* v___y_6069_; lean_object* v___y_6070_; lean_object* v___y_6071_; lean_object* v___y_6090_; uint8_t v___y_6091_; lean_object* v___y_6092_; lean_object* v___y_6093_; lean_object* v___y_6094_; lean_object* v___y_6095_; lean_object* v___y_6096_; lean_object* v___y_6097_; lean_object* v___y_6098_; lean_object* v___y_6099_; lean_object* v___y_6100_; lean_object* v___y_6101_; uint8_t v___y_6102_; lean_object* v___y_6103_; lean_object* v___y_6104_; lean_object* v___y_6105_; lean_object* v___y_6106_; lean_object* v_tk_6108_; lean_object* v___x_6109_; uint8_t v___y_6111_; lean_object* v___y_6112_; lean_object* v___y_6113_; lean_object* v___y_6114_; lean_object* v___y_6115_; lean_object* v___y_6116_; lean_object* v___y_6117_; uint8_t v___y_6118_; lean_object* v___y_6119_; lean_object* v___y_6120_; lean_object* v___y_6121_; lean_object* v_patType_x3f_6122_; lean_object* v___y_6123_; lean_object* v___y_6124_; lean_object* v___y_6125_; lean_object* v___y_6126_; lean_object* v___y_6127_; lean_object* v___y_6128_; lean_object* v___y_6129_; lean_object* v___y_6174_; uint8_t v___y_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; lean_object* v___y_6179_; lean_object* v___y_6180_; uint8_t v___y_6181_; lean_object* v___y_6182_; lean_object* v___y_6183_; lean_object* v_patType_x3f_6184_; lean_object* v___y_6185_; lean_object* v___y_6186_; lean_object* v___y_6187_; lean_object* v___y_6188_; lean_object* v___y_6189_; lean_object* v___y_6190_; lean_object* v___y_6191_; lean_object* v___y_6210_; lean_object* v___y_6211_; lean_object* v___y_6212_; uint8_t v___y_6213_; lean_object* v___y_6214_; lean_object* v_xType_x3f_6215_; lean_object* v___y_6216_; lean_object* v___y_6217_; lean_object* v___y_6218_; lean_object* v___y_6219_; lean_object* v___y_6220_; lean_object* v___y_6221_; lean_object* v___y_6222_; lean_object* v___y_6251_; lean_object* v___y_6252_; lean_object* v___y_6253_; lean_object* v___y_6254_; lean_object* v___y_6255_; lean_object* v___y_6256_; lean_object* v___y_6257_; uint8_t v___y_6258_; lean_object* v___y_6259_; lean_object* v___y_6260_; lean_object* v___y_6261_; lean_object* v___y_6262_; lean_object* v___y_6263_; lean_object* v___y_6264_; lean_object* v___y_6265_; lean_object* v___y_6266_; lean_object* v___y_6267_; lean_object* v___y_6310_; lean_object* v___y_6311_; lean_object* v___y_6312_; lean_object* v___y_6313_; lean_object* v___y_6314_; lean_object* v___y_6315_; lean_object* v___y_6316_; lean_object* v___y_6317_; lean_object* v___y_6318_; lean_object* v___y_6319_; lean_object* v___y_6320_; lean_object* v___y_6321_; lean_object* v___y_6322_; lean_object* v___y_6323_; lean_object* v___y_6324_; uint8_t v___y_6325_; lean_object* v___y_6326_; lean_object* v___y_6327_; lean_object* v_mutTk_x3f_6339_; lean_object* v___y_6340_; lean_object* v___y_6341_; lean_object* v___y_6342_; lean_object* v___y_6343_; lean_object* v___y_6344_; lean_object* v___y_6345_; lean_object* v___y_6346_; lean_object* v___x_6382_; uint8_t v___x_6383_; 
v___x_5999_ = lean_unsigned_to_nat(0u);
v_tk_6108_ = l_Lean_Syntax_getArg(v_stx_5983_, v___x_5999_);
v___x_6109_ = lean_unsigned_to_nat(1u);
v___x_6382_ = l_Lean_Syntax_getArg(v_stx_5983_, v___x_6109_);
v___x_6383_ = l_Lean_Syntax_isNone(v___x_6382_);
if (v___x_6383_ == 0)
{
uint8_t v___x_6384_; 
lean_inc(v___x_6382_);
v___x_6384_ = l_Lean_Syntax_matchesNull(v___x_6382_, v___x_6109_);
if (v___x_6384_ == 0)
{
lean_object* v___x_6385_; 
lean_dec(v___x_6382_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
lean_dec(v_stx_5983_);
v___x_6385_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6385_;
}
else
{
lean_object* v_mutTk_x3f_6386_; lean_object* v___x_6387_; 
v_mutTk_x3f_6386_ = l_Lean_Syntax_getArg(v___x_6382_, v___x_5999_);
lean_dec(v___x_6382_);
v___x_6387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6387_, 0, v_mutTk_x3f_6386_);
v_mutTk_x3f_6339_ = v___x_6387_;
v___y_6340_ = v_a_5985_;
v___y_6341_ = v_a_5986_;
v___y_6342_ = v_a_5987_;
v___y_6343_ = v_a_5988_;
v___y_6344_ = v_a_5989_;
v___y_6345_ = v_a_5990_;
v___y_6346_ = v_a_5991_;
goto v___jp_6338_;
}
}
else
{
lean_object* v___x_6388_; 
lean_dec(v___x_6382_);
v___x_6388_ = lean_box(0);
v_mutTk_x3f_6339_ = v___x_6388_;
v___y_6340_ = v_a_5985_;
v___y_6341_ = v_a_5986_;
v___y_6342_ = v_a_5987_;
v___y_6343_ = v_a_5988_;
v___y_6344_ = v_a_5989_;
v___y_6345_ = v_a_5990_;
v___y_6346_ = v_a_5991_;
goto v___jp_6338_;
}
v___jp_6000_:
{
lean_object* v___x_6018_; lean_object* v___x_6019_; 
v___x_6018_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6019_ = l_Lean_Core_mkFreshUserName(v___x_6018_, v___y_6001_, v___y_6009_);
if (lean_obj_tag(v___x_6019_) == 0)
{
lean_object* v_a_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___y_6024_; uint8_t v___x_6025_; lean_object* v___x_6026_; 
v_a_6020_ = lean_ctor_get(v___x_6019_, 0);
lean_inc(v_a_6020_);
lean_dec_ref_known(v___x_6019_, 1);
v___x_6021_ = l_Lean_mkIdentFrom(v___y_6006_, v_a_6020_, v___y_6011_);
lean_dec(v___y_6006_);
v___x_6022_ = lean_box(v___y_6010_);
v___x_6023_ = lean_box(v___x_5997_);
lean_inc(v___x_6021_);
lean_inc(v___y_6003_);
v___y_6024_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_6024_, 0, v___y_6013_);
lean_closure_set(v___y_6024_, 1, v___x_6022_);
lean_closure_set(v___y_6024_, 2, v___x_5993_);
lean_closure_set(v___y_6024_, 3, v___x_5994_);
lean_closure_set(v___y_6024_, 4, v___x_5995_);
lean_closure_set(v___y_6024_, 5, v___y_6003_);
lean_closure_set(v___y_6024_, 6, v___y_6007_);
lean_closure_set(v___y_6024_, 7, v___x_6021_);
lean_closure_set(v___y_6024_, 8, v_dec_5984_);
lean_closure_set(v___y_6024_, 9, v___x_6023_);
lean_closure_set(v___y_6024_, 10, v___y_6015_);
lean_closure_set(v___y_6024_, 11, v___x_5999_);
lean_closure_set(v___y_6024_, 12, v___y_6017_);
v___x_6025_ = 0;
v___x_6026_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6021_, v___y_6004_, v___y_6014_, v___y_6024_, v___x_6025_, v___y_6012_, v___y_6005_, v___y_6016_, v___y_6002_, v___y_6008_, v___y_6001_, v___y_6009_);
return v___x_6026_;
}
else
{
lean_object* v_a_6027_; lean_object* v___x_6029_; uint8_t v_isShared_6030_; uint8_t v_isSharedCheck_6034_; 
lean_dec(v___y_6017_);
lean_dec(v___y_6015_);
lean_dec(v___y_6014_);
lean_dec(v___y_6013_);
lean_dec(v___y_6007_);
lean_dec(v___y_6006_);
lean_dec(v___y_6004_);
lean_dec_ref(v_dec_5984_);
v_a_6027_ = lean_ctor_get(v___x_6019_, 0);
v_isSharedCheck_6034_ = !lean_is_exclusive(v___x_6019_);
if (v_isSharedCheck_6034_ == 0)
{
v___x_6029_ = v___x_6019_;
v_isShared_6030_ = v_isSharedCheck_6034_;
goto v_resetjp_6028_;
}
else
{
lean_inc(v_a_6027_);
lean_dec(v___x_6019_);
v___x_6029_ = lean_box(0);
v_isShared_6030_ = v_isSharedCheck_6034_;
goto v_resetjp_6028_;
}
v_resetjp_6028_:
{
lean_object* v___x_6032_; 
if (v_isShared_6030_ == 0)
{
v___x_6032_ = v___x_6029_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v_a_6027_);
v___x_6032_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
return v___x_6032_;
}
}
}
}
v___jp_6035_:
{
lean_object* v___x_6053_; 
v___x_6053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6053_, 0, v___y_6046_);
v___y_6001_ = v___y_6041_;
v___y_6002_ = v___y_6040_;
v___y_6003_ = v___y_6037_;
v___y_6004_ = v___y_6048_;
v___y_6005_ = v___y_6042_;
v___y_6006_ = v___y_6045_;
v___y_6007_ = v___y_6039_;
v___y_6008_ = v___y_6050_;
v___y_6009_ = v___y_6043_;
v___y_6010_ = v___y_6036_;
v___y_6011_ = v___y_6051_;
v___y_6012_ = v___y_6047_;
v___y_6013_ = v___x_6053_;
v___y_6014_ = v___y_6049_;
v___y_6015_ = v___y_6038_;
v___y_6016_ = v___y_6044_;
v___y_6017_ = v___y_6052_;
goto v___jp_6000_;
}
v___jp_6054_:
{
lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6072_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6073_ = l_Lean_Core_mkFreshUserName(v___x_6072_, v___y_6067_, v___y_6055_);
if (lean_obj_tag(v___x_6073_) == 0)
{
lean_object* v_a_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___y_6078_; uint8_t v___x_6079_; lean_object* v___x_6080_; 
v_a_6074_ = lean_ctor_get(v___x_6073_, 0);
lean_inc(v_a_6074_);
lean_dec_ref_known(v___x_6073_, 1);
v___x_6075_ = l_Lean_mkIdentFrom(v___y_6058_, v_a_6074_, v___y_6059_);
lean_dec(v___y_6058_);
v___x_6076_ = lean_box(v___y_6063_);
v___x_6077_ = lean_box(v___x_5997_);
lean_inc(v___x_6075_);
lean_inc(v___y_6056_);
v___y_6078_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed), 21, 13);
lean_closure_set(v___y_6078_, 0, v___y_6069_);
lean_closure_set(v___y_6078_, 1, v___x_6076_);
lean_closure_set(v___y_6078_, 2, v___x_5993_);
lean_closure_set(v___y_6078_, 3, v___x_5994_);
lean_closure_set(v___y_6078_, 4, v___x_5995_);
lean_closure_set(v___y_6078_, 5, v___y_6056_);
lean_closure_set(v___y_6078_, 6, v___y_6062_);
lean_closure_set(v___y_6078_, 7, v___x_6075_);
lean_closure_set(v___y_6078_, 8, v_dec_5984_);
lean_closure_set(v___y_6078_, 9, v___x_6077_);
lean_closure_set(v___y_6078_, 10, v___y_6070_);
lean_closure_set(v___y_6078_, 11, v___x_5999_);
lean_closure_set(v___y_6078_, 12, v___y_6071_);
v___x_6079_ = 0;
v___x_6080_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6075_, v___y_6064_, v___y_6065_, v___y_6078_, v___x_6079_, v___y_6061_, v___y_6068_, v___y_6060_, v___y_6057_, v___y_6066_, v___y_6067_, v___y_6055_);
return v___x_6080_;
}
else
{
lean_object* v_a_6081_; lean_object* v___x_6083_; uint8_t v_isShared_6084_; uint8_t v_isSharedCheck_6088_; 
lean_dec(v___y_6071_);
lean_dec(v___y_6070_);
lean_dec(v___y_6069_);
lean_dec(v___y_6065_);
lean_dec(v___y_6064_);
lean_dec(v___y_6062_);
lean_dec(v___y_6058_);
lean_dec_ref(v_dec_5984_);
v_a_6081_ = lean_ctor_get(v___x_6073_, 0);
v_isSharedCheck_6088_ = !lean_is_exclusive(v___x_6073_);
if (v_isSharedCheck_6088_ == 0)
{
v___x_6083_ = v___x_6073_;
v_isShared_6084_ = v_isSharedCheck_6088_;
goto v_resetjp_6082_;
}
else
{
lean_inc(v_a_6081_);
lean_dec(v___x_6073_);
v___x_6083_ = lean_box(0);
v_isShared_6084_ = v_isSharedCheck_6088_;
goto v_resetjp_6082_;
}
v_resetjp_6082_:
{
lean_object* v___x_6086_; 
if (v_isShared_6084_ == 0)
{
v___x_6086_ = v___x_6083_;
goto v_reusejp_6085_;
}
else
{
lean_object* v_reuseFailAlloc_6087_; 
v_reuseFailAlloc_6087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6087_, 0, v_a_6081_);
v___x_6086_ = v_reuseFailAlloc_6087_;
goto v_reusejp_6085_;
}
v_reusejp_6085_:
{
return v___x_6086_;
}
}
}
}
v___jp_6089_:
{
lean_object* v___x_6107_; 
v___x_6107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6107_, 0, v___y_6097_);
v___y_6055_ = v___y_6098_;
v___y_6056_ = v___y_6090_;
v___y_6057_ = v___y_6105_;
v___y_6058_ = v___y_6096_;
v___y_6059_ = v___y_6102_;
v___y_6060_ = v___y_6100_;
v___y_6061_ = v___y_6103_;
v___y_6062_ = v___y_6093_;
v___y_6063_ = v___y_6091_;
v___y_6064_ = v___y_6101_;
v___y_6065_ = v___y_6094_;
v___y_6066_ = v___y_6104_;
v___y_6067_ = v___y_6095_;
v___y_6068_ = v___y_6099_;
v___y_6069_ = v___x_6107_;
v___y_6070_ = v___y_6092_;
v___y_6071_ = v___y_6106_;
goto v___jp_6054_;
}
v___jp_6110_:
{
lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; uint8_t v___x_6133_; 
v___x_6130_ = l_Lean_Syntax_getArg(v___y_6115_, v___y_6117_);
v___x_6131_ = lean_unsigned_to_nat(4u);
v___x_6132_ = l_Lean_Syntax_getArg(v___y_6115_, v___x_6131_);
lean_dec(v___y_6115_);
lean_inc(v___x_6132_);
v___x_6133_ = l_Lean_Syntax_matchesNull(v___x_6132_, v___x_5999_);
if (v___x_6133_ == 0)
{
uint8_t v___x_6134_; 
lean_dec(v___y_6120_);
lean_dec(v_tk_6108_);
v___x_6134_ = l_Lean_Syntax_isNone(v___x_6132_);
if (v___x_6134_ == 0)
{
uint8_t v___x_6135_; 
lean_inc(v___x_6132_);
v___x_6135_ = l_Lean_Syntax_matchesNull(v___x_6132_, v___y_6117_);
if (v___x_6135_ == 0)
{
lean_object* v___x_6136_; 
lean_dec(v___x_6132_);
lean_dec(v___x_6130_);
lean_dec(v_patType_x3f_6122_);
lean_dec(v___y_6121_);
lean_dec(v___y_6114_);
lean_dec(v___y_6113_);
lean_dec_ref(v_dec_5984_);
v___x_6136_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6136_;
}
else
{
lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; 
v___x_6137_ = l_Lean_Syntax_getArg(v___x_6132_, v___x_6109_);
v___x_6138_ = l_Lean_Syntax_getArg(v___x_6132_, v___y_6119_);
lean_dec(v___x_6132_);
v___x_6139_ = l_Lean_Syntax_getOptional_x3f(v___x_6138_);
lean_dec(v___x_6138_);
if (lean_obj_tag(v___x_6139_) == 0)
{
lean_inc(v___y_6116_);
v___y_6036_ = v___y_6111_;
v___y_6037_ = v___y_6112_;
v___y_6038_ = v___y_6113_;
v___y_6039_ = v___y_6114_;
v___y_6040_ = v___y_6126_;
v___y_6041_ = v___y_6128_;
v___y_6042_ = v___y_6124_;
v___y_6043_ = v___y_6129_;
v___y_6044_ = v___y_6125_;
v___y_6045_ = v___y_6121_;
v___y_6046_ = v___x_6137_;
v___y_6047_ = v___y_6123_;
v___y_6048_ = v_patType_x3f_6122_;
v___y_6049_ = v___x_6130_;
v___y_6050_ = v___y_6127_;
v___y_6051_ = v___y_6118_;
v___y_6052_ = v___y_6116_;
goto v___jp_6035_;
}
else
{
lean_object* v_val_6140_; lean_object* v___x_6142_; uint8_t v_isShared_6143_; uint8_t v_isSharedCheck_6147_; 
v_val_6140_ = lean_ctor_get(v___x_6139_, 0);
v_isSharedCheck_6147_ = !lean_is_exclusive(v___x_6139_);
if (v_isSharedCheck_6147_ == 0)
{
v___x_6142_ = v___x_6139_;
v_isShared_6143_ = v_isSharedCheck_6147_;
goto v_resetjp_6141_;
}
else
{
lean_inc(v_val_6140_);
lean_dec(v___x_6139_);
v___x_6142_ = lean_box(0);
v_isShared_6143_ = v_isSharedCheck_6147_;
goto v_resetjp_6141_;
}
v_resetjp_6141_:
{
lean_object* v___x_6145_; 
if (v_isShared_6143_ == 0)
{
v___x_6145_ = v___x_6142_;
goto v_reusejp_6144_;
}
else
{
lean_object* v_reuseFailAlloc_6146_; 
v_reuseFailAlloc_6146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6146_, 0, v_val_6140_);
v___x_6145_ = v_reuseFailAlloc_6146_;
goto v_reusejp_6144_;
}
v_reusejp_6144_:
{
v___y_6036_ = v___y_6111_;
v___y_6037_ = v___y_6112_;
v___y_6038_ = v___y_6113_;
v___y_6039_ = v___y_6114_;
v___y_6040_ = v___y_6126_;
v___y_6041_ = v___y_6128_;
v___y_6042_ = v___y_6124_;
v___y_6043_ = v___y_6129_;
v___y_6044_ = v___y_6125_;
v___y_6045_ = v___y_6121_;
v___y_6046_ = v___x_6137_;
v___y_6047_ = v___y_6123_;
v___y_6048_ = v_patType_x3f_6122_;
v___y_6049_ = v___x_6130_;
v___y_6050_ = v___y_6127_;
v___y_6051_ = v___y_6118_;
v___y_6052_ = v___x_6145_;
goto v___jp_6035_;
}
}
}
}
}
else
{
lean_dec(v___x_6132_);
lean_inc_n(v___y_6116_, 2);
v___y_6001_ = v___y_6128_;
v___y_6002_ = v___y_6126_;
v___y_6003_ = v___y_6112_;
v___y_6004_ = v_patType_x3f_6122_;
v___y_6005_ = v___y_6124_;
v___y_6006_ = v___y_6121_;
v___y_6007_ = v___y_6114_;
v___y_6008_ = v___y_6127_;
v___y_6009_ = v___y_6129_;
v___y_6010_ = v___y_6111_;
v___y_6011_ = v___y_6118_;
v___y_6012_ = v___y_6123_;
v___y_6013_ = v___y_6116_;
v___y_6014_ = v___x_6130_;
v___y_6015_ = v___y_6113_;
v___y_6016_ = v___y_6125_;
v___y_6017_ = v___y_6116_;
goto v___jp_6000_;
}
}
else
{
lean_object* v___x_6148_; lean_object* v___x_6149_; 
lean_dec(v___x_6132_);
lean_dec(v___y_6121_);
lean_dec(v___y_6114_);
lean_dec(v___y_6113_);
v___x_6148_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6149_ = l_Lean_Core_mkFreshUserName(v___x_6148_, v___y_6128_, v___y_6129_);
if (lean_obj_tag(v___x_6149_) == 0)
{
lean_object* v_a_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; 
v_a_6150_ = lean_ctor_get(v___x_6149_, 0);
lean_inc(v_a_6150_);
lean_dec_ref_known(v___x_6149_, 1);
v___x_6151_ = l_Lean_mkIdentFrom(v___y_6120_, v_a_6150_, v___y_6118_);
lean_dec(v___y_6120_);
v___x_6152_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_5984_, v_tk_6108_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_);
lean_dec(v_tk_6108_);
if (lean_obj_tag(v___x_6152_) == 0)
{
lean_object* v_a_6153_; uint8_t v_kind_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; 
v_a_6153_ = lean_ctor_get(v___x_6152_, 0);
lean_inc(v_a_6153_);
lean_dec_ref_known(v___x_6152_, 1);
v_kind_6154_ = lean_ctor_get_uint8(v_a_6153_, sizeof(void*)*3);
v___x_6155_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6155_, 0, v_a_6153_);
v___x_6156_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6151_, v_patType_x3f_6122_, v___x_6130_, v___x_6155_, v_kind_6154_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_);
return v___x_6156_;
}
else
{
lean_object* v_a_6157_; lean_object* v___x_6159_; uint8_t v_isShared_6160_; uint8_t v_isSharedCheck_6164_; 
lean_dec(v___x_6151_);
lean_dec(v___x_6130_);
lean_dec(v_patType_x3f_6122_);
v_a_6157_ = lean_ctor_get(v___x_6152_, 0);
v_isSharedCheck_6164_ = !lean_is_exclusive(v___x_6152_);
if (v_isSharedCheck_6164_ == 0)
{
v___x_6159_ = v___x_6152_;
v_isShared_6160_ = v_isSharedCheck_6164_;
goto v_resetjp_6158_;
}
else
{
lean_inc(v_a_6157_);
lean_dec(v___x_6152_);
v___x_6159_ = lean_box(0);
v_isShared_6160_ = v_isSharedCheck_6164_;
goto v_resetjp_6158_;
}
v_resetjp_6158_:
{
lean_object* v___x_6162_; 
if (v_isShared_6160_ == 0)
{
v___x_6162_ = v___x_6159_;
goto v_reusejp_6161_;
}
else
{
lean_object* v_reuseFailAlloc_6163_; 
v_reuseFailAlloc_6163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6163_, 0, v_a_6157_);
v___x_6162_ = v_reuseFailAlloc_6163_;
goto v_reusejp_6161_;
}
v_reusejp_6161_:
{
return v___x_6162_;
}
}
}
}
else
{
lean_object* v_a_6165_; lean_object* v___x_6167_; uint8_t v_isShared_6168_; uint8_t v_isSharedCheck_6172_; 
lean_dec(v___x_6130_);
lean_dec(v_patType_x3f_6122_);
lean_dec(v___y_6120_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v_a_6165_ = lean_ctor_get(v___x_6149_, 0);
v_isSharedCheck_6172_ = !lean_is_exclusive(v___x_6149_);
if (v_isSharedCheck_6172_ == 0)
{
v___x_6167_ = v___x_6149_;
v_isShared_6168_ = v_isSharedCheck_6172_;
goto v_resetjp_6166_;
}
else
{
lean_inc(v_a_6165_);
lean_dec(v___x_6149_);
v___x_6167_ = lean_box(0);
v_isShared_6168_ = v_isSharedCheck_6172_;
goto v_resetjp_6166_;
}
v_resetjp_6166_:
{
lean_object* v___x_6170_; 
if (v_isShared_6168_ == 0)
{
v___x_6170_ = v___x_6167_;
goto v_reusejp_6169_;
}
else
{
lean_object* v_reuseFailAlloc_6171_; 
v_reuseFailAlloc_6171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6171_, 0, v_a_6165_);
v___x_6170_ = v_reuseFailAlloc_6171_;
goto v_reusejp_6169_;
}
v_reusejp_6169_:
{
return v___x_6170_;
}
}
}
}
}
v___jp_6173_:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; uint8_t v___x_6195_; 
v___x_6192_ = l_Lean_Syntax_getArg(v___y_6178_, v___y_6180_);
v___x_6193_ = lean_unsigned_to_nat(4u);
v___x_6194_ = l_Lean_Syntax_getArg(v___y_6178_, v___x_6193_);
lean_dec(v___y_6178_);
v___x_6195_ = l_Lean_Syntax_isNone(v___x_6194_);
if (v___x_6195_ == 0)
{
uint8_t v___x_6196_; 
lean_inc(v___x_6194_);
v___x_6196_ = l_Lean_Syntax_matchesNull(v___x_6194_, v___y_6180_);
if (v___x_6196_ == 0)
{
lean_object* v___x_6197_; 
lean_dec(v___x_6194_);
lean_dec(v___x_6192_);
lean_dec(v_patType_x3f_6184_);
lean_dec(v___y_6183_);
lean_dec(v___y_6177_);
lean_dec(v___y_6176_);
lean_dec_ref(v_dec_5984_);
v___x_6197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6197_;
}
else
{
lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; 
v___x_6198_ = l_Lean_Syntax_getArg(v___x_6194_, v___x_6109_);
v___x_6199_ = l_Lean_Syntax_getArg(v___x_6194_, v___y_6182_);
lean_dec(v___x_6194_);
v___x_6200_ = l_Lean_Syntax_getOptional_x3f(v___x_6199_);
lean_dec(v___x_6199_);
if (lean_obj_tag(v___x_6200_) == 0)
{
lean_inc(v___y_6179_);
v___y_6090_ = v___y_6174_;
v___y_6091_ = v___y_6175_;
v___y_6092_ = v___y_6176_;
v___y_6093_ = v___y_6177_;
v___y_6094_ = v___x_6192_;
v___y_6095_ = v___y_6190_;
v___y_6096_ = v___y_6183_;
v___y_6097_ = v___x_6198_;
v___y_6098_ = v___y_6191_;
v___y_6099_ = v___y_6186_;
v___y_6100_ = v___y_6187_;
v___y_6101_ = v_patType_x3f_6184_;
v___y_6102_ = v___y_6181_;
v___y_6103_ = v___y_6185_;
v___y_6104_ = v___y_6189_;
v___y_6105_ = v___y_6188_;
v___y_6106_ = v___y_6179_;
goto v___jp_6089_;
}
else
{
lean_object* v_val_6201_; lean_object* v___x_6203_; uint8_t v_isShared_6204_; uint8_t v_isSharedCheck_6208_; 
v_val_6201_ = lean_ctor_get(v___x_6200_, 0);
v_isSharedCheck_6208_ = !lean_is_exclusive(v___x_6200_);
if (v_isSharedCheck_6208_ == 0)
{
v___x_6203_ = v___x_6200_;
v_isShared_6204_ = v_isSharedCheck_6208_;
goto v_resetjp_6202_;
}
else
{
lean_inc(v_val_6201_);
lean_dec(v___x_6200_);
v___x_6203_ = lean_box(0);
v_isShared_6204_ = v_isSharedCheck_6208_;
goto v_resetjp_6202_;
}
v_resetjp_6202_:
{
lean_object* v___x_6206_; 
if (v_isShared_6204_ == 0)
{
v___x_6206_ = v___x_6203_;
goto v_reusejp_6205_;
}
else
{
lean_object* v_reuseFailAlloc_6207_; 
v_reuseFailAlloc_6207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6207_, 0, v_val_6201_);
v___x_6206_ = v_reuseFailAlloc_6207_;
goto v_reusejp_6205_;
}
v_reusejp_6205_:
{
v___y_6090_ = v___y_6174_;
v___y_6091_ = v___y_6175_;
v___y_6092_ = v___y_6176_;
v___y_6093_ = v___y_6177_;
v___y_6094_ = v___x_6192_;
v___y_6095_ = v___y_6190_;
v___y_6096_ = v___y_6183_;
v___y_6097_ = v___x_6198_;
v___y_6098_ = v___y_6191_;
v___y_6099_ = v___y_6186_;
v___y_6100_ = v___y_6187_;
v___y_6101_ = v_patType_x3f_6184_;
v___y_6102_ = v___y_6181_;
v___y_6103_ = v___y_6185_;
v___y_6104_ = v___y_6189_;
v___y_6105_ = v___y_6188_;
v___y_6106_ = v___x_6206_;
goto v___jp_6089_;
}
}
}
}
}
else
{
lean_dec(v___x_6194_);
lean_inc_n(v___y_6179_, 2);
v___y_6055_ = v___y_6191_;
v___y_6056_ = v___y_6174_;
v___y_6057_ = v___y_6188_;
v___y_6058_ = v___y_6183_;
v___y_6059_ = v___y_6181_;
v___y_6060_ = v___y_6187_;
v___y_6061_ = v___y_6185_;
v___y_6062_ = v___y_6177_;
v___y_6063_ = v___y_6175_;
v___y_6064_ = v_patType_x3f_6184_;
v___y_6065_ = v___x_6192_;
v___y_6066_ = v___y_6189_;
v___y_6067_ = v___y_6190_;
v___y_6068_ = v___y_6186_;
v___y_6069_ = v___y_6179_;
v___y_6070_ = v___y_6176_;
v___y_6071_ = v___y_6179_;
goto v___jp_6054_;
}
}
v___jp_6209_:
{
lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; 
v___x_6223_ = l_Lean_Syntax_getArg(v___y_6210_, v___y_6212_);
lean_dec(v___y_6210_);
v___x_6224_ = lean_mk_empty_array_with_capacity(v___x_6109_);
lean_inc(v___y_6211_);
v___x_6225_ = lean_array_push(v___x_6224_, v___y_6211_);
v___x_6226_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_6225_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
lean_dec_ref(v___x_6225_);
if (lean_obj_tag(v___x_6226_) == 0)
{
lean_object* v___x_6227_; 
lean_dec_ref_known(v___x_6226_, 1);
v___x_6227_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_5984_, v_tk_6108_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
lean_dec(v_tk_6108_);
if (lean_obj_tag(v___x_6227_) == 0)
{
lean_object* v_a_6228_; uint8_t v_kind_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; 
v_a_6228_ = lean_ctor_get(v___x_6227_, 0);
lean_inc(v_a_6228_);
lean_dec_ref_known(v___x_6227_, 1);
v_kind_6229_ = lean_ctor_get_uint8(v_a_6228_, sizeof(void*)*3);
v___x_6230_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6230_, 0, v_a_6228_);
v___x_6231_ = lean_box(v___y_6213_);
lean_inc(v___y_6211_);
v___x_6232_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 13, 5);
lean_closure_set(v___x_6232_, 0, lean_box(0));
lean_closure_set(v___x_6232_, 1, v___y_6214_);
lean_closure_set(v___x_6232_, 2, v___y_6211_);
lean_closure_set(v___x_6232_, 3, v___x_6231_);
lean_closure_set(v___x_6232_, 4, v___x_6230_);
v___x_6233_ = l_Lean_Elab_Do_elabDoIdDecl(v___y_6211_, v_xType_x3f_6215_, v___x_6223_, v___x_6232_, v_kind_6229_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
return v___x_6233_;
}
else
{
lean_object* v_a_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6241_; 
lean_dec(v___x_6223_);
lean_dec(v_xType_x3f_6215_);
lean_dec(v___y_6214_);
lean_dec(v___y_6211_);
v_a_6234_ = lean_ctor_get(v___x_6227_, 0);
v_isSharedCheck_6241_ = !lean_is_exclusive(v___x_6227_);
if (v_isSharedCheck_6241_ == 0)
{
v___x_6236_ = v___x_6227_;
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_a_6234_);
lean_dec(v___x_6227_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6239_; 
if (v_isShared_6237_ == 0)
{
v___x_6239_ = v___x_6236_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6240_; 
v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
v___x_6239_ = v_reuseFailAlloc_6240_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
return v___x_6239_;
}
}
}
}
else
{
lean_object* v_a_6242_; lean_object* v___x_6244_; uint8_t v_isShared_6245_; uint8_t v_isSharedCheck_6249_; 
lean_dec(v___x_6223_);
lean_dec(v_xType_x3f_6215_);
lean_dec(v___y_6214_);
lean_dec(v___y_6211_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v_a_6242_ = lean_ctor_get(v___x_6226_, 0);
v_isSharedCheck_6249_ = !lean_is_exclusive(v___x_6226_);
if (v_isSharedCheck_6249_ == 0)
{
v___x_6244_ = v___x_6226_;
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
else
{
lean_inc(v_a_6242_);
lean_dec(v___x_6226_);
v___x_6244_ = lean_box(0);
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
v_resetjp_6243_:
{
lean_object* v___x_6247_; 
if (v_isShared_6245_ == 0)
{
v___x_6247_ = v___x_6244_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6248_; 
v_reuseFailAlloc_6248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6248_, 0, v_a_6242_);
v___x_6247_ = v_reuseFailAlloc_6248_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
return v___x_6247_;
}
}
}
}
v___jp_6250_:
{
uint8_t v___x_6268_; 
lean_inc(v___y_6254_);
v___x_6268_ = l_Lean_Syntax_isOfKind(v___y_6254_, v___y_6255_);
if (v___x_6268_ == 0)
{
uint8_t v___x_6269_; 
lean_dec(v___y_6260_);
lean_inc(v___y_6254_);
v___x_6269_ = l_Lean_Syntax_isOfKind(v___y_6254_, v___y_6253_);
if (v___x_6269_ == 0)
{
lean_object* v___x_6270_; 
lean_dec(v___y_6254_);
lean_dec(v___y_6252_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v___x_6270_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6270_;
}
else
{
lean_object* v___x_6271_; lean_object* v___x_6272_; uint8_t v___x_6273_; 
v___x_6271_ = l_Lean_Syntax_getArg(v___y_6254_, v___x_5999_);
v___x_6272_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
lean_inc(v___x_6271_);
v___x_6273_ = l_Lean_Syntax_isOfKind(v___x_6271_, v___x_6272_);
if (v___x_6273_ == 0)
{
lean_object* v___x_6274_; uint8_t v___x_6275_; 
lean_dec(v_tk_6108_);
v___x_6274_ = l_Lean_Syntax_getArg(v___y_6254_, v___x_6109_);
v___x_6275_ = l_Lean_Syntax_isNone(v___x_6274_);
if (v___x_6275_ == 0)
{
uint8_t v___x_6276_; 
lean_inc(v___x_6274_);
v___x_6276_ = l_Lean_Syntax_matchesNull(v___x_6274_, v___x_6109_);
if (v___x_6276_ == 0)
{
lean_object* v___x_6277_; 
lean_dec(v___x_6274_);
lean_dec(v___x_6271_);
lean_dec(v___y_6254_);
lean_dec(v___y_6252_);
lean_dec_ref(v_dec_5984_);
v___x_6277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6277_;
}
else
{
lean_object* v___x_6278_; lean_object* v___x_6279_; uint8_t v___x_6280_; 
v___x_6278_ = l_Lean_Syntax_getArg(v___x_6274_, v___x_5999_);
lean_dec(v___x_6274_);
v___x_6279_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6278_);
v___x_6280_ = l_Lean_Syntax_isOfKind(v___x_6278_, v___x_6279_);
if (v___x_6280_ == 0)
{
lean_object* v___x_6281_; 
lean_dec(v___x_6278_);
lean_dec(v___x_6271_);
lean_dec(v___y_6254_);
lean_dec(v___y_6252_);
lean_dec_ref(v_dec_5984_);
v___x_6281_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6281_;
}
else
{
lean_object* v___x_6282_; lean_object* v___x_6283_; 
v___x_6282_ = l_Lean_Syntax_getArg(v___x_6278_, v___x_6109_);
lean_dec(v___x_6278_);
v___x_6283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6283_, 0, v___x_6282_);
lean_inc(v___x_6271_);
v___y_6174_ = v___y_6251_;
v___y_6175_ = v___x_6273_;
v___y_6176_ = v___y_6252_;
v___y_6177_ = v___x_6271_;
v___y_6178_ = v___y_6254_;
v___y_6179_ = v___y_6257_;
v___y_6180_ = v___y_6256_;
v___y_6181_ = v___y_6258_;
v___y_6182_ = v___y_6259_;
v___y_6183_ = v___x_6271_;
v_patType_x3f_6184_ = v___x_6283_;
v___y_6185_ = v___y_6261_;
v___y_6186_ = v___y_6262_;
v___y_6187_ = v___y_6263_;
v___y_6188_ = v___y_6264_;
v___y_6189_ = v___y_6265_;
v___y_6190_ = v___y_6266_;
v___y_6191_ = v___y_6267_;
goto v___jp_6173_;
}
}
}
else
{
lean_dec(v___x_6274_);
lean_inc(v___y_6257_);
lean_inc(v___x_6271_);
v___y_6174_ = v___y_6251_;
v___y_6175_ = v___x_6273_;
v___y_6176_ = v___y_6252_;
v___y_6177_ = v___x_6271_;
v___y_6178_ = v___y_6254_;
v___y_6179_ = v___y_6257_;
v___y_6180_ = v___y_6256_;
v___y_6181_ = v___y_6258_;
v___y_6182_ = v___y_6259_;
v___y_6183_ = v___x_6271_;
v_patType_x3f_6184_ = v___y_6257_;
v___y_6185_ = v___y_6261_;
v___y_6186_ = v___y_6262_;
v___y_6187_ = v___y_6263_;
v___y_6188_ = v___y_6264_;
v___y_6189_ = v___y_6265_;
v___y_6190_ = v___y_6266_;
v___y_6191_ = v___y_6267_;
goto v___jp_6173_;
}
}
else
{
lean_object* v___x_6284_; lean_object* v___x_6285_; uint8_t v___x_6286_; 
v___x_6284_ = l_Lean_Syntax_getArg(v___x_6271_, v___x_5999_);
v___x_6285_ = l_Lean_Syntax_getArg(v___y_6254_, v___x_6109_);
v___x_6286_ = l_Lean_Syntax_isNone(v___x_6285_);
if (v___x_6286_ == 0)
{
uint8_t v___x_6287_; 
lean_inc(v___x_6285_);
v___x_6287_ = l_Lean_Syntax_matchesNull(v___x_6285_, v___x_6109_);
if (v___x_6287_ == 0)
{
lean_object* v___x_6288_; 
lean_dec(v___x_6285_);
lean_dec(v___x_6284_);
lean_dec(v___x_6271_);
lean_dec(v___y_6254_);
lean_dec(v___y_6252_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v___x_6288_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6288_;
}
else
{
lean_object* v___x_6289_; lean_object* v___x_6290_; uint8_t v___x_6291_; 
v___x_6289_ = l_Lean_Syntax_getArg(v___x_6285_, v___x_5999_);
lean_dec(v___x_6285_);
v___x_6290_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6289_);
v___x_6291_ = l_Lean_Syntax_isOfKind(v___x_6289_, v___x_6290_);
if (v___x_6291_ == 0)
{
lean_object* v___x_6292_; 
lean_dec(v___x_6289_);
lean_dec(v___x_6284_);
lean_dec(v___x_6271_);
lean_dec(v___y_6254_);
lean_dec(v___y_6252_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v___x_6292_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6292_;
}
else
{
lean_object* v___x_6293_; lean_object* v___x_6294_; 
v___x_6293_ = l_Lean_Syntax_getArg(v___x_6289_, v___x_6109_);
lean_dec(v___x_6289_);
v___x_6294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6294_, 0, v___x_6293_);
lean_inc(v___x_6271_);
v___y_6111_ = v___x_6268_;
v___y_6112_ = v___y_6251_;
v___y_6113_ = v___y_6252_;
v___y_6114_ = v___x_6271_;
v___y_6115_ = v___y_6254_;
v___y_6116_ = v___y_6257_;
v___y_6117_ = v___y_6256_;
v___y_6118_ = v___y_6258_;
v___y_6119_ = v___y_6259_;
v___y_6120_ = v___x_6284_;
v___y_6121_ = v___x_6271_;
v_patType_x3f_6122_ = v___x_6294_;
v___y_6123_ = v___y_6261_;
v___y_6124_ = v___y_6262_;
v___y_6125_ = v___y_6263_;
v___y_6126_ = v___y_6264_;
v___y_6127_ = v___y_6265_;
v___y_6128_ = v___y_6266_;
v___y_6129_ = v___y_6267_;
goto v___jp_6110_;
}
}
}
else
{
lean_dec(v___x_6285_);
lean_inc(v___y_6257_);
lean_inc(v___x_6271_);
v___y_6111_ = v___x_6268_;
v___y_6112_ = v___y_6251_;
v___y_6113_ = v___y_6252_;
v___y_6114_ = v___x_6271_;
v___y_6115_ = v___y_6254_;
v___y_6116_ = v___y_6257_;
v___y_6117_ = v___y_6256_;
v___y_6118_ = v___y_6258_;
v___y_6119_ = v___y_6259_;
v___y_6120_ = v___x_6284_;
v___y_6121_ = v___x_6271_;
v_patType_x3f_6122_ = v___y_6257_;
v___y_6123_ = v___y_6261_;
v___y_6124_ = v___y_6262_;
v___y_6125_ = v___y_6263_;
v___y_6126_ = v___y_6264_;
v___y_6127_ = v___y_6265_;
v___y_6128_ = v___y_6266_;
v___y_6129_ = v___y_6267_;
goto v___jp_6110_;
}
}
}
}
else
{
lean_object* v___x_6295_; lean_object* v___x_6296_; uint8_t v___x_6297_; 
lean_dec(v___y_6252_);
v___x_6295_ = l_Lean_Syntax_getArg(v___y_6254_, v___x_5999_);
v___x_6296_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_6295_);
v___x_6297_ = l_Lean_Syntax_isOfKind(v___x_6295_, v___x_6296_);
if (v___x_6297_ == 0)
{
lean_object* v___x_6298_; 
lean_dec(v___x_6295_);
lean_dec(v___y_6260_);
lean_dec(v___y_6254_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v___x_6298_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6298_;
}
else
{
lean_object* v___x_6299_; uint8_t v___x_6300_; 
v___x_6299_ = l_Lean_Syntax_getArg(v___y_6254_, v___x_6109_);
v___x_6300_ = l_Lean_Syntax_isNone(v___x_6299_);
if (v___x_6300_ == 0)
{
uint8_t v___x_6301_; 
lean_inc(v___x_6299_);
v___x_6301_ = l_Lean_Syntax_matchesNull(v___x_6299_, v___x_6109_);
if (v___x_6301_ == 0)
{
lean_object* v___x_6302_; 
lean_dec(v___x_6299_);
lean_dec(v___x_6295_);
lean_dec(v___y_6260_);
lean_dec(v___y_6254_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v___x_6302_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6302_;
}
else
{
lean_object* v___x_6303_; lean_object* v___x_6304_; uint8_t v___x_6305_; 
v___x_6303_ = l_Lean_Syntax_getArg(v___x_6299_, v___x_5999_);
lean_dec(v___x_6299_);
v___x_6304_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6303_);
v___x_6305_ = l_Lean_Syntax_isOfKind(v___x_6303_, v___x_6304_);
if (v___x_6305_ == 0)
{
lean_object* v___x_6306_; 
lean_dec(v___x_6303_);
lean_dec(v___x_6295_);
lean_dec(v___y_6260_);
lean_dec(v___y_6254_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v___x_6306_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6306_;
}
else
{
lean_object* v___x_6307_; lean_object* v___x_6308_; 
v___x_6307_ = l_Lean_Syntax_getArg(v___x_6303_, v___x_6109_);
lean_dec(v___x_6303_);
v___x_6308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6308_, 0, v___x_6307_);
v___y_6210_ = v___y_6254_;
v___y_6211_ = v___x_6295_;
v___y_6212_ = v___y_6256_;
v___y_6213_ = v___y_6258_;
v___y_6214_ = v___y_6260_;
v_xType_x3f_6215_ = v___x_6308_;
v___y_6216_ = v___y_6261_;
v___y_6217_ = v___y_6262_;
v___y_6218_ = v___y_6263_;
v___y_6219_ = v___y_6264_;
v___y_6220_ = v___y_6265_;
v___y_6221_ = v___y_6266_;
v___y_6222_ = v___y_6267_;
goto v___jp_6209_;
}
}
}
else
{
lean_dec(v___x_6299_);
lean_inc(v___y_6257_);
v___y_6210_ = v___y_6254_;
v___y_6211_ = v___x_6295_;
v___y_6212_ = v___y_6256_;
v___y_6213_ = v___y_6258_;
v___y_6214_ = v___y_6260_;
v_xType_x3f_6215_ = v___y_6257_;
v___y_6216_ = v___y_6261_;
v___y_6217_ = v___y_6262_;
v___y_6218_ = v___y_6263_;
v___y_6219_ = v___y_6264_;
v___y_6220_ = v___y_6265_;
v___y_6221_ = v___y_6266_;
v___y_6222_ = v___y_6267_;
goto v___jp_6209_;
}
}
}
}
v___jp_6309_:
{
lean_object* v___x_6328_; lean_object* v___x_6329_; lean_object* v_a_6330_; lean_object* v___x_6332_; uint8_t v_isShared_6333_; uint8_t v_isSharedCheck_6337_; 
lean_dec(v___y_6327_);
lean_dec(v___y_6313_);
lean_dec(v___y_6311_);
v___x_6328_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__1, &l_Lean_Elab_Do_elabDoLetArrow___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1);
v___x_6329_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v___y_6318_, v___x_6328_, v___y_6321_, v___y_6314_, v___y_6320_, v___y_6319_, v___y_6315_, v___y_6317_, v___y_6316_);
lean_dec(v___y_6318_);
v_a_6330_ = lean_ctor_get(v___x_6329_, 0);
v_isSharedCheck_6337_ = !lean_is_exclusive(v___x_6329_);
if (v_isSharedCheck_6337_ == 0)
{
v___x_6332_ = v___x_6329_;
v_isShared_6333_ = v_isSharedCheck_6337_;
goto v_resetjp_6331_;
}
else
{
lean_inc(v_a_6330_);
lean_dec(v___x_6329_);
v___x_6332_ = lean_box(0);
v_isShared_6333_ = v_isSharedCheck_6337_;
goto v_resetjp_6331_;
}
v_resetjp_6331_:
{
lean_object* v___x_6335_; 
if (v_isShared_6333_ == 0)
{
v___x_6335_ = v___x_6332_;
goto v_reusejp_6334_;
}
else
{
lean_object* v_reuseFailAlloc_6336_; 
v_reuseFailAlloc_6336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6336_, 0, v_a_6330_);
v___x_6335_ = v_reuseFailAlloc_6336_;
goto v_reusejp_6334_;
}
v_reusejp_6334_:
{
return v___x_6335_;
}
}
}
v___jp_6338_:
{
lean_object* v___x_6347_; lean_object* v_cfg_6348_; lean_object* v___x_6349_; uint8_t v___x_6350_; 
v___x_6347_ = lean_unsigned_to_nat(2u);
v_cfg_6348_ = l_Lean_Syntax_getArg(v_stx_5983_, v___x_6347_);
v___x_6349_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_6348_);
v___x_6350_ = l_Lean_Syntax_isOfKind(v_cfg_6348_, v___x_6349_);
if (v___x_6350_ == 0)
{
lean_object* v___x_6351_; 
lean_dec(v_cfg_6348_);
lean_dec(v_mutTk_x3f_6339_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
lean_dec(v_stx_5983_);
v___x_6351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6351_;
}
else
{
lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; uint8_t v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; 
v___x_6352_ = lean_unsigned_to_nat(3u);
v___x_6353_ = l_Lean_Syntax_getArg(v_stx_5983_, v___x_6352_);
lean_dec(v_stx_5983_);
v___x_6354_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
v___x_6355_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
v___x_6356_ = 0;
v___x_6357_ = lean_box(0);
v___x_6358_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
lean_inc(v_cfg_6348_);
v___x_6359_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_cfg_6348_, v_mutTk_x3f_6339_, v___x_6358_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_);
if (lean_obj_tag(v___x_6359_) == 0)
{
lean_object* v_a_6360_; lean_object* v___x_6361_; 
v_a_6360_ = lean_ctor_get(v___x_6359_, 0);
lean_inc(v_a_6360_);
lean_dec_ref_known(v___x_6359_, 1);
v___x_6361_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_6360_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_);
if (lean_obj_tag(v___x_6361_) == 0)
{
uint8_t v_nondep_6362_; 
lean_dec_ref_known(v___x_6361_, 1);
v_nondep_6362_ = lean_ctor_get_uint8(v_a_6360_, sizeof(void*)*1);
if (v_nondep_6362_ == 0)
{
uint8_t v_usedOnly_6363_; 
v_usedOnly_6363_ = lean_ctor_get_uint8(v_a_6360_, sizeof(void*)*1 + 1);
if (v_usedOnly_6363_ == 0)
{
uint8_t v_zeta_6364_; 
v_zeta_6364_ = lean_ctor_get_uint8(v_a_6360_, sizeof(void*)*1 + 2);
if (v_zeta_6364_ == 0)
{
lean_object* v_eq_x3f_6365_; 
v_eq_x3f_6365_ = lean_ctor_get(v_a_6360_, 0);
lean_inc(v_eq_x3f_6365_);
lean_dec(v_a_6360_);
if (lean_obj_tag(v_eq_x3f_6365_) == 0)
{
lean_dec(v_cfg_6348_);
lean_inc(v_mutTk_x3f_6339_);
v___y_6251_ = v___x_6349_;
v___y_6252_ = v_mutTk_x3f_6339_;
v___y_6253_ = v___x_6355_;
v___y_6254_ = v___x_6353_;
v___y_6255_ = v___x_6354_;
v___y_6256_ = v___x_6352_;
v___y_6257_ = v___x_6357_;
v___y_6258_ = v___x_6356_;
v___y_6259_ = v___x_6347_;
v___y_6260_ = v_mutTk_x3f_6339_;
v___y_6261_ = v___y_6340_;
v___y_6262_ = v___y_6341_;
v___y_6263_ = v___y_6342_;
v___y_6264_ = v___y_6343_;
v___y_6265_ = v___y_6344_;
v___y_6266_ = v___y_6345_;
v___y_6267_ = v___y_6346_;
goto v___jp_6250_;
}
else
{
lean_dec_ref_known(v_eq_x3f_6365_, 1);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
lean_inc(v_mutTk_x3f_6339_);
v___y_6310_ = v___x_6349_;
v___y_6311_ = v_mutTk_x3f_6339_;
v___y_6312_ = v___x_6355_;
v___y_6313_ = v___x_6353_;
v___y_6314_ = v___y_6341_;
v___y_6315_ = v___y_6344_;
v___y_6316_ = v___y_6346_;
v___y_6317_ = v___y_6345_;
v___y_6318_ = v_cfg_6348_;
v___y_6319_ = v___y_6343_;
v___y_6320_ = v___y_6342_;
v___y_6321_ = v___y_6340_;
v___y_6322_ = v___x_6354_;
v___y_6323_ = v___x_6357_;
v___y_6324_ = v___x_6352_;
v___y_6325_ = v___x_6356_;
v___y_6326_ = v___x_6347_;
v___y_6327_ = v_mutTk_x3f_6339_;
goto v___jp_6309_;
}
}
else
{
lean_dec(v_a_6360_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
lean_inc(v_mutTk_x3f_6339_);
v___y_6310_ = v___x_6349_;
v___y_6311_ = v_mutTk_x3f_6339_;
v___y_6312_ = v___x_6355_;
v___y_6313_ = v___x_6353_;
v___y_6314_ = v___y_6341_;
v___y_6315_ = v___y_6344_;
v___y_6316_ = v___y_6346_;
v___y_6317_ = v___y_6345_;
v___y_6318_ = v_cfg_6348_;
v___y_6319_ = v___y_6343_;
v___y_6320_ = v___y_6342_;
v___y_6321_ = v___y_6340_;
v___y_6322_ = v___x_6354_;
v___y_6323_ = v___x_6357_;
v___y_6324_ = v___x_6352_;
v___y_6325_ = v___x_6356_;
v___y_6326_ = v___x_6347_;
v___y_6327_ = v_mutTk_x3f_6339_;
goto v___jp_6309_;
}
}
else
{
lean_dec(v_a_6360_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
lean_inc(v_mutTk_x3f_6339_);
v___y_6310_ = v___x_6349_;
v___y_6311_ = v_mutTk_x3f_6339_;
v___y_6312_ = v___x_6355_;
v___y_6313_ = v___x_6353_;
v___y_6314_ = v___y_6341_;
v___y_6315_ = v___y_6344_;
v___y_6316_ = v___y_6346_;
v___y_6317_ = v___y_6345_;
v___y_6318_ = v_cfg_6348_;
v___y_6319_ = v___y_6343_;
v___y_6320_ = v___y_6342_;
v___y_6321_ = v___y_6340_;
v___y_6322_ = v___x_6354_;
v___y_6323_ = v___x_6357_;
v___y_6324_ = v___x_6352_;
v___y_6325_ = v___x_6356_;
v___y_6326_ = v___x_6347_;
v___y_6327_ = v_mutTk_x3f_6339_;
goto v___jp_6309_;
}
}
else
{
lean_dec(v_a_6360_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
lean_inc(v_mutTk_x3f_6339_);
v___y_6310_ = v___x_6349_;
v___y_6311_ = v_mutTk_x3f_6339_;
v___y_6312_ = v___x_6355_;
v___y_6313_ = v___x_6353_;
v___y_6314_ = v___y_6341_;
v___y_6315_ = v___y_6344_;
v___y_6316_ = v___y_6346_;
v___y_6317_ = v___y_6345_;
v___y_6318_ = v_cfg_6348_;
v___y_6319_ = v___y_6343_;
v___y_6320_ = v___y_6342_;
v___y_6321_ = v___y_6340_;
v___y_6322_ = v___x_6354_;
v___y_6323_ = v___x_6357_;
v___y_6324_ = v___x_6352_;
v___y_6325_ = v___x_6356_;
v___y_6326_ = v___x_6347_;
v___y_6327_ = v_mutTk_x3f_6339_;
goto v___jp_6309_;
}
}
else
{
lean_object* v_a_6366_; lean_object* v___x_6368_; uint8_t v_isShared_6369_; uint8_t v_isSharedCheck_6373_; 
lean_dec(v_a_6360_);
lean_dec(v___x_6353_);
lean_dec(v_cfg_6348_);
lean_dec(v_mutTk_x3f_6339_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v_a_6366_ = lean_ctor_get(v___x_6361_, 0);
v_isSharedCheck_6373_ = !lean_is_exclusive(v___x_6361_);
if (v_isSharedCheck_6373_ == 0)
{
v___x_6368_ = v___x_6361_;
v_isShared_6369_ = v_isSharedCheck_6373_;
goto v_resetjp_6367_;
}
else
{
lean_inc(v_a_6366_);
lean_dec(v___x_6361_);
v___x_6368_ = lean_box(0);
v_isShared_6369_ = v_isSharedCheck_6373_;
goto v_resetjp_6367_;
}
v_resetjp_6367_:
{
lean_object* v___x_6371_; 
if (v_isShared_6369_ == 0)
{
v___x_6371_ = v___x_6368_;
goto v_reusejp_6370_;
}
else
{
lean_object* v_reuseFailAlloc_6372_; 
v_reuseFailAlloc_6372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_a_6366_);
v___x_6371_ = v_reuseFailAlloc_6372_;
goto v_reusejp_6370_;
}
v_reusejp_6370_:
{
return v___x_6371_;
}
}
}
}
else
{
lean_object* v_a_6374_; lean_object* v___x_6376_; uint8_t v_isShared_6377_; uint8_t v_isSharedCheck_6381_; 
lean_dec(v___x_6353_);
lean_dec(v_cfg_6348_);
lean_dec(v_mutTk_x3f_6339_);
lean_dec(v_tk_6108_);
lean_dec_ref(v_dec_5984_);
v_a_6374_ = lean_ctor_get(v___x_6359_, 0);
v_isSharedCheck_6381_ = !lean_is_exclusive(v___x_6359_);
if (v_isSharedCheck_6381_ == 0)
{
v___x_6376_ = v___x_6359_;
v_isShared_6377_ = v_isSharedCheck_6381_;
goto v_resetjp_6375_;
}
else
{
lean_inc(v_a_6374_);
lean_dec(v___x_6359_);
v___x_6376_ = lean_box(0);
v_isShared_6377_ = v_isSharedCheck_6381_;
goto v_resetjp_6375_;
}
v_resetjp_6375_:
{
lean_object* v___x_6379_; 
if (v_isShared_6377_ == 0)
{
v___x_6379_ = v___x_6376_;
goto v_reusejp_6378_;
}
else
{
lean_object* v_reuseFailAlloc_6380_; 
v_reuseFailAlloc_6380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6380_, 0, v_a_6374_);
v___x_6379_ = v_reuseFailAlloc_6380_;
goto v_reusejp_6378_;
}
v_reusejp_6378_:
{
return v___x_6379_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_6389_, lean_object* v_dec_6390_, lean_object* v_a_6391_, lean_object* v_a_6392_, lean_object* v_a_6393_, lean_object* v_a_6394_, lean_object* v_a_6395_, lean_object* v_a_6396_, lean_object* v_a_6397_, lean_object* v_a_6398_){
_start:
{
lean_object* v_res_6399_; 
v_res_6399_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_6389_, v_dec_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_, v_a_6395_, v_a_6396_, v_a_6397_);
lean_dec(v_a_6397_);
lean_dec_ref(v_a_6396_);
lean_dec(v_a_6395_);
lean_dec_ref(v_a_6394_);
lean_dec(v_a_6393_);
lean_dec_ref(v_a_6392_);
lean_dec_ref(v_a_6391_);
return v_res_6399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; 
v___x_6407_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6408_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_6409_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_6410_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_6411_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6407_, v___x_6408_, v___x_6409_, v___x_6410_);
return v___x_6411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_6412_){
_start:
{
lean_object* v_res_6413_; 
v_res_6413_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_6413_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3(void){
_start:
{
lean_object* v___x_6421_; lean_object* v___x_6422_; 
v___x_6421_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__2));
v___x_6422_ = l_Lean_stringToMessageData(v___x_6421_);
return v___x_6422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_6423_, lean_object* v_dec_6424_, lean_object* v_a_6425_, lean_object* v_a_6426_, lean_object* v_a_6427_, lean_object* v_a_6428_, lean_object* v_a_6429_, lean_object* v_a_6430_, lean_object* v_a_6431_){
_start:
{
lean_object* v___x_6433_; uint8_t v___x_6434_; 
v___x_6433_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_6423_);
v___x_6434_ = l_Lean_Syntax_isOfKind(v_stx_6423_, v___x_6433_);
if (v___x_6434_ == 0)
{
lean_object* v___x_6435_; 
lean_dec_ref(v_dec_6424_);
lean_dec(v_stx_6423_);
v___x_6435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6435_;
}
else
{
lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; uint8_t v___x_6439_; 
v___x_6436_ = lean_unsigned_to_nat(0u);
v___x_6437_ = l_Lean_Syntax_getArg(v_stx_6423_, v___x_6436_);
lean_dec(v_stx_6423_);
v___x_6438_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_6437_);
v___x_6439_ = l_Lean_Syntax_isOfKind(v___x_6437_, v___x_6438_);
if (v___x_6439_ == 0)
{
lean_object* v___x_6440_; uint8_t v___x_6441_; 
v___x_6440_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
lean_inc(v___x_6437_);
v___x_6441_ = l_Lean_Syntax_isOfKind(v___x_6437_, v___x_6440_);
if (v___x_6441_ == 0)
{
lean_object* v___x_6442_; 
lean_dec(v___x_6437_);
lean_dec_ref(v_dec_6424_);
v___x_6442_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6442_;
}
else
{
lean_object* v___x_6443_; lean_object* v___y_6445_; lean_object* v___y_6446_; lean_object* v___y_6447_; lean_object* v___y_6448_; lean_object* v___y_6449_; lean_object* v___y_6450_; lean_object* v___y_6451_; lean_object* v___y_6452_; lean_object* v___y_6453_; lean_object* v_t_x3f_6482_; lean_object* v___y_6483_; lean_object* v___y_6484_; lean_object* v___y_6485_; lean_object* v___y_6486_; lean_object* v___y_6487_; lean_object* v___y_6488_; lean_object* v___y_6489_; lean_object* v___x_6507_; lean_object* v___x_6508_; uint8_t v___x_6509_; 
v___x_6443_ = l_Lean_Syntax_getArg(v___x_6437_, v___x_6436_);
v___x_6507_ = lean_unsigned_to_nat(1u);
v___x_6508_ = l_Lean_Syntax_getArg(v___x_6437_, v___x_6507_);
v___x_6509_ = l_Lean_Syntax_isNone(v___x_6508_);
if (v___x_6509_ == 0)
{
uint8_t v___x_6510_; 
lean_inc(v___x_6508_);
v___x_6510_ = l_Lean_Syntax_matchesNull(v___x_6508_, v___x_6507_);
if (v___x_6510_ == 0)
{
lean_object* v___x_6511_; 
lean_dec(v___x_6508_);
lean_dec(v___x_6443_);
lean_dec(v___x_6437_);
lean_dec_ref(v_dec_6424_);
v___x_6511_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6511_;
}
else
{
lean_object* v___x_6512_; lean_object* v___x_6513_; uint8_t v___x_6514_; 
v___x_6512_ = l_Lean_Syntax_getArg(v___x_6508_, v___x_6436_);
lean_dec(v___x_6508_);
v___x_6513_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6512_);
v___x_6514_ = l_Lean_Syntax_isOfKind(v___x_6512_, v___x_6513_);
if (v___x_6514_ == 0)
{
lean_object* v___x_6515_; 
lean_dec(v___x_6512_);
lean_dec(v___x_6443_);
lean_dec(v___x_6437_);
lean_dec_ref(v_dec_6424_);
v___x_6515_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6515_;
}
else
{
lean_object* v_t_x3f_6516_; lean_object* v___x_6517_; 
v_t_x3f_6516_ = l_Lean_Syntax_getArg(v___x_6512_, v___x_6507_);
lean_dec(v___x_6512_);
v___x_6517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6517_, 0, v_t_x3f_6516_);
v_t_x3f_6482_ = v___x_6517_;
v___y_6483_ = v_a_6425_;
v___y_6484_ = v_a_6426_;
v___y_6485_ = v_a_6427_;
v___y_6486_ = v_a_6428_;
v___y_6487_ = v_a_6429_;
v___y_6488_ = v_a_6430_;
v___y_6489_ = v_a_6431_;
goto v___jp_6481_;
}
}
}
else
{
lean_object* v___x_6518_; 
lean_dec(v___x_6508_);
v___x_6518_ = lean_box(0);
v_t_x3f_6482_ = v___x_6518_;
v___y_6483_ = v_a_6425_;
v___y_6484_ = v_a_6426_;
v___y_6485_ = v_a_6427_;
v___y_6486_ = v_a_6428_;
v___y_6487_ = v_a_6429_;
v___y_6488_ = v_a_6430_;
v___y_6489_ = v_a_6431_;
goto v___jp_6481_;
}
v___jp_6444_:
{
lean_object* v___x_6454_; lean_object* v___x_6455_; 
v___x_6454_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6455_ = l_Lean_Core_mkFreshUserName(v___x_6454_, v___y_6452_, v___y_6453_);
if (lean_obj_tag(v___x_6455_) == 0)
{
lean_object* v_a_6456_; lean_object* v_ref_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; lean_object* v___x_6466_; lean_object* v___x_6467_; uint8_t v_kind_6468_; lean_object* v___x_6469_; lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; 
v_a_6456_ = lean_ctor_get(v___x_6455_, 0);
lean_inc(v_a_6456_);
lean_dec_ref_known(v___x_6455_, 1);
v_ref_6457_ = lean_ctor_get(v___y_6452_, 2);
v___x_6458_ = l_Lean_mkIdentFrom(v___x_6443_, v_a_6456_, v___x_6439_);
v___x_6459_ = l_Lean_SourceInfo_fromRef(v_ref_6457_, v___x_6439_);
v___x_6460_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6461_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
v___x_6462_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6463_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_6459_, 3);
v___x_6464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6464_, 0, v___x_6459_);
lean_ctor_set(v___x_6464_, 1, v___x_6462_);
lean_ctor_set(v___x_6464_, 2, v___x_6463_);
v___x_6465_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6466_, 0, v___x_6459_);
lean_ctor_set(v___x_6466_, 1, v___x_6465_);
lean_inc(v___x_6458_);
lean_inc_ref(v___x_6464_);
v___x_6467_ = l_Lean_Syntax_node5(v___x_6459_, v___x_6461_, v___x_6443_, v___x_6464_, v___x_6464_, v___x_6466_, v___x_6458_);
v_kind_6468_ = lean_ctor_get_uint8(v_dec_6424_, sizeof(void*)*3);
v___x_6469_ = l_Lean_Syntax_node1(v___x_6459_, v___x_6460_, v___x_6467_);
v___x_6470_ = lean_box(v___x_6434_);
v___x_6471_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6471_, 0, v___x_6469_);
lean_closure_set(v___x_6471_, 1, v_dec_6424_);
lean_closure_set(v___x_6471_, 2, v___x_6470_);
v___x_6472_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6458_, v___y_6446_, v___y_6445_, v___x_6471_, v_kind_6468_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_);
return v___x_6472_;
}
else
{
lean_object* v_a_6473_; lean_object* v___x_6475_; uint8_t v_isShared_6476_; uint8_t v_isSharedCheck_6480_; 
lean_dec(v___y_6446_);
lean_dec(v___y_6445_);
lean_dec(v___x_6443_);
lean_dec_ref(v_dec_6424_);
v_a_6473_ = lean_ctor_get(v___x_6455_, 0);
v_isSharedCheck_6480_ = !lean_is_exclusive(v___x_6455_);
if (v_isSharedCheck_6480_ == 0)
{
v___x_6475_ = v___x_6455_;
v_isShared_6476_ = v_isSharedCheck_6480_;
goto v_resetjp_6474_;
}
else
{
lean_inc(v_a_6473_);
lean_dec(v___x_6455_);
v___x_6475_ = lean_box(0);
v_isShared_6476_ = v_isSharedCheck_6480_;
goto v_resetjp_6474_;
}
v_resetjp_6474_:
{
lean_object* v___x_6478_; 
if (v_isShared_6476_ == 0)
{
v___x_6478_ = v___x_6475_;
goto v_reusejp_6477_;
}
else
{
lean_object* v_reuseFailAlloc_6479_; 
v_reuseFailAlloc_6479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_a_6473_);
v___x_6478_ = v_reuseFailAlloc_6479_;
goto v_reusejp_6477_;
}
v_reusejp_6477_:
{
return v___x_6478_;
}
}
}
}
v___jp_6481_:
{
lean_object* v___x_6490_; lean_object* v_rhs_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; uint8_t v___x_6494_; 
v___x_6490_ = lean_unsigned_to_nat(3u);
v_rhs_6491_ = l_Lean_Syntax_getArg(v___x_6437_, v___x_6490_);
v___x_6492_ = lean_unsigned_to_nat(4u);
v___x_6493_ = l_Lean_Syntax_getArg(v___x_6437_, v___x_6492_);
lean_dec(v___x_6437_);
v___x_6494_ = l_Lean_Syntax_isNone(v___x_6493_);
if (v___x_6494_ == 0)
{
uint8_t v___x_6495_; 
lean_dec(v_rhs_6491_);
lean_dec(v_t_x3f_6482_);
lean_dec(v___x_6443_);
lean_dec_ref(v_dec_6424_);
v___x_6495_ = l_Lean_Syntax_matchesNull(v___x_6493_, v___x_6490_);
if (v___x_6495_ == 0)
{
lean_object* v___x_6496_; 
v___x_6496_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6496_;
}
else
{
lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v_a_6499_; lean_object* v___x_6501_; uint8_t v_isShared_6502_; uint8_t v_isSharedCheck_6506_; 
v___x_6497_ = lean_obj_once(&l_Lean_Elab_Do_elabDoReassignArrow___closed__3, &l_Lean_Elab_Do_elabDoReassignArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3);
v___x_6498_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v___x_6497_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_);
v_a_6499_ = lean_ctor_get(v___x_6498_, 0);
v_isSharedCheck_6506_ = !lean_is_exclusive(v___x_6498_);
if (v_isSharedCheck_6506_ == 0)
{
v___x_6501_ = v___x_6498_;
v_isShared_6502_ = v_isSharedCheck_6506_;
goto v_resetjp_6500_;
}
else
{
lean_inc(v_a_6499_);
lean_dec(v___x_6498_);
v___x_6501_ = lean_box(0);
v_isShared_6502_ = v_isSharedCheck_6506_;
goto v_resetjp_6500_;
}
v_resetjp_6500_:
{
lean_object* v___x_6504_; 
if (v_isShared_6502_ == 0)
{
v___x_6504_ = v___x_6501_;
goto v_reusejp_6503_;
}
else
{
lean_object* v_reuseFailAlloc_6505_; 
v_reuseFailAlloc_6505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6505_, 0, v_a_6499_);
v___x_6504_ = v_reuseFailAlloc_6505_;
goto v_reusejp_6503_;
}
v_reusejp_6503_:
{
return v___x_6504_;
}
}
}
}
else
{
lean_dec(v___x_6493_);
v___y_6445_ = v_rhs_6491_;
v___y_6446_ = v_t_x3f_6482_;
v___y_6447_ = v___y_6483_;
v___y_6448_ = v___y_6484_;
v___y_6449_ = v___y_6485_;
v___y_6450_ = v___y_6486_;
v___y_6451_ = v___y_6487_;
v___y_6452_ = v___y_6488_;
v___y_6453_ = v___y_6489_;
goto v___jp_6444_;
}
}
}
}
else
{
lean_object* v_x_6519_; lean_object* v___y_6521_; lean_object* v_t_6522_; lean_object* v___y_6523_; lean_object* v___y_6524_; lean_object* v___y_6525_; lean_object* v___y_6526_; lean_object* v___y_6527_; lean_object* v___y_6528_; lean_object* v___y_6529_; lean_object* v_t_x3f_6562_; lean_object* v___y_6563_; lean_object* v___y_6564_; lean_object* v___y_6565_; lean_object* v___y_6566_; lean_object* v___y_6567_; lean_object* v___y_6568_; lean_object* v___y_6569_; lean_object* v___x_6604_; uint8_t v___x_6605_; 
v_x_6519_ = l_Lean_Syntax_getArg(v___x_6437_, v___x_6436_);
v___x_6604_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_6519_);
v___x_6605_ = l_Lean_Syntax_isOfKind(v_x_6519_, v___x_6604_);
if (v___x_6605_ == 0)
{
lean_object* v___x_6606_; 
lean_dec(v_x_6519_);
lean_dec(v___x_6437_);
lean_dec_ref(v_dec_6424_);
v___x_6606_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6606_;
}
else
{
lean_object* v___x_6607_; lean_object* v___x_6608_; uint8_t v___x_6609_; 
v___x_6607_ = lean_unsigned_to_nat(1u);
v___x_6608_ = l_Lean_Syntax_getArg(v___x_6437_, v___x_6607_);
v___x_6609_ = l_Lean_Syntax_isNone(v___x_6608_);
if (v___x_6609_ == 0)
{
uint8_t v___x_6610_; 
lean_inc(v___x_6608_);
v___x_6610_ = l_Lean_Syntax_matchesNull(v___x_6608_, v___x_6607_);
if (v___x_6610_ == 0)
{
lean_object* v___x_6611_; 
lean_dec(v___x_6608_);
lean_dec(v_x_6519_);
lean_dec(v___x_6437_);
lean_dec_ref(v_dec_6424_);
v___x_6611_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6611_;
}
else
{
lean_object* v___x_6612_; lean_object* v___x_6613_; uint8_t v___x_6614_; 
v___x_6612_ = l_Lean_Syntax_getArg(v___x_6608_, v___x_6436_);
lean_dec(v___x_6608_);
v___x_6613_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6612_);
v___x_6614_ = l_Lean_Syntax_isOfKind(v___x_6612_, v___x_6613_);
if (v___x_6614_ == 0)
{
lean_object* v___x_6615_; 
lean_dec(v___x_6612_);
lean_dec(v_x_6519_);
lean_dec(v___x_6437_);
lean_dec_ref(v_dec_6424_);
v___x_6615_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6615_;
}
else
{
lean_object* v_t_x3f_6616_; lean_object* v___x_6617_; 
v_t_x3f_6616_ = l_Lean_Syntax_getArg(v___x_6612_, v___x_6607_);
lean_dec(v___x_6612_);
v___x_6617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6617_, 0, v_t_x3f_6616_);
v_t_x3f_6562_ = v___x_6617_;
v___y_6563_ = v_a_6425_;
v___y_6564_ = v_a_6426_;
v___y_6565_ = v_a_6427_;
v___y_6566_ = v_a_6428_;
v___y_6567_ = v_a_6429_;
v___y_6568_ = v_a_6430_;
v___y_6569_ = v_a_6431_;
goto v___jp_6561_;
}
}
}
else
{
lean_object* v___x_6618_; 
lean_dec(v___x_6608_);
v___x_6618_ = lean_box(0);
v_t_x3f_6562_ = v___x_6618_;
v___y_6563_ = v_a_6425_;
v___y_6564_ = v_a_6426_;
v___y_6565_ = v_a_6427_;
v___y_6566_ = v_a_6428_;
v___y_6567_ = v_a_6429_;
v___y_6568_ = v_a_6430_;
v___y_6569_ = v_a_6431_;
goto v___jp_6561_;
}
}
v___jp_6520_:
{
lean_object* v___x_6530_; lean_object* v___x_6531_; 
v___x_6530_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6531_ = l_Lean_Core_mkFreshUserName(v___x_6530_, v___y_6528_, v___y_6529_);
if (lean_obj_tag(v___x_6531_) == 0)
{
lean_object* v_a_6532_; lean_object* v_ref_6533_; uint8_t v___x_6534_; lean_object* v___x_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; uint8_t v_kind_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; 
v_a_6532_ = lean_ctor_get(v___x_6531_, 0);
lean_inc(v_a_6532_);
lean_dec_ref_known(v___x_6531_, 1);
v_ref_6533_ = lean_ctor_get(v___y_6528_, 2);
v___x_6534_ = 0;
v___x_6535_ = l_Lean_mkIdentFrom(v_x_6519_, v_a_6532_, v___x_6534_);
v___x_6536_ = l_Lean_SourceInfo_fromRef(v_ref_6533_, v___x_6534_);
v___x_6537_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6538_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_6539_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v___x_6536_, 4);
v___x_6540_ = l_Lean_Syntax_node1(v___x_6536_, v___x_6539_, v_x_6519_);
v___x_6541_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6542_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_6543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6543_, 0, v___x_6536_);
lean_ctor_set(v___x_6543_, 1, v___x_6541_);
lean_ctor_set(v___x_6543_, 2, v___x_6542_);
v___x_6544_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6545_, 0, v___x_6536_);
lean_ctor_set(v___x_6545_, 1, v___x_6544_);
lean_inc(v___x_6535_);
lean_inc_ref(v___x_6543_);
v___x_6546_ = l_Lean_Syntax_node5(v___x_6536_, v___x_6538_, v___x_6540_, v___x_6543_, v___x_6543_, v___x_6545_, v___x_6535_);
v_kind_6547_ = lean_ctor_get_uint8(v_dec_6424_, sizeof(void*)*3);
v___x_6548_ = l_Lean_Syntax_node1(v___x_6536_, v___x_6537_, v___x_6546_);
v___x_6549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6549_, 0, v_t_6522_);
v___x_6550_ = lean_box(v___x_6434_);
v___x_6551_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6551_, 0, v___x_6548_);
lean_closure_set(v___x_6551_, 1, v_dec_6424_);
lean_closure_set(v___x_6551_, 2, v___x_6550_);
v___x_6552_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6535_, v___x_6549_, v___y_6521_, v___x_6551_, v_kind_6547_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_);
return v___x_6552_;
}
else
{
lean_object* v_a_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6560_; 
lean_dec(v_t_6522_);
lean_dec(v___y_6521_);
lean_dec(v_x_6519_);
lean_dec_ref(v_dec_6424_);
v_a_6553_ = lean_ctor_get(v___x_6531_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v___x_6531_);
if (v_isSharedCheck_6560_ == 0)
{
v___x_6555_ = v___x_6531_;
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_a_6553_);
lean_dec(v___x_6531_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v___x_6558_; 
if (v_isShared_6556_ == 0)
{
v___x_6558_ = v___x_6555_;
goto v_reusejp_6557_;
}
else
{
lean_object* v_reuseFailAlloc_6559_; 
v_reuseFailAlloc_6559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6553_);
v___x_6558_ = v_reuseFailAlloc_6559_;
goto v_reusejp_6557_;
}
v_reusejp_6557_:
{
return v___x_6558_;
}
}
}
}
v___jp_6561_:
{
lean_object* v___x_6570_; lean_object* v_rhs_6571_; lean_object* v___x_6572_; 
v___x_6570_ = lean_unsigned_to_nat(3u);
v_rhs_6571_ = l_Lean_Syntax_getArg(v___x_6437_, v___x_6570_);
lean_dec(v___x_6437_);
v___x_6572_ = l_Lean_Elab_Do_throwUnlessMutVarDeclared(v_x_6519_, v___y_6563_, v___y_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_);
if (lean_obj_tag(v___x_6572_) == 0)
{
lean_dec_ref_known(v___x_6572_, 1);
if (lean_obj_tag(v_t_x3f_6562_) == 0)
{
lean_object* v___x_6573_; lean_object* v___x_6574_; 
v___x_6573_ = l_Lean_TSyntax_getId(v_x_6519_);
v___x_6574_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_6573_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_);
if (lean_obj_tag(v___x_6574_) == 0)
{
lean_object* v_a_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; 
v_a_6575_ = lean_ctor_get(v___x_6574_, 0);
lean_inc(v_a_6575_);
lean_dec_ref_known(v___x_6574_, 1);
v___x_6576_ = l_Lean_LocalDecl_type(v_a_6575_);
lean_dec(v_a_6575_);
v___x_6577_ = l_Lean_Elab_Term_exprToSyntax(v___x_6576_, v___y_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_);
if (lean_obj_tag(v___x_6577_) == 0)
{
lean_object* v_a_6578_; 
v_a_6578_ = lean_ctor_get(v___x_6577_, 0);
lean_inc(v_a_6578_);
lean_dec_ref_known(v___x_6577_, 1);
v___y_6521_ = v_rhs_6571_;
v_t_6522_ = v_a_6578_;
v___y_6523_ = v___y_6563_;
v___y_6524_ = v___y_6564_;
v___y_6525_ = v___y_6565_;
v___y_6526_ = v___y_6566_;
v___y_6527_ = v___y_6567_;
v___y_6528_ = v___y_6568_;
v___y_6529_ = v___y_6569_;
goto v___jp_6520_;
}
else
{
lean_object* v_a_6579_; lean_object* v___x_6581_; uint8_t v_isShared_6582_; uint8_t v_isSharedCheck_6586_; 
lean_dec(v_rhs_6571_);
lean_dec(v_x_6519_);
lean_dec_ref(v_dec_6424_);
v_a_6579_ = lean_ctor_get(v___x_6577_, 0);
v_isSharedCheck_6586_ = !lean_is_exclusive(v___x_6577_);
if (v_isSharedCheck_6586_ == 0)
{
v___x_6581_ = v___x_6577_;
v_isShared_6582_ = v_isSharedCheck_6586_;
goto v_resetjp_6580_;
}
else
{
lean_inc(v_a_6579_);
lean_dec(v___x_6577_);
v___x_6581_ = lean_box(0);
v_isShared_6582_ = v_isSharedCheck_6586_;
goto v_resetjp_6580_;
}
v_resetjp_6580_:
{
lean_object* v___x_6584_; 
if (v_isShared_6582_ == 0)
{
v___x_6584_ = v___x_6581_;
goto v_reusejp_6583_;
}
else
{
lean_object* v_reuseFailAlloc_6585_; 
v_reuseFailAlloc_6585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6585_, 0, v_a_6579_);
v___x_6584_ = v_reuseFailAlloc_6585_;
goto v_reusejp_6583_;
}
v_reusejp_6583_:
{
return v___x_6584_;
}
}
}
}
else
{
lean_object* v_a_6587_; lean_object* v___x_6589_; uint8_t v_isShared_6590_; uint8_t v_isSharedCheck_6594_; 
lean_dec(v_rhs_6571_);
lean_dec(v_x_6519_);
lean_dec_ref(v_dec_6424_);
v_a_6587_ = lean_ctor_get(v___x_6574_, 0);
v_isSharedCheck_6594_ = !lean_is_exclusive(v___x_6574_);
if (v_isSharedCheck_6594_ == 0)
{
v___x_6589_ = v___x_6574_;
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
else
{
lean_inc(v_a_6587_);
lean_dec(v___x_6574_);
v___x_6589_ = lean_box(0);
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
v_resetjp_6588_:
{
lean_object* v___x_6592_; 
if (v_isShared_6590_ == 0)
{
v___x_6592_ = v___x_6589_;
goto v_reusejp_6591_;
}
else
{
lean_object* v_reuseFailAlloc_6593_; 
v_reuseFailAlloc_6593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6593_, 0, v_a_6587_);
v___x_6592_ = v_reuseFailAlloc_6593_;
goto v_reusejp_6591_;
}
v_reusejp_6591_:
{
return v___x_6592_;
}
}
}
}
else
{
lean_object* v_val_6595_; 
v_val_6595_ = lean_ctor_get(v_t_x3f_6562_, 0);
lean_inc(v_val_6595_);
lean_dec_ref_known(v_t_x3f_6562_, 1);
v___y_6521_ = v_rhs_6571_;
v_t_6522_ = v_val_6595_;
v___y_6523_ = v___y_6563_;
v___y_6524_ = v___y_6564_;
v___y_6525_ = v___y_6565_;
v___y_6526_ = v___y_6566_;
v___y_6527_ = v___y_6567_;
v___y_6528_ = v___y_6568_;
v___y_6529_ = v___y_6569_;
goto v___jp_6520_;
}
}
else
{
lean_object* v_a_6596_; lean_object* v___x_6598_; uint8_t v_isShared_6599_; uint8_t v_isSharedCheck_6603_; 
lean_dec(v_rhs_6571_);
lean_dec(v_t_x3f_6562_);
lean_dec(v_x_6519_);
lean_dec_ref(v_dec_6424_);
v_a_6596_ = lean_ctor_get(v___x_6572_, 0);
v_isSharedCheck_6603_ = !lean_is_exclusive(v___x_6572_);
if (v_isSharedCheck_6603_ == 0)
{
v___x_6598_ = v___x_6572_;
v_isShared_6599_ = v_isSharedCheck_6603_;
goto v_resetjp_6597_;
}
else
{
lean_inc(v_a_6596_);
lean_dec(v___x_6572_);
v___x_6598_ = lean_box(0);
v_isShared_6599_ = v_isSharedCheck_6603_;
goto v_resetjp_6597_;
}
v_resetjp_6597_:
{
lean_object* v___x_6601_; 
if (v_isShared_6599_ == 0)
{
v___x_6601_ = v___x_6598_;
goto v_reusejp_6600_;
}
else
{
lean_object* v_reuseFailAlloc_6602_; 
v_reuseFailAlloc_6602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_a_6596_);
v___x_6601_ = v_reuseFailAlloc_6602_;
goto v_reusejp_6600_;
}
v_reusejp_6600_:
{
return v___x_6601_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_6619_, lean_object* v_dec_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_, lean_object* v_a_6623_, lean_object* v_a_6624_, lean_object* v_a_6625_, lean_object* v_a_6626_, lean_object* v_a_6627_, lean_object* v_a_6628_){
_start:
{
lean_object* v_res_6629_; 
v_res_6629_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_6619_, v_dec_6620_, v_a_6621_, v_a_6622_, v_a_6623_, v_a_6624_, v_a_6625_, v_a_6626_, v_a_6627_);
lean_dec(v_a_6627_);
lean_dec_ref(v_a_6626_);
lean_dec(v_a_6625_);
lean_dec_ref(v_a_6624_);
lean_dec(v_a_6623_);
lean_dec_ref(v_a_6622_);
lean_dec_ref(v_a_6621_);
return v_res_6629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; 
v___x_6637_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6638_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_6639_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_6640_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_6641_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6637_, v___x_6638_, v___x_6639_, v___x_6640_);
return v___x_6641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_6642_){
_start:
{
lean_object* v_res_6643_; 
v_res_6643_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_6643_;
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
