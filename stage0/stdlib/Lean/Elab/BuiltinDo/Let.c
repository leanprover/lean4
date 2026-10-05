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
v___x_997_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_986_, v_a_995_, v___x_831_, v___x_831_, v___x_996_, v___y_991_, v___y_994_, v___y_988_, v___y_990_, v___y_992_, v___y_989_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref_known(v___x_997_, 1);
v___x_998_ = l_Lean_TSyntax_getId(v_x_986_);
v___x_999_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_998_, v___y_988_, v___y_990_, v___y_992_, v___y_989_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Lean_LocalDecl_type(v_a_1000_);
lean_dec(v_a_1000_);
v___x_1002_ = l_Lean_Elab_Term_exprToSyntax(v___x_1001_, v___y_991_, v___y_994_, v___y_988_, v___y_990_, v___y_992_, v___y_989_);
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
v_ref_1007_ = lean_ctor_get(v___y_992_, 2);
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
v___y_988_ = v___y_1047_;
v___y_989_ = v___y_1050_;
v___y_990_ = v___y_1048_;
v___y_991_ = v___y_1045_;
v___y_992_ = v___y_1049_;
v___y_993_ = v___x_1052_;
v___y_994_ = v___y_1046_;
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
v___y_989_ = v___y_1050_;
v___y_990_ = v___y_1048_;
v___y_991_ = v___y_1045_;
v___y_992_ = v___y_1049_;
v___y_993_ = v___x_1052_;
v___y_994_ = v___y_1046_;
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
uint8_t v___x_88568__boxed_1602_; uint8_t v___x_88571__boxed_1603_; lean_object* v_res_1604_; 
v___x_88568__boxed_1602_ = lean_unbox(v___x_1591_);
v___x_88571__boxed_1603_ = lean_unbox(v___x_1594_);
v_res_1604_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1589_, v___x_1590_, v___x_88568__boxed_1602_, v___x_1592_, v___x_1593_, v___x_88571__boxed_1603_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
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
size_t v_x_88703__boxed_1762_; size_t v_x_88704__boxed_1763_; lean_object* v_res_1764_; 
v_x_88703__boxed_1762_ = lean_unbox_usize(v_x_1758_);
lean_dec(v_x_1758_);
v_x_88704__boxed_1763_ = lean_unbox_usize(v_x_1759_);
lean_dec(v_x_1759_);
v_res_1764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1757_, v_x_88703__boxed_1762_, v_x_88704__boxed_1763_, v_x_1760_, v_x_1761_);
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
uint8_t v___x_89000__boxed_1954_; uint8_t v___x_89001__boxed_1955_; uint8_t v___y_89003__boxed_1956_; lean_object* v_res_1957_; 
v___x_89000__boxed_1954_ = lean_unbox(v___x_1942_);
v___x_89001__boxed_1955_ = lean_unbox(v___x_1943_);
v___y_89003__boxed_1956_ = lean_unbox(v___y_1945_);
v_res_1957_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1940_, v_value_1941_, v___x_89000__boxed_1954_, v___x_89001__boxed_1955_, v___x_1944_, v___y_89003__boxed_1956_, v_xs_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
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
uint8_t v_zeta_boxed_2051_; uint8_t v___y_89228__boxed_2052_; uint8_t v_usedOnly_boxed_2053_; uint8_t v___x_89229__boxed_2054_; lean_object* v_res_2055_; 
v_zeta_boxed_2051_ = lean_unbox(v_zeta_2036_);
v___y_89228__boxed_2052_ = lean_unbox(v___y_2037_);
v_usedOnly_boxed_2053_ = lean_unbox(v_usedOnly_2039_);
v___x_89229__boxed_2054_ = lean_unbox(v___x_2040_);
v_res_2055_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_2032_, v_a_2033_, v_letOrReassign_2034_, v_a_2035_, v_zeta_boxed_2051_, v___y_89228__boxed_2052_, v_x_2038_, v_usedOnly_boxed_2053_, v___x_89229__boxed_2054_, v_snd_2041_, v_h_x27_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
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
uint8_t v_zeta_boxed_2138_; uint8_t v_usedOnly_boxed_2139_; uint8_t v___y_89386__boxed_2140_; uint8_t v___x_89387__boxed_2141_; lean_object* v_res_2142_; 
v_zeta_boxed_2138_ = lean_unbox(v_zeta_2124_);
v_usedOnly_boxed_2139_ = lean_unbox(v_usedOnly_2125_);
v___y_89386__boxed_2140_ = lean_unbox(v___y_2127_);
v___x_89387__boxed_2141_ = lean_unbox(v___x_2128_);
v_res_2142_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_id_2119_, v_eq_x3f_2120_, v_a_2121_, v_letOrReassign_2122_, v_a_2123_, v_zeta_boxed_2138_, v_usedOnly_boxed_2139_, v_snd_2126_, v___y_89386__boxed_2140_, v___x_89387__boxed_2141_, v_x_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
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
uint8_t v___x_89514__boxed_2165_; lean_object* v_res_2166_; 
v___x_89514__boxed_2165_ = lean_unbox(v___x_2155_);
v_res_2166_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v___x_89514__boxed_2165_, v_____do__lift_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
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
uint8_t v___x_89549__boxed_2192_; lean_object* v_res_2193_; 
v___x_89549__boxed_2192_ = lean_unbox(v___x_2182_);
v_res_2193_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v_term_2180_, v___x_2181_, v___x_89549__boxed_2192_, v___x_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
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
lean_object* v___x_2231_; lean_object* v_infoState_2232_; lean_object* v_trees_2233_; lean_object* v___x_2234_; lean_object* v_infoState_2235_; lean_object* v_env_2236_; lean_object* v_nextMacroScope_2237_; lean_object* v_ngen_2238_; lean_object* v_auxDeclNGen_2239_; lean_object* v_traceState_2240_; lean_object* v_cache_2241_; lean_object* v_recordedDeps_2242_; lean_object* v_messages_2243_; lean_object* v_snapshotTasks_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2265_; 
v___x_2231_ = lean_st_ref_get(v___y_2229_);
v_infoState_2232_ = lean_ctor_get(v___x_2231_, 8);
lean_inc_ref(v_infoState_2232_);
lean_dec(v___x_2231_);
v_trees_2233_ = lean_ctor_get(v_infoState_2232_, 2);
lean_inc_ref(v_trees_2233_);
lean_dec_ref(v_infoState_2232_);
v___x_2234_ = lean_st_ref_take(v___y_2229_);
v_infoState_2235_ = lean_ctor_get(v___x_2234_, 8);
v_env_2236_ = lean_ctor_get(v___x_2234_, 0);
v_nextMacroScope_2237_ = lean_ctor_get(v___x_2234_, 1);
v_ngen_2238_ = lean_ctor_get(v___x_2234_, 2);
v_auxDeclNGen_2239_ = lean_ctor_get(v___x_2234_, 3);
v_traceState_2240_ = lean_ctor_get(v___x_2234_, 4);
v_cache_2241_ = lean_ctor_get(v___x_2234_, 5);
v_recordedDeps_2242_ = lean_ctor_get(v___x_2234_, 6);
v_messages_2243_ = lean_ctor_get(v___x_2234_, 7);
v_snapshotTasks_2244_ = lean_ctor_get(v___x_2234_, 9);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2246_ = v___x_2234_;
v_isShared_2247_ = v_isSharedCheck_2265_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_snapshotTasks_2244_);
lean_inc(v_infoState_2235_);
lean_inc(v_messages_2243_);
lean_inc(v_recordedDeps_2242_);
lean_inc(v_cache_2241_);
lean_inc(v_traceState_2240_);
lean_inc(v_auxDeclNGen_2239_);
lean_inc(v_ngen_2238_);
lean_inc(v_nextMacroScope_2237_);
lean_inc(v_env_2236_);
lean_dec(v___x_2234_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2265_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
uint8_t v_enabled_2248_; lean_object* v_assignment_2249_; lean_object* v_lazyAssignment_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2263_; 
v_enabled_2248_ = lean_ctor_get_uint8(v_infoState_2235_, sizeof(void*)*3);
v_assignment_2249_ = lean_ctor_get(v_infoState_2235_, 0);
v_lazyAssignment_2250_ = lean_ctor_get(v_infoState_2235_, 1);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_infoState_2235_);
if (v_isSharedCheck_2263_ == 0)
{
lean_object* v_unused_2264_; 
v_unused_2264_ = lean_ctor_get(v_infoState_2235_, 2);
lean_dec(v_unused_2264_);
v___x_2252_ = v_infoState_2235_;
v_isShared_2253_ = v_isSharedCheck_2263_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_lazyAssignment_2250_);
lean_inc(v_assignment_2249_);
lean_dec(v_infoState_2235_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2263_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 2, v___x_2254_);
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_assignment_2249_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_lazyAssignment_2250_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v___x_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*3, v_enabled_2248_);
v___x_2256_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2258_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 8, v___x_2256_);
v___x_2258_ = v___x_2246_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_env_2236_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_nextMacroScope_2237_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v_ngen_2238_);
lean_ctor_set(v_reuseFailAlloc_2261_, 3, v_auxDeclNGen_2239_);
lean_ctor_set(v_reuseFailAlloc_2261_, 4, v_traceState_2240_);
lean_ctor_set(v_reuseFailAlloc_2261_, 5, v_cache_2241_);
lean_ctor_set(v_reuseFailAlloc_2261_, 6, v_recordedDeps_2242_);
lean_ctor_set(v_reuseFailAlloc_2261_, 7, v_messages_2243_);
lean_ctor_set(v_reuseFailAlloc_2261_, 8, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2261_, 9, v_snapshotTasks_2244_);
v___x_2258_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = lean_st_ref_put(v___y_2229_, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v_trees_2233_);
return v___x_2260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___boxed(lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(v___y_2266_);
lean_dec(v___y_2266_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(lean_object* v___y_2269_, lean_object* v_mkInfoTree_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v_a_2276_, lean_object* v_a_x3f_2277_){
_start:
{
lean_object* v___x_2279_; lean_object* v_infoState_2280_; lean_object* v_trees_2281_; lean_object* v___x_2282_; 
v___x_2279_ = lean_st_ref_get(v___y_2269_);
v_infoState_2280_ = lean_ctor_get(v___x_2279_, 8);
lean_inc_ref(v_infoState_2280_);
lean_dec(v___x_2279_);
v_trees_2281_ = lean_ctor_get(v_infoState_2280_, 2);
lean_inc_ref(v_trees_2281_);
lean_dec_ref(v_infoState_2280_);
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2275_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
v___x_2282_ = lean_apply_8(v_mkInfoTree_2270_, v_trees_2281_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2269_, lean_box(0));
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2322_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2322_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2322_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v_infoState_2288_; lean_object* v_env_2289_; lean_object* v_nextMacroScope_2290_; lean_object* v_ngen_2291_; lean_object* v_auxDeclNGen_2292_; lean_object* v_traceState_2293_; lean_object* v_cache_2294_; lean_object* v_recordedDeps_2295_; lean_object* v_messages_2296_; lean_object* v_snapshotTasks_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2321_; 
v___x_2287_ = lean_st_ref_take(v___y_2269_);
v_infoState_2288_ = lean_ctor_get(v___x_2287_, 8);
v_env_2289_ = lean_ctor_get(v___x_2287_, 0);
v_nextMacroScope_2290_ = lean_ctor_get(v___x_2287_, 1);
v_ngen_2291_ = lean_ctor_get(v___x_2287_, 2);
v_auxDeclNGen_2292_ = lean_ctor_get(v___x_2287_, 3);
v_traceState_2293_ = lean_ctor_get(v___x_2287_, 4);
v_cache_2294_ = lean_ctor_get(v___x_2287_, 5);
v_recordedDeps_2295_ = lean_ctor_get(v___x_2287_, 6);
v_messages_2296_ = lean_ctor_get(v___x_2287_, 7);
v_snapshotTasks_2297_ = lean_ctor_get(v___x_2287_, 9);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2299_ = v___x_2287_;
v_isShared_2300_ = v_isSharedCheck_2321_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_snapshotTasks_2297_);
lean_inc(v_infoState_2288_);
lean_inc(v_messages_2296_);
lean_inc(v_recordedDeps_2295_);
lean_inc(v_cache_2294_);
lean_inc(v_traceState_2293_);
lean_inc(v_auxDeclNGen_2292_);
lean_inc(v_ngen_2291_);
lean_inc(v_nextMacroScope_2290_);
lean_inc(v_env_2289_);
lean_dec(v___x_2287_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2321_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
uint8_t v_enabled_2301_; lean_object* v_assignment_2302_; lean_object* v_lazyAssignment_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2319_; 
v_enabled_2301_ = lean_ctor_get_uint8(v_infoState_2288_, sizeof(void*)*3);
v_assignment_2302_ = lean_ctor_get(v_infoState_2288_, 0);
v_lazyAssignment_2303_ = lean_ctor_get(v_infoState_2288_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_infoState_2288_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_infoState_2288_, 2);
lean_dec(v_unused_2320_);
v___x_2305_ = v_infoState_2288_;
v_isShared_2306_ = v_isSharedCheck_2319_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_lazyAssignment_2303_);
lean_inc(v_assignment_2302_);
lean_dec(v_infoState_2288_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2319_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2307_ = lean_box(0);
v___x_2308_ = l_Lean_PersistentArray_push___redArg(v_a_2276_, v_a_2283_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 2, v___x_2308_);
v___x_2310_ = v___x_2305_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_assignment_2302_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_lazyAssignment_2303_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v___x_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2318_, sizeof(void*)*3, v_enabled_2301_);
v___x_2310_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2312_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 8, v___x_2310_);
v___x_2312_ = v___x_2299_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_env_2289_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_nextMacroScope_2290_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_ngen_2291_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_auxDeclNGen_2292_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v_traceState_2293_);
lean_ctor_set(v_reuseFailAlloc_2317_, 5, v_cache_2294_);
lean_ctor_set(v_reuseFailAlloc_2317_, 6, v_recordedDeps_2295_);
lean_ctor_set(v_reuseFailAlloc_2317_, 7, v_messages_2296_);
lean_ctor_set(v_reuseFailAlloc_2317_, 8, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2317_, 9, v_snapshotTasks_2297_);
v___x_2312_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = lean_st_ref_put(v___y_2269_, v___x_2312_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2307_);
v___x_2315_ = v___x_2285_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2307_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v_a_2276_);
v_a_2323_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2282_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2282_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v___y_2331_, lean_object* v_mkInfoTree_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v_a_2338_, lean_object* v_a_x3f_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(v___y_2331_, v_mkInfoTree_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v_a_2338_, v_a_x3f_2339_);
lean_dec(v_a_x3f_2339_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2331_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(lean_object* v_x_2342_, lean_object* v_mkInfoTree_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v_infoState_2352_; uint8_t v_enabled_2353_; 
v___x_2351_ = lean_st_ref_get(v___y_2349_);
v_infoState_2352_ = lean_ctor_get(v___x_2351_, 8);
lean_inc_ref(v_infoState_2352_);
lean_dec(v___x_2351_);
v_enabled_2353_ = lean_ctor_get_uint8(v_infoState_2352_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2352_);
if (v_enabled_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_dec_ref(v_mkInfoTree_2343_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
v___x_2354_ = lean_apply_7(v_x_2342_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, lean_box(0));
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; lean_object* v_a_2356_; lean_object* v_r_2357_; 
v___x_2355_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(v___y_2349_);
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2355_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
v_r_2357_ = lean_apply_7(v_x_2342_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, lean_box(0));
if (lean_obj_tag(v_r_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2382_; 
v_a_2358_ = lean_ctor_get(v_r_2357_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_r_2357_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2360_ = v_r_2357_;
v_isShared_2361_ = v_isSharedCheck_2382_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v_r_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2382_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
lean_inc(v_a_2358_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(v___y_2349_, v_mkInfoTree_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v_a_2356_, v___x_2363_);
lean_dec_ref(v___x_2363_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2371_ == 0)
{
lean_object* v_unused_2372_; 
v_unused_2372_ = lean_ctor_get(v___x_2364_, 0);
lean_dec(v_unused_2372_);
v___x_2366_ = v___x_2364_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v___x_2364_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v_a_2358_);
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2358_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_a_2358_);
v_a_2373_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2364_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2364_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_a_2383_ = lean_ctor_get(v_r_2357_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v_r_2357_, 1);
v___x_2384_ = lean_box(0);
v___x_2385_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(v___y_2349_, v_mkInfoTree_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v_a_2356_, v___x_2384_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v___x_2385_, 0);
lean_dec(v_unused_2393_);
v___x_2387_ = v___x_2385_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_dec(v___x_2385_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 1);
lean_ctor_set(v___x_2387_, 0, v_a_2383_);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2383_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v_a_2383_);
v_a_2394_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2385_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2385_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_x_2402_, lean_object* v_mkInfoTree_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(v_x_2402_, v_mkInfoTree_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(lean_object* v_stx_2412_, lean_object* v_output_2413_, lean_object* v_x_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___f_2422_; lean_object* v___x_2423_; 
v___f_2422_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2422_, 0, v_stx_2412_);
lean_closure_set(v___f_2422_, 1, v_output_2413_);
v___x_2423_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(v_x_2414_, v___f_2422_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___boxed(lean_object* v_stx_2424_, lean_object* v_output_2425_, lean_object* v_x_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_stx_2424_, v_output_2425_, v_x_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0(lean_object* v_x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
lean_inc_ref(v___y_2436_);
v___x_2444_ = lean_apply_8(v_x_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, lean_box(0));
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0___boxed(lean_object* v_x_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0(v_x_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec_ref(v___y_2446_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(lean_object* v_beforeStx_2455_, lean_object* v_afterStx_2456_, lean_object* v_x_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___f_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_inc_ref(v___y_2458_);
v___f_2466_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2466_, 0, v_x_2457_);
lean_closure_set(v___f_2466_, 1, v___y_2458_);
lean_inc(v_afterStx_2456_);
lean_inc(v_beforeStx_2455_);
v___x_2467_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2467_, 0, lean_box(0));
lean_closure_set(v___x_2467_, 1, v_beforeStx_2455_);
lean_closure_set(v___x_2467_, 2, v_afterStx_2456_);
lean_closure_set(v___x_2467_, 3, v___f_2466_);
v___x_2468_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_beforeStx_2455_, v_afterStx_2456_, v___x_2467_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2468_) == 0)
{
return v___x_2468_;
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___boxed(lean_object* v_beforeStx_2477_, lean_object* v_afterStx_2478_, lean_object* v_x_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_beforeStx_2477_, v_afterStx_2478_, v_x_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2488_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__1));
v___x_2492_ = l_String_toRawSubstring_x27(v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_rhs_2514_, uint8_t v___x_2515_, lean_object* v_config_2516_, lean_object* v_a_2517_, uint8_t v___x_2518_, lean_object* v___x_2519_, lean_object* v___x_2520_, lean_object* v___x_2521_, lean_object* v___f_2522_, lean_object* v___x_2523_, lean_object* v_body_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_term_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v_ref_2541_; lean_object* v___y_2542_; lean_object* v_toCold_2548_; lean_object* v_ref_2549_; lean_object* v_quotContext_2550_; lean_object* v_currMacroScope_2551_; lean_object* v_ref_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v_eq_x3f_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v_toCold_2548_ = lean_ctor_get(v___y_2530_, 0);
v_ref_2549_ = lean_ctor_get(v___y_2530_, 2);
v_quotContext_2550_ = lean_ctor_get(v_toCold_2548_, 8);
v_currMacroScope_2551_ = lean_ctor_get(v_toCold_2548_, 9);
v_ref_2552_ = l_Lean_replaceRef(v_rhs_2514_, v_ref_2549_);
v___x_2553_ = l_Lean_SourceInfo_fromRef(v_ref_2552_, v___x_2515_);
lean_dec(v_ref_2552_);
v___x_2554_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__0));
lean_inc_n(v___x_2553_, 2);
v___x_2555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2);
v_eq_x3f_2557_ = lean_ctor_get(v_config_2516_, 0);
lean_inc(v_eq_x3f_2557_);
lean_dec_ref(v_config_2516_);
v___x_2558_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__3));
lean_inc(v_currMacroScope_2551_);
lean_inc(v_quotContext_2550_);
v___x_2559_ = l_Lean_addMacroScope(v_quotContext_2550_, v___x_2558_, v_currMacroScope_2551_);
v___x_2560_ = lean_box(0);
lean_inc(v___x_2559_);
v___x_2561_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2553_);
lean_ctor_set(v___x_2561_, 1, v___x_2556_);
lean_ctor_set(v___x_2561_, 2, v___x_2559_);
lean_ctor_set(v___x_2561_, 3, v___x_2560_);
v___x_2562_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__4));
lean_inc_ref(v___x_2521_);
lean_inc_ref(v___x_2520_);
lean_inc_ref(v___x_2519_);
v___x_2563_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_node2(v___x_2553_, v___x_2563_, v___x_2555_, v___x_2561_);
if (lean_obj_tag(v_eq_x3f_2557_) == 1)
{
lean_object* v_val_2565_; lean_object* v___x_2566_; 
v_val_2565_ = lean_ctor_get(v_eq_x3f_2557_, 0);
lean_inc(v_val_2565_);
lean_dec_ref_known(v_eq_x3f_2557_, 1);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc_ref(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v_ref_2549_);
v___x_2566_ = lean_apply_9(v___f_2522_, v_ref_2549_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, lean_box(0));
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc_n(v_a_2567_, 23);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5));
lean_inc_ref_n(v___x_2521_, 5);
lean_inc_ref_n(v___x_2520_, 5);
lean_inc_ref_n(v___x_2519_, 5);
v___x_2569_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2568_);
v___x_2570_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6));
v___x_2571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2567_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_a_2567_);
lean_ctor_set(v___x_2572_, 1, v___x_2554_);
v___x_2573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2573_, 0, v_a_2567_);
lean_ctor_set(v___x_2573_, 1, v___x_2556_);
lean_ctor_set(v___x_2573_, 2, v___x_2559_);
lean_ctor_set(v___x_2573_, 3, v___x_2560_);
v___x_2574_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_a_2567_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_2577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2577_, 0, v_a_2567_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8));
v___x_2579_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2578_);
v___x_2580_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9));
v___x_2581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2581_, 0, v_a_2567_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_2583_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_a_2567_);
lean_ctor_set(v___x_2584_, 1, v___x_2582_);
v___x_2585_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2586_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2587_, 0, v_a_2567_);
lean_ctor_set(v___x_2587_, 1, v___x_2585_);
lean_ctor_set(v___x_2587_, 2, v___x_2586_);
v___x_2588_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11));
v___x_2589_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2588_);
v___x_2590_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2567_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = l_Lean_Syntax_node2(v_a_2567_, v___x_2585_, v_val_2565_, v___x_2591_);
v___x_2593_ = l_Lean_Syntax_node2(v_a_2567_, v___x_2589_, v___x_2592_, v___x_2564_);
v___x_2594_ = l_Lean_Syntax_node1(v_a_2567_, v___x_2585_, v___x_2593_);
v___x_2595_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_2596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_a_2567_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13));
v___x_2598_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2597_);
v___x_2599_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14));
v___x_2600_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2599_);
v___x_2601_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_2602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2602_, 0, v_a_2567_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_Syntax_node1(v_a_2567_, v___x_2585_, v___x_2523_);
v___x_2604_ = l_Lean_Syntax_node1(v_a_2567_, v___x_2585_, v___x_2603_);
v___x_2605_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_2606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2606_, 0, v_a_2567_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = l_Lean_Syntax_node4(v_a_2567_, v___x_2600_, v___x_2602_, v___x_2604_, v___x_2606_, v_body_2524_);
v___x_2608_ = l_Lean_Syntax_node1(v_a_2567_, v___x_2585_, v___x_2607_);
v___x_2609_ = l_Lean_Syntax_node1(v_a_2567_, v___x_2598_, v___x_2608_);
lean_inc_ref(v___x_2587_);
v___x_2610_ = l_Lean_Syntax_node6(v_a_2567_, v___x_2583_, v___x_2584_, v___x_2587_, v___x_2587_, v___x_2594_, v___x_2596_, v___x_2609_);
lean_inc_ref(v___x_2577_);
lean_inc_ref(v___x_2573_);
lean_inc_ref(v___x_2572_);
v___x_2611_ = l_Lean_Syntax_node5(v_a_2567_, v___x_2579_, v___x_2581_, v___x_2572_, v___x_2573_, v___x_2577_, v___x_2610_);
v___x_2612_ = l_Lean_Syntax_node7(v_a_2567_, v___x_2569_, v___x_2571_, v___x_2572_, v___x_2573_, v___x_2575_, v_rhs_2514_, v___x_2577_, v___x_2611_);
lean_inc(v_ref_2549_);
v_term_2534_ = v___x_2612_;
v___y_2535_ = v___y_2525_;
v___y_2536_ = v___y_2526_;
v___y_2537_ = v___y_2527_;
v___y_2538_ = v___y_2528_;
v___y_2539_ = v___y_2529_;
v___y_2540_ = v___y_2530_;
v_ref_2541_ = v_ref_2549_;
v___y_2542_ = v___y_2531_;
goto v___jp_2533_;
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_val_2565_);
lean_dec(v___x_2564_);
lean_dec(v___x_2559_);
lean_dec(v_body_2524_);
lean_dec(v___x_2523_);
lean_dec_ref(v___x_2521_);
lean_dec_ref(v___x_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v_a_2517_);
lean_dec(v_rhs_2514_);
v_a_2613_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2566_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2566_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v___x_2621_; 
lean_dec(v_eq_x3f_2557_);
lean_inc_ref(v_a_2517_);
v___x_2621_ = l_Lean_Elab_Term_exprToSyntax(v_a_2517_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2623_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc_ref(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v_ref_2549_);
v___x_2623_ = lean_apply_9(v___f_2522_, v_ref_2549_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, lean_box(0));
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc_n(v_a_2624_, 32);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5));
lean_inc_ref_n(v___x_2521_, 8);
lean_inc_ref_n(v___x_2520_, 8);
lean_inc_ref_n(v___x_2519_, 8);
v___x_2626_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2625_);
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6));
v___x_2628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2628_, 0, v_a_2624_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2629_, 0, v_a_2624_);
lean_ctor_set(v___x_2629_, 1, v___x_2554_);
v___x_2630_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2630_, 0, v_a_2624_);
lean_ctor_set(v___x_2630_, 1, v___x_2556_);
lean_ctor_set(v___x_2630_, 2, v___x_2559_);
lean_ctor_set(v___x_2630_, 3, v___x_2560_);
v___x_2631_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2632_, 0, v_a_2624_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_2634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2634_, 0, v_a_2624_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8));
v___x_2636_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2635_);
v___x_2637_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9));
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v_a_2624_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_2640_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2639_);
v___x_2641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2641_, 0, v_a_2624_);
lean_ctor_set(v___x_2641_, 1, v___x_2639_);
v___x_2642_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2643_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2644_, 0, v_a_2624_);
lean_ctor_set(v___x_2644_, 1, v___x_2642_);
lean_ctor_set(v___x_2644_, 2, v___x_2643_);
v___x_2645_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__17));
v___x_2646_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2645_);
v___x_2647_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2648_, 0, v_a_2624_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2649_, 0, v_a_2624_);
lean_ctor_set(v___x_2649_, 1, v___x_2645_);
v___x_2650_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__18));
v___x_2651_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2650_);
v___x_2652_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__19));
v___x_2653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_a_2624_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__20));
v___x_2655_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2654_);
v___x_2656_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_2657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2657_, 0, v_a_2624_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_Syntax_node1(v_a_2624_, v___x_2655_, v___x_2657_);
v___x_2659_ = l_Lean_Syntax_node1(v_a_2624_, v___x_2642_, v___x_2658_);
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__22));
v___x_2661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2661_, 0, v_a_2624_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
lean_inc_ref_n(v___x_2644_, 2);
v___x_2662_ = l_Lean_Syntax_node5(v_a_2624_, v___x_2651_, v___x_2653_, v___x_2659_, v___x_2644_, v___x_2661_, v_a_2622_);
v___x_2663_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2664_, 0, v_a_2624_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
lean_inc_ref(v___x_2632_);
v___x_2665_ = l_Lean_Syntax_node5(v_a_2624_, v___x_2646_, v___x_2648_, v___x_2649_, v___x_2632_, v___x_2662_, v___x_2664_);
v___x_2666_ = l_Lean_Syntax_node1(v_a_2624_, v___x_2642_, v___x_2665_);
v___x_2667_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11));
v___x_2668_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2667_);
v___x_2669_ = l_Lean_Syntax_node2(v_a_2624_, v___x_2668_, v___x_2644_, v___x_2564_);
v___x_2670_ = l_Lean_Syntax_node1(v_a_2624_, v___x_2642_, v___x_2669_);
v___x_2671_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_2672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2672_, 0, v_a_2624_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13));
v___x_2674_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2673_);
v___x_2675_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14));
v___x_2676_ = l_Lean_Name_mkStr4(v___x_2519_, v___x_2520_, v___x_2521_, v___x_2675_);
v___x_2677_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_2678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_a_2624_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_Syntax_node1(v_a_2624_, v___x_2642_, v___x_2523_);
v___x_2680_ = l_Lean_Syntax_node1(v_a_2624_, v___x_2642_, v___x_2679_);
v___x_2681_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_2682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2682_, 0, v_a_2624_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = l_Lean_Syntax_node4(v_a_2624_, v___x_2676_, v___x_2678_, v___x_2680_, v___x_2682_, v_body_2524_);
v___x_2684_ = l_Lean_Syntax_node1(v_a_2624_, v___x_2642_, v___x_2683_);
v___x_2685_ = l_Lean_Syntax_node1(v_a_2624_, v___x_2674_, v___x_2684_);
v___x_2686_ = l_Lean_Syntax_node6(v_a_2624_, v___x_2640_, v___x_2641_, v___x_2644_, v___x_2666_, v___x_2670_, v___x_2672_, v___x_2685_);
lean_inc_ref(v___x_2634_);
lean_inc_ref(v___x_2630_);
lean_inc_ref(v___x_2629_);
v___x_2687_ = l_Lean_Syntax_node5(v_a_2624_, v___x_2636_, v___x_2638_, v___x_2629_, v___x_2630_, v___x_2634_, v___x_2686_);
v___x_2688_ = l_Lean_Syntax_node7(v_a_2624_, v___x_2626_, v___x_2628_, v___x_2629_, v___x_2630_, v___x_2632_, v_rhs_2514_, v___x_2634_, v___x_2687_);
lean_inc(v_ref_2549_);
v_term_2534_ = v___x_2688_;
v___y_2535_ = v___y_2525_;
v___y_2536_ = v___y_2526_;
v___y_2537_ = v___y_2527_;
v___y_2538_ = v___y_2528_;
v___y_2539_ = v___y_2529_;
v___y_2540_ = v___y_2530_;
v_ref_2541_ = v_ref_2549_;
v___y_2542_ = v___y_2531_;
goto v___jp_2533_;
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_a_2622_);
lean_dec(v___x_2564_);
lean_dec(v___x_2559_);
lean_dec(v_body_2524_);
lean_dec(v___x_2523_);
lean_dec_ref(v___x_2521_);
lean_dec_ref(v___x_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v_a_2517_);
lean_dec(v_rhs_2514_);
v_a_2689_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2623_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2623_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v___x_2564_);
lean_dec(v___x_2559_);
lean_dec(v_body_2524_);
lean_dec(v___x_2523_);
lean_dec_ref(v___f_2522_);
lean_dec_ref(v___x_2521_);
lean_dec_ref(v___x_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v_a_2517_);
lean_dec(v_rhs_2514_);
v_a_2697_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2621_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2621_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
v___jp_2533_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; 
v___x_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_a_2517_);
v___x_2544_ = lean_box(0);
v___x_2545_ = lean_box(v___x_2518_);
lean_inc(v_term_2534_);
v___f_2546_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 12, 4);
lean_closure_set(v___f_2546_, 0, v_term_2534_);
lean_closure_set(v___f_2546_, 1, v___x_2543_);
lean_closure_set(v___f_2546_, 2, v___x_2545_);
lean_closure_set(v___f_2546_, 3, v___x_2544_);
v___x_2547_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_ref_2541_, v_term_2534_, v___f_2546_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2542_);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object** _args){
lean_object* v_rhs_2705_ = _args[0];
lean_object* v___x_2706_ = _args[1];
lean_object* v_config_2707_ = _args[2];
lean_object* v_a_2708_ = _args[3];
lean_object* v___x_2709_ = _args[4];
lean_object* v___x_2710_ = _args[5];
lean_object* v___x_2711_ = _args[6];
lean_object* v___x_2712_ = _args[7];
lean_object* v___f_2713_ = _args[8];
lean_object* v___x_2714_ = _args[9];
lean_object* v_body_2715_ = _args[10];
lean_object* v___y_2716_ = _args[11];
lean_object* v___y_2717_ = _args[12];
lean_object* v___y_2718_ = _args[13];
lean_object* v___y_2719_ = _args[14];
lean_object* v___y_2720_ = _args[15];
lean_object* v___y_2721_ = _args[16];
lean_object* v___y_2722_ = _args[17];
lean_object* v___y_2723_ = _args[18];
_start:
{
uint8_t v___x_90078__boxed_2724_; uint8_t v___x_90080__boxed_2725_; lean_object* v_res_2726_; 
v___x_90078__boxed_2724_ = lean_unbox(v___x_2706_);
v___x_90080__boxed_2725_ = lean_unbox(v___x_2709_);
v_res_2726_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_rhs_2705_, v___x_90078__boxed_2724_, v_config_2707_, v_a_2708_, v___x_90080__boxed_2725_, v___x_2710_, v___x_2711_, v___x_2712_, v___f_2713_, v___x_2714_, v_body_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2726_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2727_; double v___x_2728_; 
v___x_2727_ = lean_unsigned_to_nat(0u);
v___x_2728_ = lean_float_of_nat(v___x_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_cls_2731_, lean_object* v_msg_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_ref_2738_; lean_object* v___x_2739_; lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2785_; 
v_ref_2738_ = lean_ctor_get(v___y_2735_, 2);
v___x_2739_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(v_msg_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2785_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2785_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; lean_object* v_traceState_2745_; lean_object* v_env_2746_; lean_object* v_nextMacroScope_2747_; lean_object* v_ngen_2748_; lean_object* v_auxDeclNGen_2749_; lean_object* v_cache_2750_; lean_object* v_recordedDeps_2751_; lean_object* v_messages_2752_; lean_object* v_infoState_2753_; lean_object* v_snapshotTasks_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2784_; 
v___x_2744_ = lean_st_ref_take(v___y_2736_);
v_traceState_2745_ = lean_ctor_get(v___x_2744_, 4);
v_env_2746_ = lean_ctor_get(v___x_2744_, 0);
v_nextMacroScope_2747_ = lean_ctor_get(v___x_2744_, 1);
v_ngen_2748_ = lean_ctor_get(v___x_2744_, 2);
v_auxDeclNGen_2749_ = lean_ctor_get(v___x_2744_, 3);
v_cache_2750_ = lean_ctor_get(v___x_2744_, 5);
v_recordedDeps_2751_ = lean_ctor_get(v___x_2744_, 6);
v_messages_2752_ = lean_ctor_get(v___x_2744_, 7);
v_infoState_2753_ = lean_ctor_get(v___x_2744_, 8);
v_snapshotTasks_2754_ = lean_ctor_get(v___x_2744_, 9);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2756_ = v___x_2744_;
v_isShared_2757_ = v_isSharedCheck_2784_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_snapshotTasks_2754_);
lean_inc(v_infoState_2753_);
lean_inc(v_messages_2752_);
lean_inc(v_recordedDeps_2751_);
lean_inc(v_cache_2750_);
lean_inc(v_traceState_2745_);
lean_inc(v_auxDeclNGen_2749_);
lean_inc(v_ngen_2748_);
lean_inc(v_nextMacroScope_2747_);
lean_inc(v_env_2746_);
lean_dec(v___x_2744_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2784_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
uint64_t v_tid_2758_; lean_object* v_traces_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2783_; 
v_tid_2758_ = lean_ctor_get_uint64(v_traceState_2745_, sizeof(void*)*1);
v_traces_2759_ = lean_ctor_get(v_traceState_2745_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_traceState_2745_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2761_ = v_traceState_2745_;
v_isShared_2762_ = v_isSharedCheck_2783_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_traces_2759_);
lean_dec(v_traceState_2745_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2783_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; double v___x_2765_; uint8_t v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2763_ = lean_box(0);
v___x_2764_ = lean_box(0);
v___x_2765_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0);
v___x_2766_ = 0;
v___x_2767_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2768_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2768_, 0, v_cls_2731_);
lean_ctor_set(v___x_2768_, 1, v___x_2764_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
lean_ctor_set_float(v___x_2768_, sizeof(void*)*3, v___x_2765_);
lean_ctor_set_float(v___x_2768_, sizeof(void*)*3 + 8, v___x_2765_);
lean_ctor_set_uint8(v___x_2768_, sizeof(void*)*3 + 16, v___x_2766_);
v___x_2769_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1));
v___x_2770_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2768_);
lean_ctor_set(v___x_2770_, 1, v_a_2740_);
lean_ctor_set(v___x_2770_, 2, v___x_2769_);
lean_inc(v_ref_2738_);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v_ref_2738_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_PersistentArray_push___redArg(v_traces_2759_, v___x_2771_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2772_);
v___x_2774_ = v___x_2761_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2772_);
lean_ctor_set_uint64(v_reuseFailAlloc_2782_, sizeof(void*)*1, v_tid_2758_);
v___x_2774_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2776_; 
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 4, v___x_2774_);
v___x_2776_ = v___x_2756_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_env_2746_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_nextMacroScope_2747_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v_ngen_2748_);
lean_ctor_set(v_reuseFailAlloc_2781_, 3, v_auxDeclNGen_2749_);
lean_ctor_set(v_reuseFailAlloc_2781_, 4, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2781_, 5, v_cache_2750_);
lean_ctor_set(v_reuseFailAlloc_2781_, 6, v_recordedDeps_2751_);
lean_ctor_set(v_reuseFailAlloc_2781_, 7, v_messages_2752_);
lean_ctor_set(v_reuseFailAlloc_2781_, 8, v_infoState_2753_);
lean_ctor_set(v_reuseFailAlloc_2781_, 9, v_snapshotTasks_2754_);
v___x_2776_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2777_ = lean_st_ref_put(v___y_2736_, v___x_2776_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2763_);
v___x_2779_ = v___x_2742_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2763_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_cls_2786_, lean_object* v_msg_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_2786_, v_msg_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(lean_object* v_env_2794_, lean_object* v_currNamespace_2795_, lean_object* v_openDecls_2796_, lean_object* v_n_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = l_Lean_ResolveName_resolveNamespace(v_env_2794_, v_currNamespace_2795_, v_openDecls_2796_, v_n_2797_);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___y_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed(lean_object* v_env_2802_, lean_object* v_currNamespace_2803_, lean_object* v_openDecls_2804_, lean_object* v_n_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(v_env_2802_, v_currNamespace_2803_, v_openDecls_2804_, v_n_2805_, v___y_2806_, v___y_2807_);
lean_dec_ref(v___y_2806_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(lean_object* v_currNamespace_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v_currNamespace_2809_);
lean_ctor_set(v___x_2812_, 1, v___y_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed(lean_object* v_currNamespace_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(v_currNamespace_2813_, v___y_2814_, v___y_2815_);
lean_dec_ref(v___y_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_env_2817_, lean_object* v_declName_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
uint8_t v___x_2821_; lean_object* v_env_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; uint8_t v___x_2825_; 
v___x_2821_ = 0;
v_env_2822_ = l_Lean_Environment_setExporting(v_env_2817_, v___x_2821_);
lean_inc(v_declName_2818_);
v___x_2823_ = l_Lean_mkPrivateName(v_env_2822_, v_declName_2818_);
v___x_2824_ = 1;
lean_inc_ref(v_env_2822_);
v___x_2825_ = l_Lean_Environment_contains(v_env_2822_, v___x_2823_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2826_ = l_Lean_privateToUserName(v_declName_2818_);
v___x_2827_ = l_Lean_Environment_contains(v_env_2822_, v___x_2826_, v___x_2824_);
v___x_2828_ = lean_box(v___x_2827_);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___y_2820_);
return v___x_2829_;
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v_env_2822_);
lean_dec(v_declName_2818_);
v___x_2830_ = lean_box(v___x_2825_);
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___y_2820_);
return v___x_2831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_env_2832_, lean_object* v_declName_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_env_2832_, v_declName_2833_, v___y_2834_, v___y_2835_);
lean_dec_ref(v___y_2834_);
return v_res_2836_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = l_Lean_maxRecDepthErrorMessage;
v___x_2843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4(void){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3);
v___x_2845_ = l_Lean_MessageData_ofFormat(v___x_2844_);
return v___x_2845_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4);
v___x_2847_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__2));
v___x_2848_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
lean_ctor_set(v___x_2848_, 1, v___x_2846_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(lean_object* v_ref_2849_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5);
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v_ref_2849_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(v_ref_2854_);
return v_res_2856_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(lean_object* v_keys_2857_, lean_object* v_i_2858_, lean_object* v_k_2859_){
_start:
{
lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2860_ = lean_array_get_size(v_keys_2857_);
v___x_2861_ = lean_nat_dec_lt(v_i_2858_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_dec(v_i_2858_);
return v___x_2861_;
}
else
{
lean_object* v_k_x27_2862_; uint8_t v___x_2863_; 
v_k_x27_2862_ = lean_array_fget_borrowed(v_keys_2857_, v_i_2858_);
v___x_2863_ = l_Lean_instBEqExtraModUse_beq(v_k_2859_, v_k_x27_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_unsigned_to_nat(1u);
v___x_2865_ = lean_nat_add(v_i_2858_, v___x_2864_);
lean_dec(v_i_2858_);
v_i_2858_ = v___x_2865_;
goto _start;
}
else
{
lean_dec(v_i_2858_);
return v___x_2861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg___boxed(lean_object* v_keys_2867_, lean_object* v_i_2868_, lean_object* v_k_2869_){
_start:
{
uint8_t v_res_2870_; lean_object* v_r_2871_; 
v_res_2870_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(v_keys_2867_, v_i_2868_, v_k_2869_);
lean_dec_ref(v_k_2869_);
lean_dec_ref(v_keys_2867_);
v_r_2871_ = lean_box(v_res_2870_);
return v_r_2871_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(lean_object* v_x_2872_, size_t v_x_2873_, lean_object* v_x_2874_){
_start:
{
if (lean_obj_tag(v_x_2872_) == 0)
{
lean_object* v_es_2875_; lean_object* v___x_2876_; size_t v___x_2877_; size_t v___x_2878_; lean_object* v_j_2879_; lean_object* v___x_2880_; 
v_es_2875_ = lean_ctor_get(v_x_2872_, 0);
v___x_2876_ = lean_box(2);
v___x_2877_ = ((size_t)31ULL);
v___x_2878_ = lean_usize_land(v_x_2873_, v___x_2877_);
v_j_2879_ = lean_usize_to_nat(v___x_2878_);
v___x_2880_ = lean_array_get_borrowed(v___x_2876_, v_es_2875_, v_j_2879_);
lean_dec(v_j_2879_);
switch(lean_obj_tag(v___x_2880_))
{
case 0:
{
lean_object* v_key_2881_; uint8_t v___x_2882_; 
v_key_2881_ = lean_ctor_get(v___x_2880_, 0);
v___x_2882_ = l_Lean_instBEqExtraModUse_beq(v_x_2874_, v_key_2881_);
return v___x_2882_;
}
case 1:
{
lean_object* v_node_2883_; size_t v___x_2884_; size_t v___x_2885_; 
v_node_2883_ = lean_ctor_get(v___x_2880_, 0);
v___x_2884_ = ((size_t)5ULL);
v___x_2885_ = lean_usize_shift_right(v_x_2873_, v___x_2884_);
v_x_2872_ = v_node_2883_;
v_x_2873_ = v___x_2885_;
goto _start;
}
default: 
{
uint8_t v___x_2887_; 
v___x_2887_ = 0;
return v___x_2887_;
}
}
}
else
{
lean_object* v_ks_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v_ks_2888_ = lean_ctor_get(v_x_2872_, 0);
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(v_ks_2888_, v___x_2889_, v_x_2874_);
return v___x_2890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_x_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_){
_start:
{
size_t v_x_90680__boxed_2894_; uint8_t v_res_2895_; lean_object* v_r_2896_; 
v_x_90680__boxed_2894_ = lean_unbox_usize(v_x_2892_);
lean_dec(v_x_2892_);
v_res_2895_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(v_x_2891_, v_x_90680__boxed_2894_, v_x_2893_);
lean_dec_ref(v_x_2893_);
lean_dec_ref(v_x_2891_);
v_r_2896_ = lean_box(v_res_2895_);
return v_r_2896_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(lean_object* v_x_2897_, lean_object* v_x_2898_){
_start:
{
uint64_t v___x_2899_; size_t v___x_2900_; uint8_t v___x_2901_; 
v___x_2899_ = l_Lean_instHashableExtraModUse_hash(v_x_2898_);
v___x_2900_ = lean_uint64_to_usize(v___x_2899_);
v___x_2901_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(v_x_2897_, v___x_2900_, v_x_2898_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg___boxed(lean_object* v_x_2902_, lean_object* v_x_2903_){
_start:
{
uint8_t v_res_2904_; lean_object* v_r_2905_; 
v_res_2904_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(v_x_2902_, v_x_2903_);
lean_dec_ref(v_x_2903_);
lean_dec_ref(v_x_2902_);
v_r_2905_ = lean_box(v_res_2904_);
return v_r_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___lam__0(lean_object* v___x_2906_, lean_object* v_entry_2907_, lean_object* v_s_2908_){
_start:
{
lean_object* v_addEntryFn_2909_; lean_object* v_importedEntries_2910_; lean_object* v_state_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2919_; 
v_addEntryFn_2909_ = lean_ctor_get(v___x_2906_, 3);
lean_inc(v_addEntryFn_2909_);
lean_dec_ref(v___x_2906_);
v_importedEntries_2910_ = lean_ctor_get(v_s_2908_, 0);
v_state_2911_ = lean_ctor_get(v_s_2908_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_s_2908_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2913_ = v_s_2908_;
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_state_2911_);
lean_inc(v_importedEntries_2910_);
lean_dec(v_s_2908_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v_state_2915_; lean_object* v___x_2917_; 
v_state_2915_ = lean_apply_2(v_addEntryFn_2909_, v_state_2911_, v_entry_2907_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v_state_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_importedEntries_2910_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_state_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0(void){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2920_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1(void){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1);
v___x_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
return v___x_2924_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3(void){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1);
v___x_2926_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
lean_ctor_set(v___x_2926_, 2, v___x_2925_);
lean_ctor_set(v___x_2926_, 3, v___x_2925_);
lean_ctor_set(v___x_2926_, 4, v___x_2925_);
lean_ctor_set(v___x_2926_, 5, v___x_2925_);
return v___x_2926_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4(void){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2927_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__7));
v___x_2933_ = l_Lean_stringToMessageData(v___x_2932_);
return v___x_2933_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__9));
v___x_2936_ = l_Lean_stringToMessageData(v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2938_ = l_Lean_stringToMessageData(v___x_2937_);
return v___x_2938_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14(void){
_start:
{
lean_object* v_cls_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v_cls_2942_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__6));
v___x_2943_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13));
v___x_2944_ = l_Lean_Name_append(v___x_2943_, v_cls_2942_);
return v___x_2944_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__15));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__17));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(lean_object* v_mod_2955_, uint8_t v_isMeta_2956_, lean_object* v_hint_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v_env_3000_; uint8_t v_isExporting_3001_; lean_object* v_entry_3002_; lean_object* v___x_3003_; lean_object* v_env_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_2998_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4);
v___x_2999_ = lean_st_ref_get(v___y_2964_);
v_env_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_env_3000_);
lean_dec(v___x_2999_);
v_isExporting_3001_ = lean_ctor_get_uint8(v_env_3000_, sizeof(void*)*13);
lean_dec_ref(v_env_3000_);
lean_inc(v_mod_2955_);
v_entry_3002_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3002_, 0, v_mod_2955_);
lean_ctor_set_uint8(v_entry_3002_, sizeof(void*)*1, v_isExporting_3001_);
lean_ctor_set_uint8(v_entry_3002_, sizeof(void*)*1 + 1, v_isMeta_2956_);
v___x_3003_ = lean_st_ref_get(v___y_2964_);
v_env_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc_ref(v_env_3004_);
lean_dec(v___x_3003_);
v___x_3005_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3006_ = lean_box(1);
v___x_3007_ = lean_box(0);
v___x_3008_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2998_, v___x_3005_, v_env_3004_, v___x_3006_, v___x_3007_);
v___x_3009_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(v___x_3008_, v_entry_3002_);
lean_dec(v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v_toCold_3010_; lean_object* v_options_3011_; lean_object* v_inheritedTraceOptions_3012_; uint8_t v_hasTrace_3013_; lean_object* v___f_3014_; uint8_t v___x_3015_; lean_object* v___y_3017_; lean_object* v___y_3018_; 
v_toCold_3010_ = lean_ctor_get(v___y_2963_, 0);
v_options_3011_ = lean_ctor_get(v_toCold_3010_, 2);
v_inheritedTraceOptions_3012_ = lean_ctor_get(v_toCold_3010_, 11);
v_hasTrace_3013_ = lean_ctor_get_uint8(v_options_3011_, sizeof(void*)*1);
v___f_3014_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___lam__0), 3, 2);
lean_closure_set(v___f_3014_, 0, v___x_3005_);
lean_closure_set(v___f_3014_, 1, v_entry_3002_);
v___x_3015_ = 1;
if (v_hasTrace_3013_ == 0)
{
lean_dec(v_hint_2957_);
lean_dec(v_mod_2955_);
v___y_3017_ = v___y_2962_;
v___y_3018_ = v___y_2964_;
goto v___jp_3016_;
}
else
{
lean_object* v_cls_3045_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v_cls_3045_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__6));
v___x_3065_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14);
v___x_3066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3012_, v_options_3011_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_dec(v_hint_2957_);
lean_dec(v_mod_2955_);
v___y_3017_ = v___y_2962_;
v___y_3018_ = v___y_2964_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3067_; lean_object* v___y_3069_; 
v___x_3067_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16);
if (v_isExporting_3001_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__21));
v___y_3069_ = v___x_3076_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3077_; 
v___x_3077_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__22));
v___y_3069_ = v___x_3077_;
goto v___jp_3068_;
}
v___jp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_inc_ref(v___y_3069_);
v___x_3070_ = l_Lean_stringToMessageData(v___y_3069_);
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3067_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18);
v___x_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3071_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
if (v_isMeta_2956_ == 0)
{
lean_object* v___x_3074_; 
v___x_3074_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__19));
v___y_3052_ = v___x_3073_;
v___y_3053_ = v___x_3074_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3075_; 
v___x_3075_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__20));
v___y_3052_ = v___x_3073_;
v___y_3053_ = v___x_3075_;
goto v___jp_3051_;
}
}
}
v___jp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___y_3047_);
lean_ctor_set(v___x_3049_, 1, v___y_3048_);
v___x_3050_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_3045_, v___x_3049_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_dec_ref_known(v___x_3050_, 1);
v___y_3017_ = v___y_2962_;
v___y_3018_ = v___y_2964_;
goto v___jp_3016_;
}
else
{
lean_dec_ref(v___f_3014_);
return v___x_3050_;
}
}
v___jp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
lean_inc_ref(v___y_3053_);
v___x_3054_ = l_Lean_stringToMessageData(v___y_3053_);
v___x_3055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___y_3052_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8);
v___x_3057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = l_Lean_MessageData_ofName(v_mod_2955_);
v___x_3059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = l_Lean_Name_isAnonymous(v_hint_2957_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10);
v___x_3062_ = l_Lean_MessageData_ofName(v_hint_2957_);
v___x_3063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3061_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___y_3047_ = v___x_3059_;
v___y_3048_ = v___x_3063_;
goto v___jp_3046_;
}
else
{
lean_object* v___x_3064_; 
lean_dec(v_hint_2957_);
v___x_3064_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11);
v___y_3047_ = v___x_3059_;
v___y_3048_ = v___x_3064_;
goto v___jp_3046_;
}
}
}
v___jp_3016_:
{
lean_object* v___x_3019_; lean_object* v_toEnvExtension_3020_; uint8_t v_logWrites_3021_; 
v___x_3019_ = lean_st_ref_take(v___y_3018_);
v_toEnvExtension_3020_ = lean_ctor_get(v___x_3005_, 0);
v_logWrites_3021_ = lean_ctor_get_uint8(v_toEnvExtension_3020_, sizeof(void*)*6);
if (v_logWrites_3021_ == 0)
{
lean_object* v_env_3022_; lean_object* v_nextMacroScope_3023_; lean_object* v_ngen_3024_; lean_object* v_auxDeclNGen_3025_; lean_object* v_traceState_3026_; lean_object* v_recordedDeps_3027_; lean_object* v_messages_3028_; lean_object* v_infoState_3029_; lean_object* v_snapshotTasks_3030_; lean_object* v_asyncMode_3031_; lean_object* v___x_3032_; 
v_env_3022_ = lean_ctor_get(v___x_3019_, 0);
lean_inc_ref(v_env_3022_);
v_nextMacroScope_3023_ = lean_ctor_get(v___x_3019_, 1);
lean_inc(v_nextMacroScope_3023_);
v_ngen_3024_ = lean_ctor_get(v___x_3019_, 2);
lean_inc_ref(v_ngen_3024_);
v_auxDeclNGen_3025_ = lean_ctor_get(v___x_3019_, 3);
lean_inc_ref(v_auxDeclNGen_3025_);
v_traceState_3026_ = lean_ctor_get(v___x_3019_, 4);
lean_inc_ref(v_traceState_3026_);
v_recordedDeps_3027_ = lean_ctor_get(v___x_3019_, 6);
lean_inc_ref(v_recordedDeps_3027_);
v_messages_3028_ = lean_ctor_get(v___x_3019_, 7);
lean_inc_ref(v_messages_3028_);
v_infoState_3029_ = lean_ctor_get(v___x_3019_, 8);
lean_inc_ref(v_infoState_3029_);
v_snapshotTasks_3030_ = lean_ctor_get(v___x_3019_, 9);
lean_inc_ref(v_snapshotTasks_3030_);
lean_dec(v___x_3019_);
v_asyncMode_3031_ = lean_ctor_get(v_toEnvExtension_3020_, 2);
lean_inc_ref(v_toEnvExtension_3020_);
v___x_3032_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3020_, v_env_3022_, v___f_3014_, v_asyncMode_3031_, v___x_3007_, v___x_3015_);
v___y_2967_ = v___y_3017_;
v___y_2968_ = v___y_3018_;
v___y_2969_ = v_infoState_3029_;
v___y_2970_ = v_snapshotTasks_3030_;
v___y_2971_ = v_ngen_3024_;
v___y_2972_ = v_nextMacroScope_3023_;
v___y_2973_ = v_messages_3028_;
v___y_2974_ = v_auxDeclNGen_3025_;
v___y_2975_ = v_recordedDeps_3027_;
v___y_2976_ = v_traceState_3026_;
v___y_2977_ = v___x_3032_;
goto v___jp_2966_;
}
else
{
lean_object* v_env_3033_; lean_object* v_nextMacroScope_3034_; lean_object* v_ngen_3035_; lean_object* v_auxDeclNGen_3036_; lean_object* v_traceState_3037_; lean_object* v_recordedDeps_3038_; lean_object* v_messages_3039_; lean_object* v_infoState_3040_; lean_object* v_snapshotTasks_3041_; lean_object* v_asyncMode_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_env_3033_ = lean_ctor_get(v___x_3019_, 0);
lean_inc_ref(v_env_3033_);
v_nextMacroScope_3034_ = lean_ctor_get(v___x_3019_, 1);
lean_inc(v_nextMacroScope_3034_);
v_ngen_3035_ = lean_ctor_get(v___x_3019_, 2);
lean_inc_ref(v_ngen_3035_);
v_auxDeclNGen_3036_ = lean_ctor_get(v___x_3019_, 3);
lean_inc_ref(v_auxDeclNGen_3036_);
v_traceState_3037_ = lean_ctor_get(v___x_3019_, 4);
lean_inc_ref(v_traceState_3037_);
v_recordedDeps_3038_ = lean_ctor_get(v___x_3019_, 6);
lean_inc_ref(v_recordedDeps_3038_);
v_messages_3039_ = lean_ctor_get(v___x_3019_, 7);
lean_inc_ref(v_messages_3039_);
v_infoState_3040_ = lean_ctor_get(v___x_3019_, 8);
lean_inc_ref(v_infoState_3040_);
v_snapshotTasks_3041_ = lean_ctor_get(v___x_3019_, 9);
lean_inc_ref(v_snapshotTasks_3041_);
lean_dec(v___x_3019_);
v_asyncMode_3042_ = lean_ctor_get(v_toEnvExtension_3020_, 2);
lean_inc_ref_n(v_toEnvExtension_3020_, 2);
v___x_3043_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3020_, v_env_3033_);
lean_dec_ref(v_env_3033_);
v___x_3044_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3020_, v___x_3043_, v___f_3014_, v_asyncMode_3042_, v___x_3007_, v___x_3015_);
v___y_2967_ = v___y_3017_;
v___y_2968_ = v___y_3018_;
v___y_2969_ = v_infoState_3040_;
v___y_2970_ = v_snapshotTasks_3041_;
v___y_2971_ = v_ngen_3035_;
v___y_2972_ = v_nextMacroScope_3034_;
v___y_2973_ = v_messages_3039_;
v___y_2974_ = v_auxDeclNGen_3036_;
v___y_2975_ = v_recordedDeps_3038_;
v___y_2976_ = v_traceState_3037_;
v___y_2977_ = v___x_3044_;
goto v___jp_2966_;
}
}
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec_ref_known(v_entry_3002_, 1);
lean_dec(v_hint_2957_);
lean_dec(v_mod_2955_);
v___x_3078_ = lean_box(0);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
v___jp_2966_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v_mctx_2982_; lean_object* v_zetaDeltaFVarIds_2983_; lean_object* v_postponed_2984_; lean_object* v_diag_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2996_; 
v___x_2978_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2);
v___x_2979_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2979_, 0, v___y_2977_);
lean_ctor_set(v___x_2979_, 1, v___y_2972_);
lean_ctor_set(v___x_2979_, 2, v___y_2971_);
lean_ctor_set(v___x_2979_, 3, v___y_2974_);
lean_ctor_set(v___x_2979_, 4, v___y_2976_);
lean_ctor_set(v___x_2979_, 5, v___x_2978_);
lean_ctor_set(v___x_2979_, 6, v___y_2975_);
lean_ctor_set(v___x_2979_, 7, v___y_2973_);
lean_ctor_set(v___x_2979_, 8, v___y_2969_);
lean_ctor_set(v___x_2979_, 9, v___y_2970_);
v___x_2980_ = lean_st_ref_put(v___y_2968_, v___x_2979_);
v___x_2981_ = lean_st_ref_take(v___y_2967_);
v_mctx_2982_ = lean_ctor_get(v___x_2981_, 0);
v_zetaDeltaFVarIds_2983_ = lean_ctor_get(v___x_2981_, 2);
v_postponed_2984_ = lean_ctor_get(v___x_2981_, 3);
v_diag_2985_ = lean_ctor_get(v___x_2981_, 4);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2996_ == 0)
{
lean_object* v_unused_2997_; 
v_unused_2997_ = lean_ctor_get(v___x_2981_, 1);
lean_dec(v_unused_2997_);
v___x_2987_ = v___x_2981_;
v_isShared_2988_ = v_isSharedCheck_2996_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_diag_2985_);
lean_inc(v_postponed_2984_);
lean_inc(v_zetaDeltaFVarIds_2983_);
lean_inc(v_mctx_2982_);
lean_dec(v___x_2981_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2996_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2989_ = lean_box(0);
v___x_2990_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 1, v___x_2990_);
v___x_2992_ = v___x_2987_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_mctx_2982_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___x_2990_);
lean_ctor_set(v_reuseFailAlloc_2995_, 2, v_zetaDeltaFVarIds_2983_);
lean_ctor_set(v_reuseFailAlloc_2995_, 3, v_postponed_2984_);
lean_ctor_set(v_reuseFailAlloc_2995_, 4, v_diag_2985_);
v___x_2992_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_st_ref_put(v___y_2967_, v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2989_);
return v___x_2994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___boxed(lean_object* v_mod_3080_, lean_object* v_isMeta_3081_, lean_object* v_hint_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
uint8_t v_isMeta_boxed_3091_; lean_object* v_res_3092_; 
v_isMeta_boxed_3091_ = lean_unbox(v_isMeta_3081_);
v_res_3092_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(v_mod_3080_, v_isMeta_boxed_3091_, v_hint_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec_ref(v___y_3083_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(lean_object* v___x_3093_, lean_object* v_declName_3094_, lean_object* v_as_3095_, size_t v_sz_3096_, size_t v_i_3097_, lean_object* v_b_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_usize_dec_lt(v_i_3097_, v_sz_3096_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
lean_dec(v_declName_3094_);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v_b_3098_);
return v___x_3108_;
}
else
{
lean_object* v___x_3109_; lean_object* v_modules_3110_; lean_object* v___x_3111_; lean_object* v_a_3112_; lean_object* v___x_3113_; lean_object* v_toImport_3114_; lean_object* v_module_3115_; lean_object* v___x_3116_; uint8_t v___x_3117_; lean_object* v___x_3118_; 
v___x_3109_ = l_Lean_Environment_header(v___x_3093_);
v_modules_3110_ = lean_ctor_get(v___x_3109_, 3);
lean_inc_ref(v_modules_3110_);
lean_dec_ref(v___x_3109_);
v___x_3111_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3112_ = lean_array_uget_borrowed(v_as_3095_, v_i_3097_);
v___x_3113_ = lean_array_get(v___x_3111_, v_modules_3110_, v_a_3112_);
lean_dec_ref(v_modules_3110_);
v_toImport_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc_ref(v_toImport_3114_);
lean_dec(v___x_3113_);
v_module_3115_ = lean_ctor_get(v_toImport_3114_, 0);
lean_inc(v_module_3115_);
lean_dec_ref(v_toImport_3114_);
v___x_3116_ = lean_box(0);
v___x_3117_ = 0;
lean_inc(v_declName_3094_);
v___x_3118_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(v_module_3115_, v___x_3117_, v_declName_3094_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
if (lean_obj_tag(v___x_3118_) == 0)
{
size_t v___x_3119_; size_t v___x_3120_; 
lean_dec_ref_known(v___x_3118_, 1);
v___x_3119_ = ((size_t)1ULL);
v___x_3120_ = lean_usize_add(v_i_3097_, v___x_3119_);
v_i_3097_ = v___x_3120_;
v_b_3098_ = v___x_3116_;
goto _start;
}
else
{
lean_dec(v_declName_3094_);
return v___x_3118_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17___boxed(lean_object* v___x_3122_, lean_object* v_declName_3123_, lean_object* v_as_3124_, lean_object* v_sz_3125_, lean_object* v_i_3126_, lean_object* v_b_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
size_t v_sz_boxed_3136_; size_t v_i_boxed_3137_; lean_object* v_res_3138_; 
v_sz_boxed_3136_ = lean_unbox_usize(v_sz_3125_);
lean_dec(v_sz_3125_);
v_i_boxed_3137_ = lean_unbox_usize(v_i_3126_);
lean_dec(v_i_3126_);
v_res_3138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(v___x_3122_, v_declName_3123_, v_as_3124_, v_sz_boxed_3136_, v_i_boxed_3137_, v_b_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec_ref(v_as_3124_);
lean_dec_ref(v___x_3122_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(lean_object* v_a_3139_, lean_object* v_x_3140_){
_start:
{
if (lean_obj_tag(v_x_3140_) == 0)
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_box(0);
return v___x_3141_;
}
else
{
lean_object* v_key_3142_; lean_object* v_value_3143_; lean_object* v_tail_3144_; uint8_t v___x_3145_; 
v_key_3142_ = lean_ctor_get(v_x_3140_, 0);
v_value_3143_ = lean_ctor_get(v_x_3140_, 1);
v_tail_3144_ = lean_ctor_get(v_x_3140_, 2);
v___x_3145_ = lean_name_eq(v_key_3142_, v_a_3139_);
if (v___x_3145_ == 0)
{
v_x_3140_ = v_tail_3144_;
goto _start;
}
else
{
lean_object* v___x_3147_; 
lean_inc(v_value_3143_);
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_value_3143_);
return v___x_3147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg___boxed(lean_object* v_a_3148_, lean_object* v_x_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(v_a_3148_, v_x_3149_);
lean_dec(v_x_3149_);
lean_dec(v_a_3148_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(lean_object* v_m_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_buckets_3153_; lean_object* v___x_3154_; uint64_t v___y_3156_; 
v_buckets_3153_ = lean_ctor_get(v_m_3151_, 1);
v___x_3154_ = lean_array_get_size(v_buckets_3153_);
if (lean_obj_tag(v_a_3152_) == 0)
{
uint64_t v___x_3170_; 
v___x_3170_ = 1723ULL;
v___y_3156_ = v___x_3170_;
goto v___jp_3155_;
}
else
{
uint64_t v_hash_3171_; 
v_hash_3171_ = lean_ctor_get_uint64(v_a_3152_, sizeof(void*)*2);
v___y_3156_ = v_hash_3171_;
goto v___jp_3155_;
}
v___jp_3155_:
{
uint64_t v___x_3157_; uint64_t v___x_3158_; uint64_t v_fold_3159_; uint64_t v___x_3160_; uint64_t v___x_3161_; uint64_t v___x_3162_; size_t v___x_3163_; size_t v___x_3164_; size_t v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3157_ = 32ULL;
v___x_3158_ = lean_uint64_shift_right(v___y_3156_, v___x_3157_);
v_fold_3159_ = lean_uint64_xor(v___y_3156_, v___x_3158_);
v___x_3160_ = 16ULL;
v___x_3161_ = lean_uint64_shift_right(v_fold_3159_, v___x_3160_);
v___x_3162_ = lean_uint64_xor(v_fold_3159_, v___x_3161_);
v___x_3163_ = lean_uint64_to_usize(v___x_3162_);
v___x_3164_ = lean_usize_of_nat(v___x_3154_);
v___x_3165_ = ((size_t)1ULL);
v___x_3166_ = lean_usize_sub(v___x_3164_, v___x_3165_);
v___x_3167_ = lean_usize_land(v___x_3163_, v___x_3166_);
v___x_3168_ = lean_array_uget_borrowed(v_buckets_3153_, v___x_3167_);
v___x_3169_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(v_a_3152_, v___x_3168_);
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg___boxed(lean_object* v_m_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(v_m_3172_, v_a_3173_);
lean_dec(v_a_3173_);
lean_dec_ref(v_m_3172_);
return v_res_3174_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Std_HashMap_instInhabited___redArg();
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(lean_object* v_declName_3178_, uint8_t v_isMeta_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v_env_3193_; lean_object* v___y_3195_; lean_object* v___x_3208_; 
v___x_3188_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0);
v___x_3189_ = lean_st_ref_get(v___y_3186_);
v_env_3193_ = lean_ctor_get(v___x_3189_, 0);
lean_inc_ref(v_env_3193_);
lean_dec(v___x_3189_);
v___x_3208_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3193_, v_declName_3178_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_dec_ref(v_env_3193_);
lean_dec(v_declName_3178_);
goto v___jp_3190_;
}
else
{
lean_object* v_val_3209_; lean_object* v___x_3210_; lean_object* v_modules_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v_val_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_val_3209_);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = l_Lean_Environment_header(v_env_3193_);
v_modules_3211_ = lean_ctor_get(v___x_3210_, 3);
lean_inc_ref(v_modules_3211_);
lean_dec_ref(v___x_3210_);
v___x_3212_ = lean_array_get_size(v_modules_3211_);
v___x_3213_ = lean_nat_dec_lt(v_val_3209_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_dec_ref(v_modules_3211_);
lean_dec(v_val_3209_);
lean_dec_ref(v_env_3193_);
lean_dec(v_declName_3178_);
goto v___jp_3190_;
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; uint8_t v___y_3217_; 
v___x_3214_ = lean_array_fget(v_modules_3211_, v_val_3209_);
lean_dec(v_val_3209_);
lean_dec_ref(v_modules_3211_);
v___x_3215_ = lean_st_ref_get(v___y_3186_);
if (v_isMeta_3179_ == 0)
{
lean_dec(v___x_3215_);
v___y_3217_ = v_isMeta_3179_;
goto v___jp_3216_;
}
else
{
lean_object* v_env_3228_; uint8_t v___x_3229_; 
v_env_3228_ = lean_ctor_get(v___x_3215_, 0);
lean_inc_ref(v_env_3228_);
lean_dec(v___x_3215_);
lean_inc(v_declName_3178_);
v___x_3229_ = l_Lean_isMarkedMeta(v_env_3228_, v_declName_3178_);
if (v___x_3229_ == 0)
{
v___y_3217_ = v_isMeta_3179_;
goto v___jp_3216_;
}
else
{
uint8_t v___x_3230_; 
v___x_3230_ = 0;
v___y_3217_ = v___x_3230_;
goto v___jp_3216_;
}
}
v___jp_3216_:
{
lean_object* v_toImport_3218_; lean_object* v_module_3219_; lean_object* v___x_3220_; 
v_toImport_3218_ = lean_ctor_get(v___x_3214_, 0);
lean_inc_ref(v_toImport_3218_);
lean_dec(v___x_3214_);
v_module_3219_ = lean_ctor_get(v_toImport_3218_, 0);
lean_inc(v_module_3219_);
lean_dec_ref(v_toImport_3218_);
lean_inc(v_declName_3178_);
v___x_3220_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(v_module_3219_, v___y_3217_, v_declName_3178_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec_ref_known(v___x_3220_, 1);
v___x_3221_ = l_Lean_indirectModUseExt;
v___x_3222_ = lean_box(1);
v___x_3223_ = lean_box(0);
lean_inc_ref(v_env_3193_);
v___x_3224_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3188_, v___x_3221_, v_env_3193_, v___x_3222_, v___x_3223_);
v___x_3225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(v___x_3224_, v_declName_3178_);
lean_dec(v___x_3224_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v___x_3226_; 
v___x_3226_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__1));
v___y_3195_ = v___x_3226_;
goto v___jp_3194_;
}
else
{
lean_object* v_val_3227_; 
v_val_3227_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_val_3227_);
lean_dec_ref_known(v___x_3225_, 1);
v___y_3195_ = v_val_3227_;
goto v___jp_3194_;
}
}
else
{
lean_dec_ref(v_env_3193_);
lean_dec(v_declName_3178_);
return v___x_3220_;
}
}
}
}
v___jp_3190_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_box(0);
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
return v___x_3192_;
}
v___jp_3194_:
{
lean_object* v___x_3196_; size_t v_sz_3197_; size_t v___x_3198_; lean_object* v___x_3199_; 
v___x_3196_ = lean_box(0);
v_sz_3197_ = lean_array_size(v___y_3195_);
v___x_3198_ = ((size_t)0ULL);
v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(v_env_3193_, v_declName_3178_, v___y_3195_, v_sz_3197_, v___x_3198_, v___x_3196_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec_ref(v___y_3195_);
lean_dec_ref(v_env_3193_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v___x_3199_, 0);
lean_dec(v_unused_3207_);
v___x_3201_ = v___x_3199_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_dec(v___x_3199_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3196_);
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3196_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
else
{
return v___x_3199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___boxed(lean_object* v_declName_3231_, lean_object* v_isMeta_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
uint8_t v_isMeta_boxed_3241_; lean_object* v_res_3242_; 
v_isMeta_boxed_3241_ = lean_unbox(v_isMeta_3232_);
v_res_3242_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(v_declName_3231_, v_isMeta_boxed_3241_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(lean_object* v_as_x27_3243_, lean_object* v_b_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
if (lean_obj_tag(v_as_x27_3243_) == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v_b_3244_);
return v___x_3253_;
}
else
{
lean_object* v_head_3254_; lean_object* v_tail_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; 
v_head_3254_ = lean_ctor_get(v_as_x27_3243_, 0);
v_tail_3255_ = lean_ctor_get(v_as_x27_3243_, 1);
v___x_3256_ = lean_box(0);
v___x_3257_ = 1;
lean_inc(v_head_3254_);
v___x_3258_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(v_head_3254_, v___x_3257_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_dec_ref_known(v___x_3258_, 1);
v_as_x27_3243_ = v_tail_3255_;
v_b_3244_ = v___x_3256_;
goto _start;
}
else
{
return v___x_3258_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg___boxed(lean_object* v_as_x27_3260_, lean_object* v_b_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(v_as_x27_3260_, v_b_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v_as_x27_3260_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(lean_object* v_env_3271_, lean_object* v___x_3272_, lean_object* v_currNamespace_3273_, lean_object* v_openDecls_3274_, lean_object* v_n_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = l_Lean_ResolveName_resolveGlobalName(v_env_3271_, v___x_3272_, v_currNamespace_3273_, v_openDecls_3274_, v_n_3275_);
v___x_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v___y_3277_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed(lean_object* v_env_3280_, lean_object* v___x_3281_, lean_object* v_currNamespace_3282_, lean_object* v_openDecls_3283_, lean_object* v_n_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(v_env_3280_, v___x_3281_, v_currNamespace_3282_, v_openDecls_3283_, v_n_3284_, v___y_3285_, v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec_ref(v___x_3281_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(lean_object* v_as_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
if (lean_obj_tag(v_as_3288_) == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
else
{
lean_object* v_toCold_3299_; lean_object* v_options_3300_; uint8_t v_hasTrace_3301_; 
v_toCold_3299_ = lean_ctor_get(v___y_3294_, 0);
v_options_3300_ = lean_ctor_get(v_toCold_3299_, 2);
v_hasTrace_3301_ = lean_ctor_get_uint8(v_options_3300_, sizeof(void*)*1);
if (v_hasTrace_3301_ == 0)
{
lean_object* v_tail_3302_; 
v_tail_3302_ = lean_ctor_get(v_as_3288_, 1);
lean_inc(v_tail_3302_);
lean_dec_ref_known(v_as_3288_, 2);
v_as_3288_ = v_tail_3302_;
goto _start;
}
else
{
lean_object* v_head_3304_; lean_object* v_tail_3305_; lean_object* v_fst_3306_; lean_object* v_snd_3307_; lean_object* v_inheritedTraceOptions_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v_head_3304_ = lean_ctor_get(v_as_3288_, 0);
lean_inc(v_head_3304_);
v_tail_3305_ = lean_ctor_get(v_as_3288_, 1);
lean_inc(v_tail_3305_);
lean_dec_ref_known(v_as_3288_, 2);
v_fst_3306_ = lean_ctor_get(v_head_3304_, 0);
lean_inc_n(v_fst_3306_, 2);
v_snd_3307_ = lean_ctor_get(v_head_3304_, 1);
lean_inc(v_snd_3307_);
lean_dec(v_head_3304_);
v_inheritedTraceOptions_3308_ = lean_ctor_get(v_toCold_3299_, 11);
v___x_3309_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13));
v___x_3310_ = l_Lean_Name_append(v___x_3309_, v_fst_3306_);
v___x_3311_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3308_, v_options_3300_, v___x_3310_);
lean_dec(v___x_3310_);
if (v___x_3311_ == 0)
{
lean_dec(v_snd_3307_);
lean_dec(v_fst_3306_);
v_as_3288_ = v_tail_3305_;
goto _start;
}
else
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3313_, 0, v_snd_3307_);
v___x_3314_ = l_Lean_MessageData_ofFormat(v___x_3313_);
v___x_3315_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_fst_3306_, v___x_3314_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_dec_ref_known(v___x_3315_, 1);
v_as_3288_ = v_tail_3305_;
goto _start;
}
else
{
lean_dec(v_tail_3305_);
return v___x_3315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___boxed(lean_object* v_as_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(v_as_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v___y_3318_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(lean_object* v_x_3327_, lean_object* v___y_3328_){
_start:
{
if (lean_obj_tag(v_x_3327_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3330_; 
v_a_3329_ = lean_ctor_get(v_x_3327_, 0);
lean_inc(v_a_3329_);
v___x_3330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3330_, 0, v_a_3329_);
lean_ctor_set(v___x_3330_, 1, v___y_3328_);
return v___x_3330_;
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3332_; 
v_a_3331_ = lean_ctor_get(v_x_3327_, 0);
lean_inc(v_a_3331_);
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v_a_3331_);
lean_ctor_set(v___x_3332_, 1, v___y_3328_);
return v___x_3332_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg___boxed(lean_object* v_x_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v_x_3333_, v___y_3334_);
lean_dec_ref(v_x_3333_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(lean_object* v_env_3336_, lean_object* v_stx_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_3336_, v_stx_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
if (lean_obj_tag(v_a_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3350_; 
v_a_3342_ = lean_ctor_get(v___x_3340_, 1);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; 
v_unused_3351_ = lean_ctor_get(v___x_3340_, 0);
lean_dec(v_unused_3351_);
v___x_3344_ = v___x_3340_;
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3340_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = lean_box(0);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3346_);
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_a_3342_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
else
{
lean_object* v_val_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3380_; 
v_val_3352_ = lean_ctor_get(v_a_3341_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_a_3341_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3354_ = v_a_3341_;
v_isShared_3355_ = v_isSharedCheck_3380_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_val_3352_);
lean_dec(v_a_3341_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3380_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v_snd_3356_; 
v_snd_3356_ = lean_ctor_get(v_val_3352_, 1);
lean_inc(v_snd_3356_);
lean_dec(v_val_3352_);
if (lean_obj_tag(v_snd_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3366_; 
lean_del_object(v___x_3354_);
v_a_3357_ = lean_ctor_get(v___x_3340_, 1);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3340_, 2);
v_a_3358_ = lean_ctor_get(v_snd_3356_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v_snd_3356_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3360_ = v_snd_3356_;
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v_snd_3356_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v___x_3363_, v_a_3357_);
lean_dec_ref(v___x_3363_);
return v___x_3364_;
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3379_; 
v_a_3367_ = lean_ctor_get(v___x_3340_, 1);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3340_, 2);
v_a_3368_ = lean_ctor_get(v_snd_3356_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_snd_3356_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3370_ = v_snd_3356_;
v_isShared_3371_ = v_isSharedCheck_3379_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v_snd_3356_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3379_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v_a_3368_);
v___x_3373_ = v___x_3354_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3373_);
v___x_3375_ = v___x_3370_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v___x_3375_, v_a_3367_);
lean_dec_ref(v___x_3375_);
return v___x_3376_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
v_a_3381_ = lean_ctor_get(v___x_3340_, 0);
v_a_3382_ = lean_ctor_get(v___x_3340_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3340_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_inc(v_a_3381_);
lean_dec(v___x_3340_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3381_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed(lean_object* v_env_3390_, lean_object* v_stx_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(v_env_3390_, v_stx_3391_, v___y_3392_, v___y_3393_);
lean_dec_ref(v___y_3392_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; lean_object* v_toCold_3406_; lean_object* v_env_3407_; lean_object* v_currRecDepth_3408_; lean_object* v_ref_3409_; lean_object* v_maxRecDepth_3410_; lean_object* v_currNamespace_3411_; lean_object* v_openDecls_3412_; lean_object* v_quotContext_3413_; lean_object* v_currMacroScope_3414_; lean_object* v___f_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; lean_object* v___f_3418_; lean_object* v___f_3419_; lean_object* v___f_3420_; lean_object* v_methods_3421_; lean_object* v___x_3422_; lean_object* v_nextMacroScope_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3405_ = lean_st_ref_get(v___y_3403_);
v_toCold_3406_ = lean_ctor_get(v___y_3402_, 0);
v_env_3407_ = lean_ctor_get(v___x_3405_, 0);
lean_inc_ref_n(v_env_3407_, 4);
lean_dec(v___x_3405_);
v_currRecDepth_3408_ = lean_ctor_get(v___y_3402_, 1);
v_ref_3409_ = lean_ctor_get(v___y_3402_, 2);
v_maxRecDepth_3410_ = lean_ctor_get(v_toCold_3406_, 3);
v_currNamespace_3411_ = lean_ctor_get(v_toCold_3406_, 4);
v_openDecls_3412_ = lean_ctor_get(v_toCold_3406_, 5);
v_quotContext_3413_ = lean_ctor_get(v_toCold_3406_, 8);
v_currMacroScope_3414_ = lean_ctor_get(v_toCold_3406_, 9);
v___f_3415_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3415_, 0, v_env_3407_);
v___f_3416_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3416_, 0, v_env_3407_);
v___x_3417_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3402_);
lean_inc_n(v_currNamespace_3411_, 3);
v___f_3418_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3418_, 0, v_currNamespace_3411_);
lean_inc_n(v_openDecls_3412_, 2);
v___f_3419_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_3419_, 0, v_env_3407_);
lean_closure_set(v___f_3419_, 1, v___x_3417_);
lean_closure_set(v___f_3419_, 2, v_currNamespace_3411_);
lean_closure_set(v___f_3419_, 3, v_openDecls_3412_);
v___f_3420_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_3420_, 0, v_env_3407_);
lean_closure_set(v___f_3420_, 1, v_currNamespace_3411_);
lean_closure_set(v___f_3420_, 2, v_openDecls_3412_);
v_methods_3421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3421_, 0, v___f_3416_);
lean_ctor_set(v_methods_3421_, 1, v___f_3418_);
lean_ctor_set(v_methods_3421_, 2, v___f_3415_);
lean_ctor_set(v_methods_3421_, 3, v___f_3420_);
lean_ctor_set(v_methods_3421_, 4, v___f_3419_);
v___x_3422_ = lean_st_ref_get(v___y_3403_);
v_nextMacroScope_3423_ = lean_ctor_get(v___x_3422_, 1);
lean_inc(v_nextMacroScope_3423_);
lean_dec(v___x_3422_);
lean_inc(v_ref_3409_);
lean_inc(v_maxRecDepth_3410_);
lean_inc(v_currRecDepth_3408_);
lean_inc(v_currMacroScope_3414_);
lean_inc(v_quotContext_3413_);
v___x_3424_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3424_, 0, v_methods_3421_);
lean_ctor_set(v___x_3424_, 1, v_quotContext_3413_);
lean_ctor_set(v___x_3424_, 2, v_currMacroScope_3414_);
lean_ctor_set(v___x_3424_, 3, v_currRecDepth_3408_);
lean_ctor_set(v___x_3424_, 4, v_maxRecDepth_3410_);
lean_ctor_set(v___x_3424_, 5, v_ref_3409_);
v___x_3425_ = lean_box(0);
v___x_3426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3426_, 0, v_nextMacroScope_3423_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
lean_ctor_set(v___x_3426_, 2, v___x_3425_);
v___x_3427_ = lean_apply_2(v_x_3396_, v___x_3424_, v___x_3426_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v_a_3429_; lean_object* v_macroScope_3430_; lean_object* v_traceMsgs_3431_; lean_object* v_expandedMacroDecls_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 1);
lean_inc(v_a_3428_);
v_a_3429_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3427_, 2);
v_macroScope_3430_ = lean_ctor_get(v_a_3428_, 0);
lean_inc(v_macroScope_3430_);
v_traceMsgs_3431_ = lean_ctor_get(v_a_3428_, 1);
lean_inc(v_traceMsgs_3431_);
v_expandedMacroDecls_3432_ = lean_ctor_get(v_a_3428_, 2);
lean_inc(v_expandedMacroDecls_3432_);
lean_dec(v_a_3428_);
v___x_3433_ = lean_box(0);
v___x_3434_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(v_expandedMacroDecls_3432_, v___x_3433_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v_expandedMacroDecls_3432_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v___x_3435_; lean_object* v_env_3436_; lean_object* v_ngen_3437_; lean_object* v_auxDeclNGen_3438_; lean_object* v_traceState_3439_; lean_object* v_cache_3440_; lean_object* v_recordedDeps_3441_; lean_object* v_messages_3442_; lean_object* v_infoState_3443_; lean_object* v_snapshotTasks_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref_known(v___x_3434_, 1);
v___x_3435_ = lean_st_ref_take(v___y_3403_);
v_env_3436_ = lean_ctor_get(v___x_3435_, 0);
v_ngen_3437_ = lean_ctor_get(v___x_3435_, 2);
v_auxDeclNGen_3438_ = lean_ctor_get(v___x_3435_, 3);
v_traceState_3439_ = lean_ctor_get(v___x_3435_, 4);
v_cache_3440_ = lean_ctor_get(v___x_3435_, 5);
v_recordedDeps_3441_ = lean_ctor_get(v___x_3435_, 6);
v_messages_3442_ = lean_ctor_get(v___x_3435_, 7);
v_infoState_3443_ = lean_ctor_get(v___x_3435_, 8);
v_snapshotTasks_3444_ = lean_ctor_get(v___x_3435_, 9);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; 
v_unused_3471_ = lean_ctor_get(v___x_3435_, 1);
lean_dec(v_unused_3471_);
v___x_3446_ = v___x_3435_;
v_isShared_3447_ = v_isSharedCheck_3470_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_snapshotTasks_3444_);
lean_inc(v_infoState_3443_);
lean_inc(v_messages_3442_);
lean_inc(v_recordedDeps_3441_);
lean_inc(v_cache_3440_);
lean_inc(v_traceState_3439_);
lean_inc(v_auxDeclNGen_3438_);
lean_inc(v_ngen_3437_);
lean_inc(v_env_3436_);
lean_dec(v___x_3435_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3470_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v_macroScope_3430_);
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_env_3436_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_macroScope_3430_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_ngen_3437_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v_auxDeclNGen_3438_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_traceState_3439_);
lean_ctor_set(v_reuseFailAlloc_3469_, 5, v_cache_3440_);
lean_ctor_set(v_reuseFailAlloc_3469_, 6, v_recordedDeps_3441_);
lean_ctor_set(v_reuseFailAlloc_3469_, 7, v_messages_3442_);
lean_ctor_set(v_reuseFailAlloc_3469_, 8, v_infoState_3443_);
lean_ctor_set(v_reuseFailAlloc_3469_, 9, v_snapshotTasks_3444_);
v___x_3449_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = lean_st_ref_put(v___y_3403_, v___x_3449_);
v___x_3451_ = l_List_reverse___redArg(v_traceMsgs_3431_);
v___x_3452_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(v___x_3451_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; 
v_unused_3460_ = lean_ctor_get(v___x_3452_, 0);
lean_dec(v_unused_3460_);
v___x_3454_ = v___x_3452_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_dec(v___x_3452_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v_a_3429_);
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3429_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_a_3429_);
v_a_3461_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3452_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3452_);
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
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec(v_traceMsgs_3431_);
lean_dec(v_macroScope_3430_);
lean_dec(v_a_3429_);
v_a_3472_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3434_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3434_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v_a_3480_; 
v_a_3480_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3427_, 2);
if (lean_obj_tag(v_a_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v_a_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v_a_3481_ = lean_ctor_get(v_a_3480_, 0);
lean_inc(v_a_3481_);
v_a_3482_ = lean_ctor_get(v_a_3480_, 1);
lean_inc_ref(v_a_3482_);
lean_dec_ref_known(v_a_3480_, 2);
v___x_3483_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___closed__0));
v___x_3484_ = lean_string_dec_eq(v_a_3482_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3485_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3485_, 0, v_a_3482_);
v___x_3486_ = l_Lean_MessageData_ofFormat(v___x_3485_);
v___x_3487_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_a_3481_, v___x_3486_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v_a_3481_);
return v___x_3487_;
}
else
{
lean_object* v___x_3488_; 
lean_dec_ref(v_a_3482_);
v___x_3488_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(v_a_3481_);
return v___x_3488_;
}
}
else
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_x_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec_ref(v___y_3491_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(lean_object* v___x_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_toCold_3504_; lean_object* v_quotContext_3505_; lean_object* v_currMacroScope_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v_toCold_3504_ = lean_ctor_get(v___y_3501_, 0);
lean_inc_ref(v_toCold_3504_);
lean_dec_ref(v___y_3501_);
v_quotContext_3505_ = lean_ctor_get(v_toCold_3504_, 8);
lean_inc(v_quotContext_3505_);
v_currMacroScope_3506_ = lean_ctor_get(v_toCold_3504_, 9);
lean_inc(v_currMacroScope_3506_);
lean_dec_ref(v_toCold_3504_);
v___x_3507_ = l_Lean_addMacroScope(v_quotContext_3505_, v___x_3500_, v_currMacroScope_3506_);
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v___x_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(v___x_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___f_3522_; lean_object* v___x_3523_; 
v___f_3522_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__2));
v___x_3523_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3522_, v___y_3519_, v___y_3520_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___boxed(lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_ref_3528_, uint8_t v_canonical_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3535_, v___y_3536_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3547_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3543_ = l_Lean_mkIdentFrom(v_ref_3528_, v_a_3539_, v_canonical_3529_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3543_);
v___x_3545_ = v___x_3541_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3538_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3538_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_ref_3556_, lean_object* v_canonical_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
uint8_t v_canonical_boxed_3566_; lean_object* v_res_3567_; 
v_canonical_boxed_3566_ = lean_unbox(v_canonical_3557_);
v_res_3567_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_ref_3556_, v_canonical_boxed_3566_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v_ref_3556_);
return v_res_3567_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__0));
v___x_3570_ = l_Lean_stringToMessageData(v___x_3569_);
return v___x_3570_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3576_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3577_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13));
v___x_3578_ = l_Lean_Name_append(v___x_3577_, v___x_3576_);
return v___x_3578_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3581_ = l_Lean_stringToMessageData(v___x_3580_);
return v___x_3581_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3584_ = l_Lean_stringToMessageData(v___x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3591_, lean_object* v_letOrReassign_3592_, lean_object* v_decl_3593_, lean_object* v_tk_3594_, lean_object* v_dec_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3591_, v_letOrReassign_3592_, v_decl_3593_, v_tk_3594_, v_dec_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec_ref(v_a_3596_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3605_, lean_object* v_letOrReassign_3606_, lean_object* v_decl_3607_, lean_object* v_tk_3608_, lean_object* v_dec_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_config_3605_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v___x_3619_; 
lean_dec_ref_known(v___x_3618_, 1);
lean_inc(v_decl_3607_);
v___x_3619_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3607_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; lean_object* v___x_3621_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3619_, 1);
v___x_3621_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3606_, v_a_3620_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v___x_3622_; 
lean_dec_ref_known(v___x_3621_, 1);
v___x_3622_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3609_, v_tk_3608_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; uint8_t v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; uint8_t v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v_rhs_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; uint8_t v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; uint8_t v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; uint8_t v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v_xType_x3f_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; uint8_t v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; uint8_t v___y_3725_; lean_object* v___y_3726_; uint8_t v___y_3727_; lean_object* v___y_3728_; uint8_t v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; uint8_t v___y_3740_; uint8_t v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; uint8_t v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; uint8_t v___y_3805_; uint8_t v___y_3806_; lean_object* v_id_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; uint8_t v___y_3826_; lean_object* v___y_3827_; uint8_t v___y_3828_; lean_object* v___y_3829_; uint8_t v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; uint8_t v___y_3838_; lean_object* v_decl_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___x_3925_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
v___x_3925_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_3606_, v_a_3620_, v_a_3610_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3927_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref_known(v___x_3925_, 1);
v___x_3927_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3606_, v_decl_3607_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
if (lean_obj_tag(v___x_3927_) == 0)
{
uint8_t v___x_3928_; 
v___x_3928_ = lean_unbox(v_a_3926_);
lean_dec(v_a_3926_);
if (v___x_3928_ == 0)
{
lean_object* v_a_3929_; 
v_a_3929_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3927_, 1);
v_decl_3856_ = v_a_3929_;
v___y_3857_ = v_a_3610_;
v___y_3858_ = v_a_3611_;
v___y_3859_ = v_a_3612_;
v___y_3860_ = v_a_3613_;
v___y_3861_ = v_a_3614_;
v___y_3862_ = v_a_3615_;
v___y_3863_ = v_a_3616_;
goto v___jp_3855_;
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3931_; 
v_a_3930_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3927_, 1);
v___x_3931_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(v_a_3930_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v_decl_3856_ = v_a_3932_;
v___y_3857_ = v_a_3610_;
v___y_3858_ = v_a_3611_;
v___y_3859_ = v_a_3612_;
v___y_3860_ = v_a_3613_;
v___y_3861_ = v_a_3614_;
v___y_3862_ = v_a_3615_;
v___y_3863_ = v_a_3616_;
goto v___jp_3855_;
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_tk_3608_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v_a_3933_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3931_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3931_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec(v_a_3926_);
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_tk_3608_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v_a_3941_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3927_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3927_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_tk_3608_);
lean_dec(v_decl_3607_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v_a_3949_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3925_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3925_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
v___jp_3624_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___f_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3642_ = lean_box(v___y_3628_);
v___x_3643_ = lean_box(v___y_3631_);
lean_inc_ref(v___y_3632_);
lean_inc_ref(v___y_3630_);
lean_inc_ref(v___y_3627_);
v___f_3644_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 19, 10);
lean_closure_set(v___f_3644_, 0, v_rhs_3634_);
lean_closure_set(v___f_3644_, 1, v___x_3642_);
lean_closure_set(v___f_3644_, 2, v_config_3605_);
lean_closure_set(v___f_3644_, 3, v___y_3629_);
lean_closure_set(v___f_3644_, 4, v___x_3643_);
lean_closure_set(v___f_3644_, 5, v___y_3627_);
lean_closure_set(v___f_3644_, 6, v___y_3630_);
lean_closure_set(v___f_3644_, 7, v___y_3632_);
lean_closure_set(v___f_3644_, 8, v___y_3625_);
lean_closure_set(v___f_3644_, 9, v___y_3626_);
v___x_3645_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3645_, 0, v_a_3623_);
v___x_3646_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3646_, 0, v_letOrReassign_3606_);
lean_closure_set(v___x_3646_, 1, v_a_3620_);
lean_closure_set(v___x_3646_, 2, v___x_3645_);
v___x_3647_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1);
v___x_3648_ = l_Lean_MessageData_ofSyntax(v___y_3633_);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_box(0);
v___x_3651_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3649_, v___x_3646_, v___f_3644_, v___x_3650_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
return v___x_3651_;
}
v___jp_3652_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = lean_unsigned_to_nat(4u);
v___x_3675_ = l_Lean_Syntax_getArg(v___y_3662_, v___x_3674_);
lean_dec(v___y_3662_);
if (lean_obj_tag(v_xType_x3f_3666_) == 0)
{
lean_inc(v___y_3654_);
v___y_3625_ = v___y_3653_;
v___y_3626_ = v___y_3654_;
v___y_3627_ = v___y_3655_;
v___y_3628_ = v___y_3656_;
v___y_3629_ = v___y_3657_;
v___y_3630_ = v___y_3658_;
v___y_3631_ = v___y_3659_;
v___y_3632_ = v___y_3660_;
v___y_3633_ = v___y_3654_;
v_rhs_3634_ = v___x_3675_;
v___y_3635_ = v___y_3667_;
v___y_3636_ = v___y_3668_;
v___y_3637_ = v___y_3669_;
v___y_3638_ = v___y_3670_;
v___y_3639_ = v___y_3671_;
v___y_3640_ = v___y_3672_;
v___y_3641_ = v___y_3673_;
goto v___jp_3624_;
}
else
{
lean_object* v_toCold_3676_; lean_object* v_val_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3720_; 
v_toCold_3676_ = lean_ctor_get(v___y_3672_, 0);
v_val_3677_ = lean_ctor_get(v_xType_x3f_3666_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_xType_x3f_3666_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3679_ = v_xType_x3f_3666_;
v_isShared_3680_ = v_isSharedCheck_3720_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_val_3677_);
lean_dec(v_xType_x3f_3666_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3720_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v_ref_3681_; lean_object* v_quotContext_3682_; lean_object* v_currMacroScope_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3699_; 
v_ref_3681_ = lean_ctor_get(v___y_3672_, 2);
v_quotContext_3682_ = lean_ctor_get(v_toCold_3676_, 8);
v_currMacroScope_3683_ = lean_ctor_get(v_toCold_3676_, 9);
v___x_3684_ = l_Lean_SourceInfo_fromRef(v_ref_3681_, v___y_3663_);
v___x_3685_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__15));
lean_inc_ref_n(v___y_3665_, 2);
lean_inc_ref_n(v___y_3664_, 2);
lean_inc_ref_n(v___y_3661_, 3);
v___x_3686_ = l_Lean_Name_mkStr4(v___y_3661_, v___y_3664_, v___y_3665_, v___x_3685_);
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__17));
v___x_3688_ = l_Lean_Name_mkStr4(v___y_3661_, v___y_3664_, v___y_3665_, v___x_3687_);
v___x_3689_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_3684_);
v___x_3690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3684_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3692_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3693_ = lean_box(0);
lean_inc(v_currMacroScope_3683_);
lean_inc(v_quotContext_3682_);
v___x_3694_ = l_Lean_addMacroScope(v_quotContext_3682_, v___x_3693_, v_currMacroScope_3683_);
v___x_3695_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24));
v___x_3696_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25));
v___x_3697_ = l_Lean_Name_mkStr3(v___y_3661_, v___x_3695_, v___x_3696_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set_tag(v___x_3679_, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3697_);
v___x_3699_ = v___x_3679_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3700_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__28));
lean_inc_ref_n(v___y_3661_, 2);
v___x_3701_ = l_Lean_Name_mkStr2(v___y_3661_, v___x_3700_);
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
lean_inc_ref(v___y_3665_);
lean_inc_ref(v___y_3664_);
v___x_3703_ = l_Lean_Name_mkStr3(v___y_3661_, v___y_3664_, v___y_3665_);
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
v___x_3705_ = lean_box(0);
v___x_3706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3704_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3702_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3699_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
lean_inc_n(v___x_3684_, 6);
v___x_3709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3684_);
lean_ctor_set(v___x_3709_, 1, v___x_3692_);
lean_ctor_set(v___x_3709_, 2, v___x_3694_);
lean_ctor_set(v___x_3709_, 3, v___x_3708_);
v___x_3710_ = l_Lean_Syntax_node1(v___x_3684_, v___x_3691_, v___x_3709_);
v___x_3711_ = l_Lean_Syntax_node2(v___x_3684_, v___x_3688_, v___x_3690_, v___x_3710_);
v___x_3712_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3684_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3715_ = l_Lean_Syntax_node1(v___x_3684_, v___x_3714_, v_val_3677_);
v___x_3716_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3684_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = l_Lean_Syntax_node5(v___x_3684_, v___x_3686_, v___x_3711_, v___x_3675_, v___x_3713_, v___x_3715_, v___x_3717_);
lean_inc(v___y_3654_);
v___y_3625_ = v___y_3653_;
v___y_3626_ = v___y_3654_;
v___y_3627_ = v___y_3655_;
v___y_3628_ = v___y_3656_;
v___y_3629_ = v___y_3657_;
v___y_3630_ = v___y_3658_;
v___y_3631_ = v___y_3659_;
v___y_3632_ = v___y_3660_;
v___y_3633_ = v___y_3654_;
v_rhs_3634_ = v___x_3718_;
v___y_3635_ = v___y_3667_;
v___y_3636_ = v___y_3668_;
v___y_3637_ = v___y_3669_;
v___y_3638_ = v___y_3670_;
v___y_3639_ = v___y_3671_;
v___y_3640_ = v___y_3672_;
v___y_3641_ = v___y_3673_;
goto v___jp_3624_;
}
}
}
}
v___jp_3721_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___f_3744_; lean_object* v___x_3745_; 
v___x_3741_ = lean_box(v___y_3729_);
v___x_3742_ = lean_box(v___y_3722_);
v___x_3743_ = lean_box(v___y_3740_);
v___f_3744_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3744_, 0, v___y_3730_);
lean_closure_set(v___f_3744_, 1, v___y_3723_);
lean_closure_set(v___f_3744_, 2, v___x_3741_);
lean_closure_set(v___f_3744_, 3, v___x_3742_);
lean_closure_set(v___f_3744_, 4, v___y_3724_);
lean_closure_set(v___f_3744_, 5, v___x_3743_);
v___x_3745_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___y_3739_, v___f_3744_, v___y_3736_, v___y_3731_, v___y_3734_, v___y_3738_, v___y_3737_, v___y_3733_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v_toCold_3747_; lean_object* v_options_3748_; lean_object* v_fst_3749_; lean_object* v_snd_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3789_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
v_toCold_3747_ = lean_ctor_get(v___y_3737_, 0);
v_options_3748_ = lean_ctor_get(v_toCold_3747_, 2);
v_fst_3749_ = lean_ctor_get(v_a_3746_, 0);
v_snd_3750_ = lean_ctor_get(v_a_3746_, 1);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_a_3746_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3752_ = v_a_3746_;
v_isShared_3753_ = v_isSharedCheck_3789_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_snd_3750_);
lean_inc(v_fst_3749_);
lean_dec(v_a_3746_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3789_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v_inheritedTraceOptions_3754_; uint8_t v_hasTrace_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___f_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v_inheritedTraceOptions_3754_ = lean_ctor_get(v_toCold_3747_, 11);
v_hasTrace_3755_ = lean_ctor_get_uint8(v_options_3748_, sizeof(void*)*1);
v___x_3756_ = lean_box(v___y_3725_);
v___x_3757_ = lean_box(v___y_3727_);
v___x_3758_ = lean_box(v___y_3740_);
v___x_3759_ = lean_box(v___y_3729_);
lean_inc(v_snd_3750_);
v___f_3760_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 19, 10);
lean_closure_set(v___f_3760_, 0, v___y_3726_);
lean_closure_set(v___f_3760_, 1, v___y_3728_);
lean_closure_set(v___f_3760_, 2, v_a_3623_);
lean_closure_set(v___f_3760_, 3, v_letOrReassign_3606_);
lean_closure_set(v___f_3760_, 4, v_a_3620_);
lean_closure_set(v___f_3760_, 5, v___x_3756_);
lean_closure_set(v___f_3760_, 6, v___x_3757_);
lean_closure_set(v___f_3760_, 7, v_snd_3750_);
lean_closure_set(v___f_3760_, 8, v___x_3758_);
lean_closure_set(v___f_3760_, 9, v___x_3759_);
v___x_3761_ = l_Lean_Syntax_getId(v___y_3735_);
lean_dec(v___y_3735_);
v___x_3762_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3761_);
if (v_hasTrace_3755_ == 0)
{
lean_object* v___x_3763_; 
lean_del_object(v___x_3752_);
v___x_3763_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3761_, v_fst_3749_, v_snd_3750_, v___f_3760_, v___y_3740_, v___x_3762_, v___y_3732_, v___y_3736_, v___y_3731_, v___y_3734_, v___y_3738_, v___y_3737_, v___y_3733_);
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; 
v___x_3764_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3765_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3754_, v_options_3748_, v___x_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; 
lean_del_object(v___x_3752_);
v___x_3767_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3761_, v_fst_3749_, v_snd_3750_, v___f_3760_, v___y_3740_, v___x_3762_, v___y_3732_, v___y_3736_, v___y_3731_, v___y_3734_, v___y_3738_, v___y_3737_, v___y_3733_);
return v___x_3767_;
}
else
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3771_; 
lean_inc(v___x_3761_);
v___x_3768_ = l_Lean_MessageData_ofName(v___x_3761_);
v___x_3769_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3753_ == 0)
{
lean_ctor_set_tag(v___x_3752_, 7);
lean_ctor_set(v___x_3752_, 1, v___x_3769_);
lean_ctor_set(v___x_3752_, 0, v___x_3768_);
v___x_3771_ = v___x_3752_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_inc(v_fst_3749_);
v___x_3772_ = l_Lean_MessageData_ofExpr(v_fst_3749_);
v___x_3773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3773_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
lean_inc(v_snd_3750_);
v___x_3776_ = l_Lean_MessageData_ofExpr(v_snd_3750_);
v___x_3777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3775_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3764_, v___x_3777_, v___y_3734_, v___y_3738_, v___y_3737_, v___y_3733_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v___x_3779_; 
lean_dec_ref_known(v___x_3778_, 1);
v___x_3779_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3761_, v_fst_3749_, v_snd_3750_, v___f_3760_, v___y_3740_, v___x_3762_, v___y_3732_, v___y_3736_, v___y_3731_, v___y_3734_, v___y_3738_, v___y_3737_, v___y_3733_);
return v___x_3779_;
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v___x_3761_);
lean_dec_ref(v___f_3760_);
lean_dec(v_snd_3750_);
lean_dec(v_fst_3749_);
v_a_3780_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3778_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3778_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
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
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec(v___y_3735_);
lean_dec(v___y_3728_);
lean_dec(v___y_3726_);
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_letOrReassign_3606_);
v_a_3790_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3745_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3745_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
v___jp_3798_:
{
uint8_t v_nondep_3815_; 
v_nondep_3815_ = lean_ctor_get_uint8(v_config_3605_, sizeof(void*)*1);
if (v_nondep_3815_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3606_) == 1)
{
uint8_t v_usedOnly_3816_; uint8_t v_zeta_3817_; lean_object* v_eq_x3f_3818_; 
v_usedOnly_3816_ = lean_ctor_get_uint8(v_config_3605_, sizeof(void*)*1 + 1);
v_zeta_3817_ = lean_ctor_get_uint8(v_config_3605_, sizeof(void*)*1 + 2);
v_eq_x3f_3818_ = lean_ctor_get(v_config_3605_, 0);
lean_inc(v_eq_x3f_3818_);
lean_dec_ref(v_config_3605_);
lean_inc(v_id_3807_);
v___y_3722_ = v___y_3799_;
v___y_3723_ = v___y_3800_;
v___y_3724_ = v___y_3801_;
v___y_3725_ = v_zeta_3817_;
v___y_3726_ = v_id_3807_;
v___y_3727_ = v_usedOnly_3816_;
v___y_3728_ = v_eq_x3f_3818_;
v___y_3729_ = v___y_3802_;
v___y_3730_ = v___y_3804_;
v___y_3731_ = v___y_3810_;
v___y_3732_ = v___y_3808_;
v___y_3733_ = v___y_3814_;
v___y_3734_ = v___y_3811_;
v___y_3735_ = v_id_3807_;
v___y_3736_ = v___y_3809_;
v___y_3737_ = v___y_3813_;
v___y_3738_ = v___y_3812_;
v___y_3739_ = v___y_3803_;
v___y_3740_ = v___y_3806_;
goto v___jp_3721_;
}
else
{
uint8_t v_usedOnly_3819_; uint8_t v_zeta_3820_; lean_object* v_eq_x3f_3821_; 
v_usedOnly_3819_ = lean_ctor_get_uint8(v_config_3605_, sizeof(void*)*1 + 1);
v_zeta_3820_ = lean_ctor_get_uint8(v_config_3605_, sizeof(void*)*1 + 2);
v_eq_x3f_3821_ = lean_ctor_get(v_config_3605_, 0);
lean_inc(v_eq_x3f_3821_);
lean_dec_ref(v_config_3605_);
lean_inc(v_id_3807_);
v___y_3722_ = v___y_3799_;
v___y_3723_ = v___y_3800_;
v___y_3724_ = v___y_3801_;
v___y_3725_ = v_zeta_3820_;
v___y_3726_ = v_id_3807_;
v___y_3727_ = v_usedOnly_3819_;
v___y_3728_ = v_eq_x3f_3821_;
v___y_3729_ = v___y_3802_;
v___y_3730_ = v___y_3804_;
v___y_3731_ = v___y_3810_;
v___y_3732_ = v___y_3808_;
v___y_3733_ = v___y_3814_;
v___y_3734_ = v___y_3811_;
v___y_3735_ = v_id_3807_;
v___y_3736_ = v___y_3809_;
v___y_3737_ = v___y_3813_;
v___y_3738_ = v___y_3812_;
v___y_3739_ = v___y_3803_;
v___y_3740_ = v___y_3805_;
goto v___jp_3721_;
}
}
else
{
uint8_t v_usedOnly_3822_; uint8_t v_zeta_3823_; lean_object* v_eq_x3f_3824_; 
v_usedOnly_3822_ = lean_ctor_get_uint8(v_config_3605_, sizeof(void*)*1 + 1);
v_zeta_3823_ = lean_ctor_get_uint8(v_config_3605_, sizeof(void*)*1 + 2);
v_eq_x3f_3824_ = lean_ctor_get(v_config_3605_, 0);
lean_inc(v_eq_x3f_3824_);
lean_dec_ref(v_config_3605_);
lean_inc(v_id_3807_);
v___y_3722_ = v___y_3799_;
v___y_3723_ = v___y_3800_;
v___y_3724_ = v___y_3801_;
v___y_3725_ = v_zeta_3823_;
v___y_3726_ = v_id_3807_;
v___y_3727_ = v_usedOnly_3822_;
v___y_3728_ = v_eq_x3f_3824_;
v___y_3729_ = v___y_3802_;
v___y_3730_ = v___y_3804_;
v___y_3731_ = v___y_3810_;
v___y_3732_ = v___y_3808_;
v___y_3733_ = v___y_3814_;
v___y_3734_ = v___y_3811_;
v___y_3735_ = v_id_3807_;
v___y_3736_ = v___y_3809_;
v___y_3737_ = v___y_3813_;
v___y_3738_ = v___y_3812_;
v___y_3739_ = v___y_3803_;
v___y_3740_ = v___y_3806_;
goto v___jp_3721_;
}
}
v___jp_3825_:
{
lean_object* v___x_3839_; lean_object* v_id_3840_; lean_object* v_binders_3841_; lean_object* v_type_3842_; lean_object* v_value_3843_; uint8_t v___x_3844_; 
v___x_3839_ = l_Lean_Elab_Term_mkLetIdDeclView(v___y_3833_);
lean_dec(v___y_3833_);
v_id_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_id_3840_);
v_binders_3841_ = lean_ctor_get(v___x_3839_, 1);
lean_inc_ref(v_binders_3841_);
v_type_3842_ = lean_ctor_get(v___x_3839_, 2);
lean_inc(v_type_3842_);
v_value_3843_ = lean_ctor_get(v___x_3839_, 3);
lean_inc(v_value_3843_);
lean_dec_ref(v___x_3839_);
v___x_3844_ = l_Lean_Syntax_isIdent(v_id_3840_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_id_3840_, v___y_3838_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3834_, v___y_3829_, v___y_3832_, v___y_3831_);
lean_dec(v_id_3840_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___y_3799_ = v___y_3826_;
v___y_3800_ = v_value_3843_;
v___y_3801_ = v___y_3827_;
v___y_3802_ = v___y_3828_;
v___y_3803_ = v_binders_3841_;
v___y_3804_ = v_type_3842_;
v___y_3805_ = v___y_3830_;
v___y_3806_ = v___y_3838_;
v_id_3807_ = v_a_3846_;
v___y_3808_ = v___y_3835_;
v___y_3809_ = v___y_3836_;
v___y_3810_ = v___y_3837_;
v___y_3811_ = v___y_3834_;
v___y_3812_ = v___y_3829_;
v___y_3813_ = v___y_3832_;
v___y_3814_ = v___y_3831_;
goto v___jp_3798_;
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec(v_value_3843_);
lean_dec(v_type_3842_);
lean_dec_ref(v_binders_3841_);
lean_dec(v___y_3827_);
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v_a_3847_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3845_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3845_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
else
{
v___y_3799_ = v___y_3826_;
v___y_3800_ = v_value_3843_;
v___y_3801_ = v___y_3827_;
v___y_3802_ = v___y_3828_;
v___y_3803_ = v_binders_3841_;
v___y_3804_ = v_type_3842_;
v___y_3805_ = v___y_3830_;
v___y_3806_ = v___y_3838_;
v_id_3807_ = v_id_3840_;
v___y_3808_ = v___y_3835_;
v___y_3809_ = v___y_3836_;
v___y_3810_ = v___y_3837_;
v___y_3811_ = v___y_3834_;
v___y_3812_ = v___y_3829_;
v___y_3813_ = v___y_3832_;
v___y_3814_ = v___y_3831_;
goto v___jp_3798_;
}
}
v___jp_3855_:
{
lean_object* v_doBlockResultType_3864_; lean_object* v___x_3865_; 
v_doBlockResultType_3864_ = lean_ctor_get(v___y_3857_, 3);
lean_inc_ref(v_doBlockResultType_3864_);
v___x_3865_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3864_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3924_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3868_ = v___x_3865_;
v_isShared_3869_ = v_isSharedCheck_3924_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3924_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v___x_3870_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3871_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3872_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3873_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_3856_);
v___x_3874_ = l_Lean_Syntax_isOfKind(v_decl_3856_, v___x_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
lean_del_object(v___x_3868_);
lean_dec(v_a_3866_);
lean_dec(v_decl_3856_);
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_tk_3608_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v___x_3875_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3875_;
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3876_ = lean_unsigned_to_nat(0u);
v___x_3877_ = l_Lean_Syntax_getArg(v_decl_3856_, v___x_3876_);
lean_dec(v_decl_3856_);
v___x_3878_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__10));
lean_inc(v___x_3877_);
v___x_3879_ = l_Lean_Syntax_isOfKind(v___x_3877_, v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; uint8_t v___x_3881_; 
lean_dec(v_tk_3608_);
v___x_3880_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3877_);
v___x_3881_ = l_Lean_Syntax_isOfKind(v___x_3877_, v___x_3880_);
if (v___x_3881_ == 0)
{
lean_del_object(v___x_3868_);
lean_dec(v_a_3866_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3877_);
v___x_3883_ = l_Lean_Syntax_isOfKind(v___x_3877_, v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
lean_dec(v___x_3877_);
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v___x_3884_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3884_;
}
else
{
v___y_3826_ = v___x_3881_;
v___y_3827_ = v___x_3876_;
v___y_3828_ = v___x_3874_;
v___y_3829_ = v___y_3861_;
v___y_3830_ = v___x_3881_;
v___y_3831_ = v___y_3863_;
v___y_3832_ = v___y_3862_;
v___y_3833_ = v___x_3877_;
v___y_3834_ = v___y_3860_;
v___y_3835_ = v___y_3857_;
v___y_3836_ = v___y_3858_;
v___y_3837_ = v___y_3859_;
v___y_3838_ = v___x_3874_;
goto v___jp_3825_;
}
}
else
{
v___y_3826_ = v___x_3881_;
v___y_3827_ = v___x_3876_;
v___y_3828_ = v___x_3874_;
v___y_3829_ = v___y_3861_;
v___y_3830_ = v___x_3881_;
v___y_3831_ = v___y_3863_;
v___y_3832_ = v___y_3862_;
v___y_3833_ = v___x_3877_;
v___y_3834_ = v___y_3860_;
v___y_3835_ = v___y_3857_;
v___y_3836_ = v___y_3858_;
v___y_3837_ = v___y_3859_;
v___y_3838_ = v___x_3874_;
goto v___jp_3825_;
}
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
v___x_3885_ = lean_unsigned_to_nat(1u);
v___x_3886_ = l_Lean_Syntax_getArg(v___x_3877_, v___x_3885_);
v___x_3887_ = l_Lean_Syntax_matchesNull(v___x_3886_, v___x_3876_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; 
lean_dec(v___x_3877_);
lean_del_object(v___x_3868_);
lean_dec(v_a_3866_);
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v___x_3888_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3888_;
}
else
{
lean_object* v___x_3889_; lean_object* v___f_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3889_ = lean_box(v___x_3879_);
v___f_3890_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 10, 1);
lean_closure_set(v___f_3890_, 0, v___x_3889_);
v___x_3891_ = l_Lean_Syntax_getArg(v___x_3877_, v___x_3876_);
v___x_3892_ = lean_unsigned_to_nat(2u);
v___x_3893_ = l_Lean_Syntax_getArg(v___x_3877_, v___x_3892_);
v___x_3894_ = l_Lean_Syntax_isNone(v___x_3893_);
if (v___x_3894_ == 0)
{
uint8_t v___x_3895_; 
lean_inc(v___x_3893_);
v___x_3895_ = l_Lean_Syntax_matchesNull(v___x_3893_, v___x_3885_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; 
lean_dec(v___x_3893_);
lean_dec(v___x_3891_);
lean_dec_ref(v___f_3890_);
lean_dec(v___x_3877_);
lean_del_object(v___x_3868_);
lean_dec(v_a_3866_);
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v___x_3896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3896_;
}
else
{
lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3897_ = l_Lean_Syntax_getArg(v___x_3893_, v___x_3876_);
lean_dec(v___x_3893_);
v___x_3898_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3897_);
v___x_3899_ = l_Lean_Syntax_isOfKind(v___x_3897_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; 
lean_dec(v___x_3897_);
lean_dec(v___x_3891_);
lean_dec_ref(v___f_3890_);
lean_dec(v___x_3877_);
lean_del_object(v___x_3868_);
lean_dec(v_a_3866_);
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v___x_3900_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3900_;
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = l_Lean_Syntax_getArg(v___x_3897_, v___x_3885_);
lean_dec(v___x_3897_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set_tag(v___x_3868_, 1);
lean_ctor_set(v___x_3868_, 0, v___x_3901_);
v___x_3903_ = v___x_3868_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
v___y_3653_ = v___f_3890_;
v___y_3654_ = v___x_3891_;
v___y_3655_ = v___x_3870_;
v___y_3656_ = v___x_3879_;
v___y_3657_ = v_a_3866_;
v___y_3658_ = v___x_3871_;
v___y_3659_ = v___x_3874_;
v___y_3660_ = v___x_3872_;
v___y_3661_ = v___x_3870_;
v___y_3662_ = v___x_3877_;
v___y_3663_ = v___x_3879_;
v___y_3664_ = v___x_3871_;
v___y_3665_ = v___x_3872_;
v_xType_x3f_3666_ = v___x_3903_;
v___y_3667_ = v___y_3857_;
v___y_3668_ = v___y_3858_;
v___y_3669_ = v___y_3859_;
v___y_3670_ = v___y_3860_;
v___y_3671_ = v___y_3861_;
v___y_3672_ = v___y_3862_;
v___y_3673_ = v___y_3863_;
goto v___jp_3652_;
}
}
}
}
else
{
lean_object* v___x_3905_; 
lean_dec(v___x_3893_);
lean_del_object(v___x_3868_);
v___x_3905_ = lean_box(0);
v___y_3653_ = v___f_3890_;
v___y_3654_ = v___x_3891_;
v___y_3655_ = v___x_3870_;
v___y_3656_ = v___x_3879_;
v___y_3657_ = v_a_3866_;
v___y_3658_ = v___x_3871_;
v___y_3659_ = v___x_3874_;
v___y_3660_ = v___x_3872_;
v___y_3661_ = v___x_3870_;
v___y_3662_ = v___x_3877_;
v___y_3663_ = v___x_3879_;
v___y_3664_ = v___x_3871_;
v___y_3665_ = v___x_3872_;
v_xType_x3f_3666_ = v___x_3905_;
v___y_3667_ = v___y_3857_;
v___y_3668_ = v___y_3858_;
v___y_3669_ = v___y_3859_;
v___y_3670_ = v___y_3860_;
v___y_3671_ = v___y_3861_;
v___y_3672_ = v___y_3862_;
v___y_3673_ = v___y_3863_;
goto v___jp_3652_;
}
}
}
}
else
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_del_object(v___x_3868_);
lean_dec(v_a_3866_);
lean_dec(v_a_3620_);
v___x_3906_ = lean_box(v___x_3874_);
lean_inc(v___x_3877_);
v___x_3907_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3907_, 0, v___x_3877_);
lean_closure_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3907_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v_ref_3910_; uint8_t v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v_ref_3910_ = lean_ctor_get(v___y_3862_, 2);
v___x_3911_ = 0;
v___x_3912_ = l_Lean_SourceInfo_fromRef(v_ref_3910_, v___x_3911_);
v___x_3913_ = l_Lean_Syntax_node1(v___x_3912_, v___x_3873_, v_a_3909_);
lean_inc(v___x_3913_);
v___x_3914_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3914_, 0, v_config_3605_);
lean_closure_set(v___x_3914_, 1, v_letOrReassign_3606_);
lean_closure_set(v___x_3914_, 2, v___x_3913_);
lean_closure_set(v___x_3914_, 3, v_tk_3608_);
lean_closure_set(v___x_3914_, 4, v_a_3623_);
v___x_3915_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v___x_3877_, v___x_3913_, v___x_3914_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
return v___x_3915_;
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v___x_3877_);
lean_dec(v_a_3623_);
lean_dec(v_tk_3608_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v_a_3916_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3908_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3908_);
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
}
}
else
{
lean_dec(v_decl_3856_);
lean_dec(v_a_3623_);
lean_dec(v_a_3620_);
lean_dec(v_tk_3608_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
return v___x_3865_;
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec(v_a_3620_);
lean_dec(v_tk_3608_);
lean_dec(v_decl_3607_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v_a_3957_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3622_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3622_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec(v_a_3620_);
lean_dec_ref(v_dec_3609_);
lean_dec(v_tk_3608_);
lean_dec(v_decl_3607_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v_a_3965_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3621_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3621_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v_dec_3609_);
lean_dec(v_tk_3608_);
lean_dec(v_decl_3607_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v_a_3973_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3619_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3619_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref(v_dec_3609_);
lean_dec(v_tk_3608_);
lean_dec(v_decl_3607_);
lean_dec(v_letOrReassign_3606_);
lean_dec_ref(v_config_3605_);
v_a_3981_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3618_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3618_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3989_, lean_object* v_x_3990_, lean_object* v_x_3991_, lean_object* v_x_3992_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3990_, v_x_3991_, v_x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_cls_3994_, lean_object* v_msg_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_3994_, v_msg_3995_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_cls_4005_, lean_object* v_msg_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_cls_4005_, v_msg_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec_ref(v___y_4007_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_4021_, v___y_4022_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___boxed(lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec_ref(v___y_4025_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_00_u03b1_4034_, lean_object* v_beforeStx_4035_, lean_object* v_afterStx_4036_, lean_object* v_x_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_beforeStx_4035_, v_afterStx_4036_, v_x_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_00_u03b1_4047_, lean_object* v_beforeStx_4048_, lean_object* v_afterStx_4049_, lean_object* v_x_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_00_u03b1_4047_, v_beforeStx_4048_, v_afterStx_4049_, v_x_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec_ref(v___y_4051_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11(lean_object* v_00_u03b1_4060_, lean_object* v_x_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v___x_4064_; 
v___x_4064_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v_x_4061_, v___y_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___boxed(lean_object* v_00_u03b1_4065_, lean_object* v_x_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11(v_00_u03b1_4065_, v_x_4066_, v___y_4067_, v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec_ref(v_x_4066_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(lean_object* v_00_u03b1_4070_, lean_object* v_ref_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(v_ref_4071_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___boxed(lean_object* v_00_u03b1_4081_, lean_object* v_ref_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(v_00_u03b1_4081_, v_ref_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec_ref(v___y_4083_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_4092_, lean_object* v_x_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_4103_, lean_object* v_x_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_4103_, v_x_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec_ref(v___y_4105_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_4114_, lean_object* v_x_4115_, size_t v_x_4116_, size_t v_x_4117_, lean_object* v_x_4118_, lean_object* v_x_4119_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_4115_, v_x_4116_, v_x_4117_, v_x_4118_, v_x_4119_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4121_, lean_object* v_x_4122_, lean_object* v_x_4123_, lean_object* v_x_4124_, lean_object* v_x_4125_, lean_object* v_x_4126_){
_start:
{
size_t v_x_92761__boxed_4127_; size_t v_x_92762__boxed_4128_; lean_object* v_res_4129_; 
v_x_92761__boxed_4127_ = lean_unbox_usize(v_x_4123_);
lean_dec(v_x_4123_);
v_x_92762__boxed_4128_ = lean_unbox_usize(v_x_4124_);
lean_dec(v_x_4124_);
v_res_4129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_4121_, v_x_4122_, v_x_92761__boxed_4127_, v_x_92762__boxed_4128_, v_x_4125_, v_x_4126_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(lean_object* v_00_u03b1_4130_, lean_object* v_stx_4131_, lean_object* v_output_4132_, lean_object* v_x_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_stx_4131_, v_output_4132_, v_x_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4142_, lean_object* v_stx_4143_, lean_object* v_output_4144_, lean_object* v_x_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(v_00_u03b1_4142_, v_stx_4143_, v_output_4144_, v_x_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(lean_object* v_as_4154_, lean_object* v_as_x27_4155_, lean_object* v_b_4156_, lean_object* v_a_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v___x_4166_; 
v___x_4166_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(v_as_x27_4155_, v_b_4156_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___boxed(lean_object* v_as_4167_, lean_object* v_as_x27_4168_, lean_object* v_b_4169_, lean_object* v_a_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(v_as_4167_, v_as_x27_4168_, v_b_4169_, v_a_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v_as_x27_4168_);
lean_dec(v_as_4167_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4180_, lean_object* v_n_4181_, lean_object* v_k_4182_, lean_object* v_v_4183_){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(v_n_4181_, v_k_4182_, v_v_4183_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_4185_, size_t v_depth_4186_, lean_object* v_keys_4187_, lean_object* v_vals_4188_, lean_object* v_heq_4189_, lean_object* v_i_4190_, lean_object* v_entries_4191_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_depth_4186_, v_keys_4187_, v_vals_4188_, v_i_4190_, v_entries_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_4193_, lean_object* v_depth_4194_, lean_object* v_keys_4195_, lean_object* v_vals_4196_, lean_object* v_heq_4197_, lean_object* v_i_4198_, lean_object* v_entries_4199_){
_start:
{
size_t v_depth_boxed_4200_; lean_object* v_res_4201_; 
v_depth_boxed_4200_ = lean_unbox_usize(v_depth_4194_);
lean_dec(v_depth_4194_);
v_res_4201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(v_00_u03b2_4193_, v_depth_boxed_4200_, v_keys_4195_, v_vals_4196_, v_heq_4197_, v_i_4198_, v_entries_4199_);
lean_dec_ref(v_vals_4196_);
lean_dec_ref(v_keys_4195_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17(lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(v___y_4207_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___boxed(lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17(v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_4218_, lean_object* v_x_4219_, lean_object* v_mkInfoTree_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(v_x_4219_, v_mkInfoTree_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4229_, lean_object* v_x_4230_, lean_object* v_mkInfoTree_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12(v_00_u03b1_4229_, v_x_4230_, v_mkInfoTree_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18(lean_object* v_00_u03b2_4240_, lean_object* v_m_4241_, lean_object* v_a_4242_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(v_m_4241_, v_a_4242_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___boxed(lean_object* v_00_u03b2_4244_, lean_object* v_m_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18(v_00_u03b2_4244_, v_m_4245_, v_a_4246_);
lean_dec(v_a_4246_);
lean_dec_ref(v_m_4245_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13(lean_object* v_00_u03b2_4248_, lean_object* v_x_4249_, lean_object* v_x_4250_, lean_object* v_x_4251_, lean_object* v_x_4252_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13___redArg(v_x_4249_, v_x_4250_, v_x_4251_, v_x_4252_);
return v___x_4253_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20(lean_object* v_00_u03b2_4254_, lean_object* v_x_4255_, lean_object* v_x_4256_){
_start:
{
uint8_t v___x_4257_; 
v___x_4257_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(v_x_4255_, v_x_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___boxed(lean_object* v_00_u03b2_4258_, lean_object* v_x_4259_, lean_object* v_x_4260_){
_start:
{
uint8_t v_res_4261_; lean_object* v_r_4262_; 
v_res_4261_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20(v_00_u03b2_4258_, v_x_4259_, v_x_4260_);
lean_dec_ref(v_x_4260_);
lean_dec_ref(v_x_4259_);
v_r_4262_ = lean_box(v_res_4261_);
return v_r_4262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23(lean_object* v_00_u03b2_4263_, lean_object* v_a_4264_, lean_object* v_x_4265_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(v_a_4264_, v_x_4265_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___boxed(lean_object* v_00_u03b2_4267_, lean_object* v_a_4268_, lean_object* v_x_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23(v_00_u03b2_4267_, v_a_4268_, v_x_4269_);
lean_dec(v_x_4269_);
lean_dec(v_a_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_4271_, lean_object* v_x_4272_, size_t v_x_4273_, lean_object* v_x_4274_){
_start:
{
uint8_t v___x_4275_; 
v___x_4275_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(v_x_4272_, v_x_4273_, v_x_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_4276_, lean_object* v_x_4277_, lean_object* v_x_4278_, lean_object* v_x_4279_){
_start:
{
size_t v_x_92905__boxed_4280_; uint8_t v_res_4281_; lean_object* v_r_4282_; 
v_x_92905__boxed_4280_ = lean_unbox_usize(v_x_4278_);
lean_dec(v_x_4278_);
v_res_4281_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23(v_00_u03b2_4276_, v_x_4277_, v_x_92905__boxed_4280_, v_x_4279_);
lean_dec_ref(v_x_4279_);
lean_dec_ref(v_x_4277_);
v_r_4282_ = lean_box(v_res_4281_);
return v_r_4282_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26(lean_object* v_00_u03b2_4283_, lean_object* v_keys_4284_, lean_object* v_vals_4285_, lean_object* v_heq_4286_, lean_object* v_i_4287_, lean_object* v_k_4288_){
_start:
{
uint8_t v___x_4289_; 
v___x_4289_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(v_keys_4284_, v_i_4287_, v_k_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___boxed(lean_object* v_00_u03b2_4290_, lean_object* v_keys_4291_, lean_object* v_vals_4292_, lean_object* v_heq_4293_, lean_object* v_i_4294_, lean_object* v_k_4295_){
_start:
{
uint8_t v_res_4296_; lean_object* v_r_4297_; 
v_res_4296_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26(v_00_u03b2_4290_, v_keys_4291_, v_vals_4292_, v_heq_4293_, v_i_4294_, v_k_4295_);
lean_dec_ref(v_k_4295_);
lean_dec_ref(v_vals_4292_);
lean_dec_ref(v_keys_4291_);
v_r_4297_ = lean_box(v_res_4296_);
return v_r_4297_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__0));
v___x_4300_ = l_Lean_stringToMessageData(v___x_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4301_, lean_object* v_mutTk_x3f_4302_, lean_object* v_initConfig_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4302_) == 0)
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4301_, v_initConfig_4303_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_);
return v___x_4312_;
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4313_ = lean_unsigned_to_nat(0u);
v___x_4314_ = l_Lean_Syntax_getArg(v_letConfigStx_4301_, v___x_4313_);
v___x_4315_ = l_Lean_Syntax_getArgs(v___x_4314_);
lean_dec(v___x_4314_);
v___x_4316_ = lean_array_get_size(v___x_4315_);
lean_dec_ref(v___x_4315_);
v___x_4317_ = lean_nat_dec_eq(v___x_4316_, v___x_4313_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v_initConfig_4303_);
v___x_4318_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1);
v___x_4319_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_letConfigStx_4301_, v___x_4318_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_);
lean_dec(v_letConfigStx_4301_);
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4319_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4319_);
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
else
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4301_, v_initConfig_4303_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_);
return v___x_4328_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4329_, lean_object* v_mutTk_x3f_4330_, lean_object* v_initConfig_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4329_, v_mutTk_x3f_4330_, v_initConfig_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_);
lean_dec(v_a_4338_);
lean_dec_ref(v_a_4337_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec_ref(v_a_4332_);
lean_dec(v_mutTk_x3f_4330_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4356_, lean_object* v_dec_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v___x_4366_; uint8_t v___x_4367_; 
v___x_4366_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_stx_4356_);
v___x_4367_ = l_Lean_Syntax_isOfKind(v_stx_4356_, v___x_4366_);
if (v___x_4367_ == 0)
{
lean_object* v___x_4368_; 
lean_dec_ref(v_dec_4357_);
lean_dec(v_stx_4356_);
v___x_4368_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4368_;
}
else
{
lean_object* v___x_4369_; lean_object* v_tk_4370_; lean_object* v_mutTk_x3f_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___x_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; 
v___x_4369_ = lean_unsigned_to_nat(0u);
v_tk_4370_ = l_Lean_Syntax_getArg(v_stx_4356_, v___x_4369_);
v___x_4404_ = lean_unsigned_to_nat(1u);
v___x_4405_ = l_Lean_Syntax_getArg(v_stx_4356_, v___x_4404_);
v___x_4406_ = l_Lean_Syntax_isNone(v___x_4405_);
if (v___x_4406_ == 0)
{
uint8_t v___x_4407_; 
lean_inc(v___x_4405_);
v___x_4407_ = l_Lean_Syntax_matchesNull(v___x_4405_, v___x_4404_);
if (v___x_4407_ == 0)
{
lean_object* v___x_4408_; 
lean_dec(v___x_4405_);
lean_dec(v_tk_4370_);
lean_dec_ref(v_dec_4357_);
lean_dec(v_stx_4356_);
v___x_4408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4408_;
}
else
{
lean_object* v_mutTk_x3f_4409_; lean_object* v___x_4410_; 
v_mutTk_x3f_4409_ = l_Lean_Syntax_getArg(v___x_4405_, v___x_4369_);
lean_dec(v___x_4405_);
v___x_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4410_, 0, v_mutTk_x3f_4409_);
v_mutTk_x3f_4372_ = v___x_4410_;
v___y_4373_ = v_a_4358_;
v___y_4374_ = v_a_4359_;
v___y_4375_ = v_a_4360_;
v___y_4376_ = v_a_4361_;
v___y_4377_ = v_a_4362_;
v___y_4378_ = v_a_4363_;
v___y_4379_ = v_a_4364_;
goto v___jp_4371_;
}
}
else
{
lean_object* v___x_4411_; 
lean_dec(v___x_4405_);
v___x_4411_ = lean_box(0);
v_mutTk_x3f_4372_ = v___x_4411_;
v___y_4373_ = v_a_4358_;
v___y_4374_ = v_a_4359_;
v___y_4375_ = v_a_4360_;
v___y_4376_ = v_a_4361_;
v___y_4377_ = v_a_4362_;
v___y_4378_ = v_a_4363_;
v___y_4379_ = v_a_4364_;
goto v___jp_4371_;
}
v___jp_4371_:
{
lean_object* v___x_4380_; lean_object* v_config_4381_; lean_object* v___x_4382_; uint8_t v___x_4383_; 
v___x_4380_ = lean_unsigned_to_nat(2u);
v_config_4381_ = l_Lean_Syntax_getArg(v_stx_4356_, v___x_4380_);
v___x_4382_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_config_4381_);
v___x_4383_ = l_Lean_Syntax_isOfKind(v_config_4381_, v___x_4382_);
if (v___x_4383_ == 0)
{
lean_object* v___x_4384_; 
lean_dec(v_config_4381_);
lean_dec(v_mutTk_x3f_4372_);
lean_dec(v_tk_4370_);
lean_dec_ref(v_dec_4357_);
lean_dec(v_stx_4356_);
v___x_4384_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4384_;
}
else
{
lean_object* v___x_4385_; lean_object* v_decl_4386_; lean_object* v___x_4387_; uint8_t v___x_4388_; 
v___x_4385_ = lean_unsigned_to_nat(3u);
v_decl_4386_ = l_Lean_Syntax_getArg(v_stx_4356_, v___x_4385_);
lean_dec(v_stx_4356_);
v___x_4387_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4386_);
v___x_4388_ = l_Lean_Syntax_isOfKind(v_decl_4386_, v___x_4387_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; 
lean_dec(v_decl_4386_);
lean_dec(v_config_4381_);
lean_dec(v_mutTk_x3f_4372_);
lean_dec(v_tk_4370_);
lean_dec_ref(v_dec_4357_);
v___x_4389_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4389_;
}
else
{
uint8_t v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4390_ = 0;
v___x_4391_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_4392_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_config_4381_, v_mutTk_x3f_4372_, v___x_4391_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4393_);
lean_dec_ref_known(v___x_4392_, 1);
v___x_4394_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4394_, 0, v_mutTk_x3f_4372_);
lean_ctor_set_uint8(v___x_4394_, sizeof(void*)*1, v___x_4390_);
v___x_4395_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4393_, v___x_4394_, v_decl_4386_, v_tk_4370_, v_dec_4357_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
return v___x_4395_;
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec(v_decl_4386_);
lean_dec(v_mutTk_x3f_4372_);
lean_dec(v_tk_4370_);
lean_dec_ref(v_dec_4357_);
v_a_4396_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4392_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4392_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4412_, lean_object* v_dec_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Lean_Elab_Do_elabDoLet(v_stx_4412_, v_dec_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
lean_dec(v_a_4420_);
lean_dec_ref(v_a_4419_);
lean_dec(v_a_4418_);
lean_dec_ref(v_a_4417_);
lean_dec(v_a_4416_);
lean_dec_ref(v_a_4415_);
lean_dec_ref(v_a_4414_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4430_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4431_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_4432_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4433_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4434_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4430_, v___x_4431_, v___x_4432_, v___x_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased(lean_object* v_stx_4451_, lean_object* v_dec_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v___x_4461_; uint8_t v___x_4462_; 
v___x_4461_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
lean_inc(v_stx_4451_);
v___x_4462_ = l_Lean_Syntax_isOfKind(v_stx_4451_, v___x_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; 
lean_dec_ref(v_dec_4452_);
lean_dec(v_stx_4451_);
v___x_4463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4463_;
}
else
{
lean_object* v___x_4464_; lean_object* v_tk_4465_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; uint8_t v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v_t_x3f_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___x_4526_; lean_object* v_mutTk_x3f_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___x_4563_; uint8_t v___x_4564_; 
v___x_4464_ = lean_unsigned_to_nat(0u);
v_tk_4465_ = l_Lean_Syntax_getArg(v_stx_4451_, v___x_4464_);
v___x_4526_ = lean_unsigned_to_nat(1u);
v___x_4563_ = l_Lean_Syntax_getArg(v_stx_4451_, v___x_4526_);
v___x_4564_ = l_Lean_Syntax_isNone(v___x_4563_);
if (v___x_4564_ == 0)
{
uint8_t v___x_4565_; 
lean_inc(v___x_4563_);
v___x_4565_ = l_Lean_Syntax_matchesNull(v___x_4563_, v___x_4526_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; 
lean_dec(v___x_4563_);
lean_dec(v_tk_4465_);
lean_dec_ref(v_dec_4452_);
lean_dec(v_stx_4451_);
v___x_4566_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4566_;
}
else
{
lean_object* v_mutTk_x3f_4567_; lean_object* v___x_4568_; 
v_mutTk_x3f_4567_ = l_Lean_Syntax_getArg(v___x_4563_, v___x_4464_);
lean_dec(v___x_4563_);
v___x_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4568_, 0, v_mutTk_x3f_4567_);
v_mutTk_x3f_4528_ = v___x_4568_;
v___y_4529_ = v_a_4453_;
v___y_4530_ = v_a_4454_;
v___y_4531_ = v_a_4455_;
v___y_4532_ = v_a_4456_;
v___y_4533_ = v_a_4457_;
v___y_4534_ = v_a_4458_;
v___y_4535_ = v_a_4459_;
goto v___jp_4527_;
}
}
else
{
lean_object* v___x_4569_; 
lean_dec(v___x_4563_);
v___x_4569_ = lean_box(0);
v_mutTk_x3f_4528_ = v___x_4569_;
v___y_4529_ = v_a_4453_;
v___y_4530_ = v_a_4454_;
v___y_4531_ = v_a_4455_;
v___y_4532_ = v_a_4456_;
v___y_4533_ = v_a_4457_;
v___y_4534_ = v_a_4458_;
v___y_4535_ = v_a_4459_;
goto v___jp_4527_;
}
v___jp_4466_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
lean_inc_ref(v___y_4477_);
v___x_4485_ = l_Array_append___redArg(v___y_4477_, v___y_4484_);
lean_dec_ref(v___y_4484_);
lean_inc(v___y_4474_);
lean_inc_n(v___y_4479_, 3);
v___x_4486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4486_, 0, v___y_4479_);
lean_ctor_set(v___x_4486_, 1, v___y_4474_);
lean_ctor_set(v___x_4486_, 2, v___x_4485_);
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___y_4479_);
lean_ctor_set(v___x_4488_, 1, v___x_4487_);
lean_inc(v___y_4470_);
v___x_4489_ = l_Lean_Syntax_node5(v___y_4479_, v___y_4470_, v___y_4475_, v___y_4481_, v___x_4486_, v___x_4488_, v___y_4471_);
lean_inc(v___y_4473_);
v___x_4490_ = l_Lean_Syntax_node1(v___y_4479_, v___y_4473_, v___x_4489_);
v___x_4491_ = lean_box(0);
v___x_4492_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*1, v___y_4480_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*1 + 1, v___y_4480_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*1 + 2, v___y_4480_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*1 + 3, v___y_4480_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*1 + 4, v___y_4480_);
v___x_4493_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4493_, 0, v___y_4468_);
lean_ctor_set_uint8(v___x_4493_, sizeof(void*)*1, v___x_4462_);
v___x_4494_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4492_, v___x_4493_, v___x_4490_, v_tk_4465_, v_dec_4452_, v___y_4472_, v___y_4469_, v___y_4482_, v___y_4467_, v___y_4478_, v___y_4483_, v___y_4476_);
return v___x_4494_;
}
v___jp_4495_:
{
lean_object* v_ref_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_ref_4508_ = lean_ctor_get(v___y_4506_, 2);
v___x_4509_ = lean_unsigned_to_nat(4u);
v___x_4510_ = l_Lean_Syntax_getArg(v___y_4499_, v___x_4509_);
lean_dec(v___y_4499_);
v___x_4511_ = 0;
v___x_4512_ = l_Lean_SourceInfo_fromRef(v_ref_4508_, v___x_4511_);
v___x_4513_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4514_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___y_4497_);
lean_inc_n(v___x_4512_, 2);
v___x_4515_ = l_Lean_Syntax_node1(v___x_4512_, v___y_4497_, v___y_4496_);
v___x_4516_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4517_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4512_);
lean_ctor_set(v___x_4518_, 1, v___x_4516_);
lean_ctor_set(v___x_4518_, 2, v___x_4517_);
if (lean_obj_tag(v_t_x3f_4500_) == 1)
{
lean_object* v_val_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v_val_4519_ = lean_ctor_get(v_t_x3f_4500_, 0);
lean_inc(v_val_4519_);
lean_dec_ref_known(v_t_x3f_4500_, 1);
v___x_4520_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4521_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_4512_, 2);
v___x_4522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4512_);
lean_ctor_set(v___x_4522_, 1, v___x_4521_);
v___x_4523_ = l_Lean_Syntax_node2(v___x_4512_, v___x_4520_, v___x_4522_, v_val_4519_);
v___x_4524_ = l_Array_mkArray1___redArg(v___x_4523_);
v___y_4467_ = v___y_4504_;
v___y_4468_ = v___y_4498_;
v___y_4469_ = v___y_4502_;
v___y_4470_ = v___x_4514_;
v___y_4471_ = v___x_4510_;
v___y_4472_ = v___y_4501_;
v___y_4473_ = v___x_4513_;
v___y_4474_ = v___x_4516_;
v___y_4475_ = v___x_4515_;
v___y_4476_ = v___y_4507_;
v___y_4477_ = v___x_4517_;
v___y_4478_ = v___y_4505_;
v___y_4479_ = v___x_4512_;
v___y_4480_ = v___x_4511_;
v___y_4481_ = v___x_4518_;
v___y_4482_ = v___y_4503_;
v___y_4483_ = v___y_4506_;
v___y_4484_ = v___x_4524_;
goto v___jp_4466_;
}
else
{
lean_object* v___x_4525_; 
lean_dec(v_t_x3f_4500_);
v___x_4525_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4467_ = v___y_4504_;
v___y_4468_ = v___y_4498_;
v___y_4469_ = v___y_4502_;
v___y_4470_ = v___x_4514_;
v___y_4471_ = v___x_4510_;
v___y_4472_ = v___y_4501_;
v___y_4473_ = v___x_4513_;
v___y_4474_ = v___x_4516_;
v___y_4475_ = v___x_4515_;
v___y_4476_ = v___y_4507_;
v___y_4477_ = v___x_4517_;
v___y_4478_ = v___y_4505_;
v___y_4479_ = v___x_4512_;
v___y_4480_ = v___x_4511_;
v___y_4481_ = v___x_4518_;
v___y_4482_ = v___y_4503_;
v___y_4483_ = v___y_4506_;
v___y_4484_ = v___x_4525_;
goto v___jp_4466_;
}
}
v___jp_4527_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v___x_4536_ = lean_unsigned_to_nat(2u);
v___x_4537_ = l_Lean_Syntax_getArg(v_stx_4451_, v___x_4536_);
lean_dec(v_stx_4451_);
v___x_4538_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_4537_);
v___x_4539_ = l_Lean_Syntax_isOfKind(v___x_4537_, v___x_4538_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; 
lean_dec(v___x_4537_);
lean_dec(v_mutTk_x3f_4528_);
lean_dec(v_tk_4465_);
lean_dec_ref(v_dec_4452_);
v___x_4540_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4540_;
}
else
{
lean_object* v___x_4541_; lean_object* v___x_4542_; uint8_t v___x_4543_; 
v___x_4541_ = l_Lean_Syntax_getArg(v___x_4537_, v___x_4464_);
v___x_4542_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_4541_);
v___x_4543_ = l_Lean_Syntax_isOfKind(v___x_4541_, v___x_4542_);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; 
lean_dec(v___x_4541_);
lean_dec(v___x_4537_);
lean_dec(v_mutTk_x3f_4528_);
lean_dec(v_tk_4465_);
lean_dec_ref(v_dec_4452_);
v___x_4544_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4544_;
}
else
{
lean_object* v___x_4545_; lean_object* v___x_4546_; uint8_t v___x_4547_; 
v___x_4545_ = l_Lean_Syntax_getArg(v___x_4541_, v___x_4464_);
lean_dec(v___x_4541_);
v___x_4546_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4545_);
v___x_4547_ = l_Lean_Syntax_isOfKind(v___x_4545_, v___x_4546_);
if (v___x_4547_ == 0)
{
lean_object* v___x_4548_; 
lean_dec(v___x_4545_);
lean_dec(v___x_4537_);
lean_dec(v_mutTk_x3f_4528_);
lean_dec(v_tk_4465_);
lean_dec_ref(v_dec_4452_);
v___x_4548_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4548_;
}
else
{
lean_object* v___x_4549_; uint8_t v___x_4550_; 
v___x_4549_ = l_Lean_Syntax_getArg(v___x_4537_, v___x_4526_);
v___x_4550_ = l_Lean_Syntax_matchesNull(v___x_4549_, v___x_4464_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; 
lean_dec(v___x_4545_);
lean_dec(v___x_4537_);
lean_dec(v_mutTk_x3f_4528_);
lean_dec(v_tk_4465_);
lean_dec_ref(v_dec_4452_);
v___x_4551_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4551_;
}
else
{
lean_object* v___x_4552_; uint8_t v___x_4553_; 
v___x_4552_ = l_Lean_Syntax_getArg(v___x_4537_, v___x_4536_);
v___x_4553_ = l_Lean_Syntax_isNone(v___x_4552_);
if (v___x_4553_ == 0)
{
uint8_t v___x_4554_; 
lean_inc(v___x_4552_);
v___x_4554_ = l_Lean_Syntax_matchesNull(v___x_4552_, v___x_4526_);
if (v___x_4554_ == 0)
{
lean_object* v___x_4555_; 
lean_dec(v___x_4552_);
lean_dec(v___x_4545_);
lean_dec(v___x_4537_);
lean_dec(v_mutTk_x3f_4528_);
lean_dec(v_tk_4465_);
lean_dec_ref(v_dec_4452_);
v___x_4555_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4555_;
}
else
{
lean_object* v___x_4556_; lean_object* v___x_4557_; uint8_t v___x_4558_; 
v___x_4556_ = l_Lean_Syntax_getArg(v___x_4552_, v___x_4464_);
lean_dec(v___x_4552_);
v___x_4557_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4556_);
v___x_4558_ = l_Lean_Syntax_isOfKind(v___x_4556_, v___x_4557_);
if (v___x_4558_ == 0)
{
lean_object* v___x_4559_; 
lean_dec(v___x_4556_);
lean_dec(v___x_4545_);
lean_dec(v___x_4537_);
lean_dec(v_mutTk_x3f_4528_);
lean_dec(v_tk_4465_);
lean_dec_ref(v_dec_4452_);
v___x_4559_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4559_;
}
else
{
lean_object* v_t_x3f_4560_; lean_object* v___x_4561_; 
v_t_x3f_4560_ = l_Lean_Syntax_getArg(v___x_4556_, v___x_4526_);
lean_dec(v___x_4556_);
v___x_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4561_, 0, v_t_x3f_4560_);
v___y_4496_ = v___x_4545_;
v___y_4497_ = v___x_4542_;
v___y_4498_ = v_mutTk_x3f_4528_;
v___y_4499_ = v___x_4537_;
v_t_x3f_4500_ = v___x_4561_;
v___y_4501_ = v___y_4529_;
v___y_4502_ = v___y_4530_;
v___y_4503_ = v___y_4531_;
v___y_4504_ = v___y_4532_;
v___y_4505_ = v___y_4533_;
v___y_4506_ = v___y_4534_;
v___y_4507_ = v___y_4535_;
goto v___jp_4495_;
}
}
}
else
{
lean_object* v___x_4562_; 
lean_dec(v___x_4552_);
v___x_4562_ = lean_box(0);
v___y_4496_ = v___x_4545_;
v___y_4497_ = v___x_4542_;
v___y_4498_ = v_mutTk_x3f_4528_;
v___y_4499_ = v___x_4537_;
v_t_x3f_4500_ = v___x_4562_;
v___y_4501_ = v___y_4529_;
v___y_4502_ = v___y_4530_;
v___y_4503_ = v___y_4531_;
v___y_4504_ = v___y_4532_;
v___y_4505_ = v___y_4533_;
v___y_4506_ = v___y_4534_;
v___y_4507_ = v___y_4535_;
goto v___jp_4495_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased___boxed(lean_object* v_stx_4570_, lean_object* v_dec_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_Elab_Do_elabDoErased(v_stx_4570_, v_dec_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
lean_dec(v_a_4574_);
lean_dec_ref(v_a_4573_);
lean_dec_ref(v_a_4572_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1(){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4588_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4589_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4590_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1));
v___x_4591_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoErased___boxed), 10, 0);
v___x_4592_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4588_, v___x_4589_, v___x_4590_, v___x_4591_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___boxed(lean_object* v_a_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1();
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0(lean_object* v_____do__lift_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
uint8_t v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4598_ = 0;
v___x_4599_ = l_Lean_SourceInfo_fromRef(v_____do__lift_4595_, v___x_4598_);
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4599_);
lean_ctor_set(v___x_4600_, 1, v___y_4597_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0___boxed(lean_object* v_____do__lift_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_____do__lift_4601_, v___y_4602_, v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v_____do__lift_4601_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow(lean_object* v_stx_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; uint8_t v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___x_4690_; uint8_t v___x_4691_; 
v___x_4690_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
lean_inc(v_stx_4648_);
v___x_4691_ = l_Lean_Syntax_isOfKind(v_stx_4648_, v___x_4690_);
if (v___x_4691_ == 0)
{
lean_object* v___x_4692_; 
lean_dec(v_stx_4648_);
v___x_4692_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4650_);
return v___x_4692_;
}
else
{
lean_object* v___x_4693_; lean_object* v_tk_4694_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___y_4700_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4703_; lean_object* v___y_4704_; lean_object* v___y_4705_; lean_object* v___y_4706_; uint8_t v___y_4707_; lean_object* v___y_4708_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4739_; lean_object* v___y_4740_; lean_object* v___y_4741_; lean_object* v___y_4742_; lean_object* v_t_x3f_4743_; lean_object* v___y_4744_; lean_object* v___y_4745_; lean_object* v___x_4779_; lean_object* v_mutTk_x3f_4781_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___x_4804_; uint8_t v___x_4805_; 
v___x_4693_ = lean_unsigned_to_nat(0u);
v_tk_4694_ = l_Lean_Syntax_getArg(v_stx_4648_, v___x_4693_);
v___x_4779_ = lean_unsigned_to_nat(1u);
v___x_4804_ = l_Lean_Syntax_getArg(v_stx_4648_, v___x_4779_);
v___x_4805_ = l_Lean_Syntax_isNone(v___x_4804_);
if (v___x_4805_ == 0)
{
uint8_t v___x_4806_; 
lean_inc(v___x_4804_);
v___x_4806_ = l_Lean_Syntax_matchesNull(v___x_4804_, v___x_4779_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; 
lean_dec(v___x_4804_);
lean_dec(v_tk_4694_);
lean_dec(v_stx_4648_);
v___x_4807_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4650_);
return v___x_4807_;
}
else
{
lean_object* v_mutTk_x3f_4808_; lean_object* v___x_4809_; 
v_mutTk_x3f_4808_ = l_Lean_Syntax_getArg(v___x_4804_, v___x_4693_);
lean_dec(v___x_4804_);
v___x_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4809_, 0, v_mutTk_x3f_4808_);
v_mutTk_x3f_4781_ = v___x_4809_;
v___y_4782_ = v_a_4649_;
v___y_4783_ = v_a_4650_;
goto v___jp_4780_;
}
}
else
{
lean_object* v___x_4810_; 
lean_dec(v___x_4804_);
v___x_4810_ = lean_box(0);
v_mutTk_x3f_4781_ = v___x_4810_;
v___y_4782_ = v_a_4649_;
v___y_4783_ = v_a_4650_;
goto v___jp_4780_;
}
v___jp_4695_:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v_a_4716_; lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4737_; 
lean_inc_ref(v___y_4711_);
v___x_4713_ = l_Array_append___redArg(v___y_4711_, v___y_4712_);
lean_dec_ref(v___y_4712_);
lean_inc(v___y_4709_);
lean_inc(v___y_4698_);
v___x_4714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4714_, 0, v___y_4698_);
lean_ctor_set(v___x_4714_, 1, v___y_4709_);
lean_ctor_set(v___x_4714_, 2, v___x_4713_);
v___x_4715_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v___y_4697_, v___y_4704_, v___y_4700_);
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
v_a_4717_ = lean_ctor_get(v___x_4715_, 1);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4719_ = v___x_4715_;
v_isShared_4720_ = v_isSharedCheck_4737_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_inc(v_a_4716_);
lean_dec(v___x_4715_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4737_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4721_; lean_object* v___x_4723_; 
v___x_4721_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__9));
lean_inc(v___y_4698_);
if (v_isShared_4720_ == 0)
{
lean_ctor_set_tag(v___x_4719_, 2);
lean_ctor_set(v___x_4719_, 1, v___x_4721_);
lean_ctor_set(v___x_4719_, 0, v___y_4698_);
v___x_4723_ = v___x_4719_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___y_4698_);
lean_ctor_set(v_reuseFailAlloc_4736_, 1, v___x_4721_);
v___x_4723_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
lean_inc(v___y_4710_);
lean_inc(v___y_4702_);
lean_inc(v___y_4698_);
v___x_4724_ = l_Lean_Syntax_node4(v___y_4698_, v___y_4702_, v___y_4710_, v___x_4714_, v___x_4723_, v___y_4701_);
lean_inc(v___y_4705_);
v___x_4725_ = l_Lean_Syntax_node4(v___y_4698_, v___y_4705_, v___y_4708_, v___y_4696_, v___y_4703_, v___x_4724_);
v___x_4726_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4727_ = l_Lean_SourceInfo_fromRef(v_tk_4694_, v___x_4691_);
lean_dec(v_tk_4694_);
v___x_4728_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__10));
v___x_4729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4727_);
lean_ctor_set(v___x_4729_, 1, v___x_4728_);
if (lean_obj_tag(v___y_4699_) == 1)
{
lean_object* v_val_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
v_val_4730_ = lean_ctor_get(v___y_4699_, 0);
lean_inc(v_val_4730_);
lean_dec_ref_known(v___y_4699_, 1);
v___x_4731_ = l_Lean_SourceInfo_fromRef(v_val_4730_, v___x_4691_);
lean_dec(v_val_4730_);
v___x_4732_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_4733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4731_);
lean_ctor_set(v___x_4733_, 1, v___x_4732_);
v___x_4734_ = l_Array_mkArray1___redArg(v___x_4733_);
v___y_4652_ = v___x_4725_;
v___y_4653_ = v___x_4726_;
v___y_4654_ = v_a_4716_;
v___y_4655_ = v___y_4697_;
v___y_4656_ = v___y_4707_;
v___y_4657_ = v___y_4706_;
v___y_4658_ = v___x_4729_;
v___y_4659_ = v___y_4710_;
v___y_4660_ = v___y_4709_;
v___y_4661_ = v_a_4717_;
v___y_4662_ = v___y_4711_;
v___y_4663_ = v___x_4734_;
goto v___jp_4651_;
}
else
{
lean_object* v___x_4735_; 
lean_dec(v___y_4699_);
v___x_4735_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4652_ = v___x_4725_;
v___y_4653_ = v___x_4726_;
v___y_4654_ = v_a_4716_;
v___y_4655_ = v___y_4697_;
v___y_4656_ = v___y_4707_;
v___y_4657_ = v___y_4706_;
v___y_4658_ = v___x_4729_;
v___y_4659_ = v___y_4710_;
v___y_4660_ = v___y_4709_;
v___y_4661_ = v_a_4717_;
v___y_4662_ = v___y_4711_;
v___y_4663_ = v___x_4735_;
goto v___jp_4651_;
}
}
}
}
v___jp_4738_:
{
lean_object* v_quotContext_4746_; lean_object* v_currMacroScope_4747_; lean_object* v_ref_4748_; lean_object* v___x_4749_; lean_object* v_a_4750_; lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4778_; 
v_quotContext_4746_ = lean_ctor_get(v___y_4744_, 1);
v_currMacroScope_4747_ = lean_ctor_get(v___y_4744_, 2);
v_ref_4748_ = lean_ctor_get(v___y_4744_, 5);
v___x_4749_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_ref_4748_, v___y_4744_, v___y_4745_);
v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
v_a_4751_ = lean_ctor_get(v___x_4749_, 1);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4753_ = v___x_4749_;
v_isShared_4754_ = v_isSharedCheck_4778_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_inc(v_a_4750_);
lean_dec(v___x_4749_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4778_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; uint8_t v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4764_; 
v___x_4755_ = lean_unsigned_to_nat(3u);
v___x_4756_ = l_Lean_Syntax_getArg(v___y_4740_, v___x_4755_);
lean_dec(v___y_4740_);
v___x_4757_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
lean_inc(v_currMacroScope_4747_);
lean_inc(v_quotContext_4746_);
v___x_4758_ = l_Lean_addMacroScope(v_quotContext_4746_, v___x_4757_, v_currMacroScope_4747_);
v___x_4759_ = 0;
v___x_4760_ = l_Lean_mkIdentFrom(v___y_4742_, v___x_4758_, v___x_4759_);
v___x_4761_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_4762_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v_a_4750_);
if (v_isShared_4754_ == 0)
{
lean_ctor_set_tag(v___x_4753_, 2);
lean_ctor_set(v___x_4753_, 1, v___x_4762_);
v___x_4764_ = v___x_4753_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4750_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v___x_4762_);
v___x_4764_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4765_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4766_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v_a_4750_, 2);
v___x_4767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4767_, 0, v_a_4750_);
lean_ctor_set(v___x_4767_, 1, v___x_4765_);
lean_ctor_set(v___x_4767_, 2, v___x_4766_);
v___x_4768_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc_ref(v___x_4767_);
v___x_4769_ = l_Lean_Syntax_node1(v_a_4750_, v___x_4768_, v___x_4767_);
if (lean_obj_tag(v_t_x3f_4743_) == 1)
{
lean_object* v_val_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v_val_4770_ = lean_ctor_get(v_t_x3f_4743_, 0);
lean_inc(v_val_4770_);
lean_dec_ref_known(v_t_x3f_4743_, 1);
v___x_4771_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4772_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v_a_4750_, 2);
v___x_4773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4773_, 0, v_a_4750_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
v___x_4774_ = l_Lean_Syntax_node2(v_a_4750_, v___x_4771_, v___x_4773_, v_val_4770_);
v___x_4775_ = l_Array_mkArray1___redArg(v___x_4774_);
v___y_4696_ = v___x_4767_;
v___y_4697_ = v_ref_4748_;
v___y_4698_ = v_a_4750_;
v___y_4699_ = v___y_4739_;
v___y_4700_ = v_a_4751_;
v___y_4701_ = v___x_4756_;
v___y_4702_ = v___y_4741_;
v___y_4703_ = v___x_4769_;
v___y_4704_ = v___y_4744_;
v___y_4705_ = v___x_4761_;
v___y_4706_ = v___y_4742_;
v___y_4707_ = v___x_4759_;
v___y_4708_ = v___x_4764_;
v___y_4709_ = v___x_4765_;
v___y_4710_ = v___x_4760_;
v___y_4711_ = v___x_4766_;
v___y_4712_ = v___x_4775_;
goto v___jp_4695_;
}
else
{
lean_object* v___x_4776_; 
lean_dec(v_t_x3f_4743_);
v___x_4776_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4696_ = v___x_4767_;
v___y_4697_ = v_ref_4748_;
v___y_4698_ = v_a_4750_;
v___y_4699_ = v___y_4739_;
v___y_4700_ = v_a_4751_;
v___y_4701_ = v___x_4756_;
v___y_4702_ = v___y_4741_;
v___y_4703_ = v___x_4769_;
v___y_4704_ = v___y_4744_;
v___y_4705_ = v___x_4761_;
v___y_4706_ = v___y_4742_;
v___y_4707_ = v___x_4759_;
v___y_4708_ = v___x_4764_;
v___y_4709_ = v___x_4765_;
v___y_4710_ = v___x_4760_;
v___y_4711_ = v___x_4766_;
v___y_4712_ = v___x_4776_;
goto v___jp_4695_;
}
}
}
}
v___jp_4780_:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; 
v___x_4784_ = lean_unsigned_to_nat(2u);
v___x_4785_ = l_Lean_Syntax_getArg(v_stx_4648_, v___x_4784_);
lean_dec(v_stx_4648_);
v___x_4786_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_4785_);
v___x_4787_ = l_Lean_Syntax_isOfKind(v___x_4785_, v___x_4786_);
if (v___x_4787_ == 0)
{
lean_object* v___x_4788_; 
lean_dec(v___x_4785_);
lean_dec(v_mutTk_x3f_4781_);
lean_dec(v_tk_4694_);
v___x_4788_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4783_);
return v___x_4788_;
}
else
{
lean_object* v___x_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; 
v___x_4789_ = l_Lean_Syntax_getArg(v___x_4785_, v___x_4693_);
v___x_4790_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4789_);
v___x_4791_ = l_Lean_Syntax_isOfKind(v___x_4789_, v___x_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; 
lean_dec(v___x_4789_);
lean_dec(v___x_4785_);
lean_dec(v_mutTk_x3f_4781_);
lean_dec(v_tk_4694_);
v___x_4792_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4783_);
return v___x_4792_;
}
else
{
lean_object* v___x_4793_; uint8_t v___x_4794_; 
v___x_4793_ = l_Lean_Syntax_getArg(v___x_4785_, v___x_4779_);
v___x_4794_ = l_Lean_Syntax_isNone(v___x_4793_);
if (v___x_4794_ == 0)
{
uint8_t v___x_4795_; 
lean_inc(v___x_4793_);
v___x_4795_ = l_Lean_Syntax_matchesNull(v___x_4793_, v___x_4779_);
if (v___x_4795_ == 0)
{
lean_object* v___x_4796_; 
lean_dec(v___x_4793_);
lean_dec(v___x_4789_);
lean_dec(v___x_4785_);
lean_dec(v_mutTk_x3f_4781_);
lean_dec(v_tk_4694_);
v___x_4796_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4783_);
return v___x_4796_;
}
else
{
lean_object* v___x_4797_; lean_object* v___x_4798_; uint8_t v___x_4799_; 
v___x_4797_ = l_Lean_Syntax_getArg(v___x_4793_, v___x_4693_);
lean_dec(v___x_4793_);
v___x_4798_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4797_);
v___x_4799_ = l_Lean_Syntax_isOfKind(v___x_4797_, v___x_4798_);
if (v___x_4799_ == 0)
{
lean_object* v___x_4800_; 
lean_dec(v___x_4797_);
lean_dec(v___x_4789_);
lean_dec(v___x_4785_);
lean_dec(v_mutTk_x3f_4781_);
lean_dec(v_tk_4694_);
v___x_4800_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4783_);
return v___x_4800_;
}
else
{
lean_object* v_t_x3f_4801_; lean_object* v___x_4802_; 
v_t_x3f_4801_ = l_Lean_Syntax_getArg(v___x_4797_, v___x_4779_);
lean_dec(v___x_4797_);
v___x_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4802_, 0, v_t_x3f_4801_);
v___y_4739_ = v_mutTk_x3f_4781_;
v___y_4740_ = v___x_4785_;
v___y_4741_ = v___x_4786_;
v___y_4742_ = v___x_4789_;
v_t_x3f_4743_ = v___x_4802_;
v___y_4744_ = v___y_4782_;
v___y_4745_ = v___y_4783_;
goto v___jp_4738_;
}
}
}
else
{
lean_object* v___x_4803_; 
lean_dec(v___x_4793_);
v___x_4803_ = lean_box(0);
v___y_4739_ = v_mutTk_x3f_4781_;
v___y_4740_ = v___x_4785_;
v___y_4741_ = v___x_4786_;
v___y_4742_ = v___x_4789_;
v_t_x3f_4743_ = v___x_4803_;
v___y_4744_ = v___y_4782_;
v___y_4745_ = v___y_4783_;
goto v___jp_4738_;
}
}
}
}
}
v___jp_4651_:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
lean_inc_ref_n(v___y_4662_, 3);
v___x_4664_ = l_Array_append___redArg(v___y_4662_, v___y_4663_);
lean_dec_ref(v___y_4663_);
lean_inc_n(v___y_4660_, 5);
lean_inc_n(v___y_4654_, 5);
v___x_4665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4665_, 0, v___y_4654_);
lean_ctor_set(v___x_4665_, 1, v___y_4660_);
lean_ctor_set(v___x_4665_, 2, v___x_4664_);
v___x_4666_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_4667_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
v___x_4668_ = l_Lean_Syntax_node1(v___y_4654_, v___x_4667_, v___y_4657_);
v___x_4669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4669_, 0, v___y_4654_);
lean_ctor_set(v___x_4669_, 1, v___y_4660_);
lean_ctor_set(v___x_4669_, 2, v___y_4662_);
v___x_4670_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4671_, 0, v___y_4654_);
lean_ctor_set(v___x_4671_, 1, v___x_4670_);
lean_inc_ref(v___x_4669_);
v___x_4672_ = l_Lean_Syntax_node5(v___y_4654_, v___x_4666_, v___x_4668_, v___x_4669_, v___x_4669_, v___x_4671_, v___y_4659_);
lean_inc(v___y_4653_);
v___x_4673_ = l_Lean_Syntax_node3(v___y_4654_, v___y_4653_, v___y_4658_, v___x_4665_, v___x_4672_);
v___x_4674_ = l_Lean_SourceInfo_fromRef(v___y_4655_, v___y_4656_);
v___x_4675_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_4676_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
lean_inc_n(v___x_4674_, 8);
v___x_4677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4674_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
v___x_4678_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_4679_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_4680_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4674_);
lean_ctor_set(v___x_4681_, 1, v___x_4680_);
v___x_4682_ = l_Lean_Syntax_node1(v___x_4674_, v___y_4660_, v___x_4681_);
v___x_4683_ = l_Lean_Syntax_node2(v___x_4674_, v___x_4679_, v___y_4652_, v___x_4682_);
v___x_4684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4674_);
lean_ctor_set(v___x_4684_, 1, v___y_4660_);
lean_ctor_set(v___x_4684_, 2, v___y_4662_);
v___x_4685_ = l_Lean_Syntax_node2(v___x_4674_, v___x_4679_, v___x_4673_, v___x_4684_);
v___x_4686_ = l_Lean_Syntax_node2(v___x_4674_, v___y_4660_, v___x_4683_, v___x_4685_);
v___x_4687_ = l_Lean_Syntax_node1(v___x_4674_, v___x_4678_, v___x_4686_);
v___x_4688_ = l_Lean_Syntax_node2(v___x_4674_, v___x_4675_, v___x_4677_, v___x_4687_);
v___x_4689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
lean_ctor_set(v___x_4689_, 1, v___y_4661_);
return v___x_4689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___boxed(lean_object* v_stx_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_Elab_Do_expandDoErasedArrow(v_stx_4811_, v_a_4812_, v_a_4813_);
lean_dec_ref(v_a_4812_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1(){
_start:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4822_ = l_Lean_Elab_macroAttribute;
v___x_4823_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
v___x_4824_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1));
v___x_4825_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoErasedArrow___boxed), 3, 0);
v___x_4826_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4822_, v___x_4823_, v___x_4824_, v___x_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___boxed(lean_object* v_a_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1();
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4835_, lean_object* v_dec_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_){
_start:
{
lean_object* v___x_4845_; uint8_t v___x_4846_; 
v___x_4845_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
lean_inc(v_stx_4835_);
v___x_4846_ = l_Lean_Syntax_isOfKind(v_stx_4835_, v___x_4845_);
if (v___x_4846_ == 0)
{
lean_object* v___x_4847_; 
lean_dec_ref(v_dec_4836_);
lean_dec(v_stx_4835_);
v___x_4847_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4847_;
}
else
{
lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; uint8_t v___x_4851_; 
v___x_4848_ = lean_unsigned_to_nat(1u);
v___x_4849_ = l_Lean_Syntax_getArg(v_stx_4835_, v___x_4848_);
v___x_4850_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v___x_4849_);
v___x_4851_ = l_Lean_Syntax_isOfKind(v___x_4849_, v___x_4850_);
if (v___x_4851_ == 0)
{
lean_object* v___x_4852_; 
lean_dec(v___x_4849_);
lean_dec_ref(v_dec_4836_);
lean_dec(v_stx_4835_);
v___x_4852_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4852_;
}
else
{
lean_object* v___x_4853_; lean_object* v_decl_4854_; lean_object* v___x_4855_; uint8_t v___x_4856_; 
v___x_4853_ = lean_unsigned_to_nat(2u);
v_decl_4854_ = l_Lean_Syntax_getArg(v_stx_4835_, v___x_4853_);
v___x_4855_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4854_);
v___x_4856_ = l_Lean_Syntax_isOfKind(v_decl_4854_, v___x_4855_);
if (v___x_4856_ == 0)
{
lean_object* v___x_4857_; 
lean_dec(v_decl_4854_);
lean_dec(v___x_4849_);
lean_dec_ref(v_dec_4836_);
lean_dec(v_stx_4835_);
v___x_4857_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4857_;
}
else
{
lean_object* v___x_4858_; lean_object* v_tk_4859_; uint8_t v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4858_ = lean_unsigned_to_nat(0u);
v_tk_4859_ = l_Lean_Syntax_getArg(v_stx_4835_, v___x_4858_);
lean_dec(v_stx_4835_);
v___x_4860_ = 0;
v___x_4861_ = lean_box(0);
v___x_4862_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
lean_ctor_set_uint8(v___x_4862_, sizeof(void*)*1, v___x_4856_);
lean_ctor_set_uint8(v___x_4862_, sizeof(void*)*1 + 1, v___x_4860_);
lean_ctor_set_uint8(v___x_4862_, sizeof(void*)*1 + 2, v___x_4860_);
lean_ctor_set_uint8(v___x_4862_, sizeof(void*)*1 + 3, v___x_4860_);
lean_ctor_set_uint8(v___x_4862_, sizeof(void*)*1 + 4, v___x_4860_);
v___x_4863_ = l_Lean_Elab_Term_mkLetConfig(v___x_4849_, v___x_4862_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v___x_4865_ = lean_box(1);
v___x_4866_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4864_, v___x_4865_, v_decl_4854_, v_tk_4859_, v_dec_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_);
return v___x_4866_;
}
else
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4874_; 
lean_dec(v_tk_4859_);
lean_dec(v_decl_4854_);
lean_dec_ref(v_dec_4836_);
v_a_4867_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4869_ = v___x_4863_;
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4863_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4872_; 
if (v_isShared_4870_ == 0)
{
v___x_4872_ = v___x_4869_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4875_, lean_object* v_dec_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_Elab_Do_elabDoHave(v_stx_4875_, v_dec_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
lean_dec(v_a_4879_);
lean_dec_ref(v_a_4878_);
lean_dec_ref(v_a_4877_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4893_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4894_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
v___x_4895_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4896_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4897_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4893_, v___x_4894_, v___x_4895_, v___x_4896_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4902_, lean_object* v___x_4903_, lean_object* v___x_4904_, lean_object* v___x_4905_, lean_object* v_decls_4906_, lean_object* v_a_4907_, uint8_t v___x_4908_, lean_object* v_body_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v_ref_4918_; uint8_t v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v_ref_4918_ = lean_ctor_get(v___y_4915_, 2);
v___x_4919_ = 0;
v___x_4920_ = l_Lean_SourceInfo_fromRef(v_ref_4918_, v___x_4919_);
v___x_4921_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4922_ = l_Lean_Name_mkStr4(v___x_4902_, v___x_4903_, v___x_4904_, v___x_4921_);
v___x_4923_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4920_, 4);
v___x_4924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4920_);
lean_ctor_set(v___x_4924_, 1, v___x_4923_);
v___x_4925_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4920_);
lean_ctor_set(v___x_4926_, 1, v___x_4925_);
v___x_4927_ = l_Lean_Syntax_node2(v___x_4920_, v___x_4905_, v___x_4924_, v___x_4926_);
v___x_4928_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4920_);
lean_ctor_set(v___x_4929_, 1, v___x_4928_);
v___x_4930_ = l_Lean_Syntax_node4(v___x_4920_, v___x_4922_, v___x_4927_, v_decls_4906_, v___x_4929_, v_body_4909_);
v___x_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4931_, 0, v_a_4907_);
v___x_4932_ = l_Lean_Elab_Term_elabTerm(v___x_4930_, v___x_4931_, v___x_4908_, v___x_4908_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4933_, lean_object* v___x_4934_, lean_object* v___x_4935_, lean_object* v___x_4936_, lean_object* v_decls_4937_, lean_object* v_a_4938_, lean_object* v___x_4939_, lean_object* v_body_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
uint8_t v___x_4496__boxed_4949_; lean_object* v_res_4950_; 
v___x_4496__boxed_4949_ = lean_unbox(v___x_4939_);
v_res_4950_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4933_, v___x_4934_, v___x_4935_, v___x_4936_, v_decls_4937_, v_a_4938_, v___x_4496__boxed_4949_, v_body_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
lean_dec(v___y_4947_);
lean_dec_ref(v___y_4946_);
lean_dec(v___y_4945_);
lean_dec_ref(v___y_4944_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec_ref(v___y_4941_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4951_, lean_object* v_a_4952_){
_start:
{
if (lean_obj_tag(v_a_4951_) == 0)
{
lean_object* v___x_4953_; 
v___x_4953_ = l_List_reverse___redArg(v_a_4952_);
return v___x_4953_;
}
else
{
lean_object* v_head_4954_; lean_object* v_tail_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4964_; 
v_head_4954_ = lean_ctor_get(v_a_4951_, 0);
v_tail_4955_ = lean_ctor_get(v_a_4951_, 1);
v_isSharedCheck_4964_ = !lean_is_exclusive(v_a_4951_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4957_ = v_a_4951_;
v_isShared_4958_ = v_isSharedCheck_4964_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_tail_4955_);
lean_inc(v_head_4954_);
lean_dec(v_a_4951_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4964_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4959_; lean_object* v___x_4961_; 
v___x_4959_ = l_Lean_MessageData_ofSyntax(v_head_4954_);
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 1, v_a_4952_);
lean_ctor_set(v___x_4957_, 0, v___x_4959_);
v___x_4961_ = v___x_4957_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4959_);
lean_ctor_set(v_reuseFailAlloc_4963_, 1, v_a_4952_);
v___x_4961_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
v_a_4951_ = v_tail_4955_;
v_a_4952_ = v___x_4961_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4981_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4982_ = l_Lean_stringToMessageData(v___x_4981_);
return v___x_4982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4983_, lean_object* v_dec_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; uint8_t v___x_4997_; 
v___x_4993_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4994_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4995_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4996_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4983_);
v___x_4997_ = l_Lean_Syntax_isOfKind(v_stx_4983_, v___x_4996_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; 
lean_dec_ref(v_dec_4984_);
lean_dec(v_stx_4983_);
v___x_4998_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4998_;
}
else
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; uint8_t v___x_5002_; 
v___x_4999_ = lean_unsigned_to_nat(0u);
v___x_5000_ = l_Lean_Syntax_getArg(v_stx_4983_, v___x_4999_);
v___x_5001_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_5000_);
v___x_5002_ = l_Lean_Syntax_isOfKind(v___x_5000_, v___x_5001_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; 
lean_dec(v___x_5000_);
lean_dec_ref(v_dec_4984_);
lean_dec(v_stx_4983_);
v___x_5003_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5003_;
}
else
{
lean_object* v___x_5004_; lean_object* v_decls_5005_; lean_object* v___x_5006_; uint8_t v___x_5007_; 
v___x_5004_ = lean_unsigned_to_nat(1u);
v_decls_5005_ = l_Lean_Syntax_getArg(v_stx_4983_, v___x_5004_);
lean_dec(v_stx_4983_);
v___x_5006_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_5005_);
v___x_5007_ = l_Lean_Syntax_isOfKind(v_decls_5005_, v___x_5006_);
if (v___x_5007_ == 0)
{
lean_object* v___x_5008_; 
lean_dec(v_decls_5005_);
lean_dec(v___x_5000_);
lean_dec_ref(v_dec_4984_);
v___x_5008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5008_;
}
else
{
lean_object* v_tk_5009_; lean_object* v___x_5010_; 
v_tk_5009_ = l_Lean_Syntax_getArg(v___x_5000_, v___x_4999_);
lean_dec(v___x_5000_);
v___x_5010_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4984_, v_tk_5009_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
lean_dec(v_tk_5009_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v_a_5011_; lean_object* v___x_5012_; 
v_a_5011_ = lean_ctor_get(v___x_5010_, 0);
lean_inc(v_a_5011_);
lean_dec_ref_known(v___x_5010_, 1);
lean_inc(v_decls_5005_);
v___x_5012_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_5005_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v_doBlockResultType_5014_; lean_object* v___x_5015_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_a_5013_);
lean_dec_ref_known(v___x_5012_, 1);
v_doBlockResultType_5014_ = lean_ctor_get(v_a_4985_, 3);
lean_inc_ref(v_doBlockResultType_5014_);
v___x_5015_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_5014_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v_a_5016_; lean_object* v___x_5017_; lean_object* v___f_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
lean_inc(v_a_5016_);
lean_dec_ref_known(v___x_5015_, 1);
v___x_5017_ = lean_box(v___x_5007_);
v___f_5018_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_5018_, 0, v___x_4993_);
lean_closure_set(v___f_5018_, 1, v___x_4994_);
lean_closure_set(v___f_5018_, 2, v___x_4995_);
lean_closure_set(v___f_5018_, 3, v___x_5001_);
lean_closure_set(v___f_5018_, 4, v_decls_5005_);
lean_closure_set(v___f_5018_, 5, v_a_5016_);
lean_closure_set(v___f_5018_, 6, v___x_5017_);
v___x_5019_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_5020_ = lean_array_to_list(v_a_5013_);
v___x_5021_ = lean_box(0);
v___x_5022_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_5020_, v___x_5021_);
v___x_5023_ = l_Lean_MessageData_ofList(v___x_5022_);
v___x_5024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5024_, 0, v___x_5019_);
lean_ctor_set(v___x_5024_, 1, v___x_5023_);
v___x_5025_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_5025_, 0, v_a_5011_);
v___x_5026_ = lean_box(0);
v___x_5027_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_5024_, v___x_5025_, v___f_5018_, v___x_5026_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
return v___x_5027_;
}
else
{
lean_dec(v_a_5013_);
lean_dec(v_a_5011_);
lean_dec(v_decls_5005_);
return v___x_5015_;
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
lean_dec(v_a_5011_);
lean_dec(v_decls_5005_);
v_a_5028_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_5012_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_5012_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5033_; 
if (v_isShared_5031_ == 0)
{
v___x_5033_ = v___x_5030_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_5028_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
else
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
lean_dec(v_decls_5005_);
v_a_5036_ = lean_ctor_get(v___x_5010_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5010_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5038_ = v___x_5010_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_5010_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5041_; 
if (v_isShared_5039_ == 0)
{
v___x_5041_ = v___x_5038_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5036_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_5044_, lean_object* v_dec_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_5044_, v_dec_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_);
lean_dec(v_a_5052_);
lean_dec_ref(v_a_5051_);
lean_dec(v_a_5050_);
lean_dec_ref(v_a_5049_);
lean_dec(v_a_5048_);
lean_dec_ref(v_a_5047_);
lean_dec_ref(v_a_5046_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5062_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5063_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_5064_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_5065_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_5066_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5062_, v___x_5063_, v___x_5064_, v___x_5065_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_5075_, lean_object* v_dec_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_){
_start:
{
lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v___y_5091_; lean_object* v___y_5092_; lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___y_5096_; lean_object* v___y_5097_; lean_object* v___y_5098_; uint8_t v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___x_5118_; uint8_t v___x_5119_; 
v___x_5118_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
lean_inc(v_stx_5075_);
v___x_5119_ = l_Lean_Syntax_isOfKind(v_stx_5075_, v___x_5118_);
if (v___x_5119_ == 0)
{
lean_object* v___x_5120_; 
lean_dec_ref(v_dec_5076_);
lean_dec(v_stx_5075_);
v___x_5120_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5120_;
}
else
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; uint8_t v___x_5124_; 
v___x_5121_ = lean_unsigned_to_nat(0u);
v___x_5122_ = l_Lean_Syntax_getArg(v_stx_5075_, v___x_5121_);
lean_dec(v_stx_5075_);
v___x_5123_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_5122_);
v___x_5124_ = l_Lean_Syntax_isOfKind(v___x_5122_, v___x_5123_);
if (v___x_5124_ == 0)
{
if (v___x_5124_ == 0)
{
lean_object* v___x_5136_; uint8_t v___x_5137_; 
v___x_5136_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5122_);
v___x_5137_ = l_Lean_Syntax_isOfKind(v___x_5122_, v___x_5136_);
if (v___x_5137_ == 0)
{
lean_object* v___x_5138_; 
lean_dec(v___x_5122_);
lean_dec_ref(v_dec_5076_);
v___x_5138_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5138_;
}
else
{
goto v___jp_5125_;
}
}
else
{
goto v___jp_5125_;
}
}
else
{
lean_object* v___x_5139_; lean_object* v___x_5140_; uint8_t v___x_5141_; 
v___x_5139_ = l_Lean_Syntax_getArg(v___x_5122_, v___x_5121_);
v___x_5140_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5139_);
v___x_5141_ = l_Lean_Syntax_isOfKind(v___x_5139_, v___x_5140_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; 
lean_dec(v___x_5139_);
lean_dec(v___x_5122_);
lean_dec_ref(v_dec_5076_);
v___x_5142_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5142_;
}
else
{
lean_object* v___x_5143_; lean_object* v_xType_x3f_5145_; lean_object* v___y_5146_; lean_object* v___y_5147_; lean_object* v___y_5148_; lean_object* v___y_5149_; lean_object* v___y_5150_; lean_object* v___y_5151_; lean_object* v___y_5152_; lean_object* v___x_5172_; uint8_t v___x_5173_; 
v___x_5143_ = l_Lean_Syntax_getArg(v___x_5139_, v___x_5121_);
lean_dec(v___x_5139_);
v___x_5172_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5143_);
v___x_5173_ = l_Lean_Syntax_isOfKind(v___x_5143_, v___x_5172_);
if (v___x_5173_ == 0)
{
lean_object* v___x_5174_; 
lean_dec(v___x_5143_);
lean_dec(v___x_5122_);
lean_dec_ref(v_dec_5076_);
v___x_5174_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5174_;
}
else
{
lean_object* v___x_5175_; lean_object* v___x_5176_; uint8_t v___x_5177_; 
v___x_5175_ = lean_unsigned_to_nat(1u);
v___x_5176_ = l_Lean_Syntax_getArg(v___x_5122_, v___x_5175_);
v___x_5177_ = l_Lean_Syntax_matchesNull(v___x_5176_, v___x_5121_);
if (v___x_5177_ == 0)
{
lean_object* v___x_5178_; 
lean_dec(v___x_5143_);
lean_dec(v___x_5122_);
lean_dec_ref(v_dec_5076_);
v___x_5178_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5178_;
}
else
{
lean_object* v___x_5179_; lean_object* v___x_5180_; uint8_t v___x_5181_; 
v___x_5179_ = lean_unsigned_to_nat(2u);
v___x_5180_ = l_Lean_Syntax_getArg(v___x_5122_, v___x_5179_);
v___x_5181_ = l_Lean_Syntax_isNone(v___x_5180_);
if (v___x_5181_ == 0)
{
uint8_t v___x_5182_; 
lean_inc(v___x_5180_);
v___x_5182_ = l_Lean_Syntax_matchesNull(v___x_5180_, v___x_5175_);
if (v___x_5182_ == 0)
{
lean_object* v___x_5183_; 
lean_dec(v___x_5180_);
lean_dec(v___x_5143_);
lean_dec(v___x_5122_);
lean_dec_ref(v_dec_5076_);
v___x_5183_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5183_;
}
else
{
lean_object* v___x_5184_; lean_object* v___x_5185_; uint8_t v___x_5186_; 
v___x_5184_ = l_Lean_Syntax_getArg(v___x_5180_, v___x_5121_);
lean_dec(v___x_5180_);
v___x_5185_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5184_);
v___x_5186_ = l_Lean_Syntax_isOfKind(v___x_5184_, v___x_5185_);
if (v___x_5186_ == 0)
{
lean_object* v___x_5187_; 
lean_dec(v___x_5184_);
lean_dec(v___x_5143_);
lean_dec(v___x_5122_);
lean_dec_ref(v_dec_5076_);
v___x_5187_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5187_;
}
else
{
lean_object* v_xType_x3f_5188_; lean_object* v___x_5189_; 
v_xType_x3f_5188_ = l_Lean_Syntax_getArg(v___x_5184_, v___x_5175_);
lean_dec(v___x_5184_);
v___x_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5189_, 0, v_xType_x3f_5188_);
v_xType_x3f_5145_ = v___x_5189_;
v___y_5146_ = v_a_5077_;
v___y_5147_ = v_a_5078_;
v___y_5148_ = v_a_5079_;
v___y_5149_ = v_a_5080_;
v___y_5150_ = v_a_5081_;
v___y_5151_ = v_a_5082_;
v___y_5152_ = v_a_5083_;
goto v___jp_5144_;
}
}
}
else
{
lean_object* v___x_5190_; 
lean_dec(v___x_5180_);
v___x_5190_ = lean_box(0);
v_xType_x3f_5145_ = v___x_5190_;
v___y_5146_ = v_a_5077_;
v___y_5147_ = v_a_5078_;
v___y_5148_ = v_a_5079_;
v___y_5149_ = v_a_5080_;
v___y_5150_ = v_a_5081_;
v___y_5151_ = v_a_5082_;
v___y_5152_ = v_a_5083_;
goto v___jp_5144_;
}
}
}
v___jp_5144_:
{
lean_object* v_ref_5153_; lean_object* v___x_5154_; lean_object* v_tk_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; uint8_t v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
v_ref_5153_ = lean_ctor_get(v___y_5151_, 2);
v___x_5154_ = lean_unsigned_to_nat(3u);
v_tk_5155_ = l_Lean_Syntax_getArg(v___x_5122_, v___x_5154_);
v___x_5156_ = lean_unsigned_to_nat(4u);
v___x_5157_ = l_Lean_Syntax_getArg(v___x_5122_, v___x_5156_);
lean_dec(v___x_5122_);
v___x_5158_ = 0;
v___x_5159_ = l_Lean_SourceInfo_fromRef(v_ref_5153_, v___x_5158_);
v___x_5160_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5159_, 2);
v___x_5161_ = l_Lean_Syntax_node1(v___x_5159_, v___x_5140_, v___x_5143_);
v___x_5162_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5163_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5159_);
lean_ctor_set(v___x_5164_, 1, v___x_5162_);
lean_ctor_set(v___x_5164_, 2, v___x_5163_);
if (lean_obj_tag(v_xType_x3f_5145_) == 1)
{
lean_object* v_val_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v_val_5165_ = lean_ctor_get(v_xType_x3f_5145_, 0);
lean_inc(v_val_5165_);
lean_dec_ref_known(v_xType_x3f_5145_, 1);
v___x_5166_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5167_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5159_, 2);
v___x_5168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5159_);
lean_ctor_set(v___x_5168_, 1, v___x_5167_);
v___x_5169_ = l_Lean_Syntax_node2(v___x_5159_, v___x_5166_, v___x_5168_, v_val_5165_);
v___x_5170_ = l_Array_mkArray1___redArg(v___x_5169_);
v___y_5086_ = v___x_5159_;
v___y_5087_ = v___x_5157_;
v___y_5088_ = v___y_5151_;
v___y_5089_ = v_tk_5155_;
v___y_5090_ = v___y_5146_;
v___y_5091_ = v___x_5160_;
v___y_5092_ = v___y_5152_;
v___y_5093_ = v___x_5163_;
v___y_5094_ = v___y_5149_;
v___y_5095_ = v___x_5164_;
v___y_5096_ = v___y_5148_;
v___y_5097_ = v___x_5161_;
v___y_5098_ = v___x_5162_;
v___y_5099_ = v___x_5158_;
v___y_5100_ = v___y_5150_;
v___y_5101_ = v___y_5147_;
v___y_5102_ = v___x_5170_;
goto v___jp_5085_;
}
else
{
lean_object* v___x_5171_; 
lean_dec(v_xType_x3f_5145_);
v___x_5171_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_5086_ = v___x_5159_;
v___y_5087_ = v___x_5157_;
v___y_5088_ = v___y_5151_;
v___y_5089_ = v_tk_5155_;
v___y_5090_ = v___y_5146_;
v___y_5091_ = v___x_5160_;
v___y_5092_ = v___y_5152_;
v___y_5093_ = v___x_5163_;
v___y_5094_ = v___y_5149_;
v___y_5095_ = v___x_5164_;
v___y_5096_ = v___y_5148_;
v___y_5097_ = v___x_5161_;
v___y_5098_ = v___x_5162_;
v___y_5099_ = v___x_5158_;
v___y_5100_ = v___y_5150_;
v___y_5101_ = v___y_5147_;
v___y_5102_ = v___x_5171_;
goto v___jp_5085_;
}
}
}
}
v___jp_5125_:
{
lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v_decl_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; 
v___x_5126_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5127_ = lean_unsigned_to_nat(1u);
v___x_5128_ = lean_mk_empty_array_with_capacity(v___x_5127_);
v___x_5129_ = lean_array_push(v___x_5128_, v___x_5122_);
v___x_5130_ = lean_box(2);
v_decl_5131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5131_, 0, v___x_5130_);
lean_ctor_set(v_decl_5131_, 1, v___x_5126_);
lean_ctor_set(v_decl_5131_, 2, v___x_5129_);
v___x_5132_ = lean_box(0);
v___x_5133_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5133_, 0, v___x_5132_);
lean_ctor_set_uint8(v___x_5133_, sizeof(void*)*1, v___x_5124_);
lean_ctor_set_uint8(v___x_5133_, sizeof(void*)*1 + 1, v___x_5124_);
lean_ctor_set_uint8(v___x_5133_, sizeof(void*)*1 + 2, v___x_5124_);
lean_ctor_set_uint8(v___x_5133_, sizeof(void*)*1 + 3, v___x_5124_);
lean_ctor_set_uint8(v___x_5133_, sizeof(void*)*1 + 4, v___x_5124_);
v___x_5134_ = lean_box(2);
lean_inc_ref(v_decl_5131_);
v___x_5135_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5133_, v___x_5134_, v_decl_5131_, v_decl_5131_, v_dec_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_);
return v___x_5135_;
}
}
v___jp_5085_:
{
lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_inc_ref(v___y_5093_);
v___x_5103_ = l_Array_append___redArg(v___y_5093_, v___y_5102_);
lean_dec_ref(v___y_5102_);
lean_inc(v___y_5098_);
lean_inc_n(v___y_5086_, 2);
v___x_5104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5104_, 0, v___y_5086_);
lean_ctor_set(v___x_5104_, 1, v___y_5098_);
lean_ctor_set(v___x_5104_, 2, v___x_5103_);
v___x_5105_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5106_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5106_, 0, v___y_5086_);
lean_ctor_set(v___x_5106_, 1, v___x_5105_);
lean_inc(v___y_5091_);
v___x_5107_ = l_Lean_Syntax_node5(v___y_5086_, v___y_5091_, v___y_5097_, v___y_5095_, v___x_5104_, v___x_5106_, v___y_5087_);
v___x_5108_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5109_ = lean_unsigned_to_nat(1u);
v___x_5110_ = lean_mk_empty_array_with_capacity(v___x_5109_);
v___x_5111_ = lean_array_push(v___x_5110_, v___x_5107_);
v___x_5112_ = lean_box(2);
v___x_5113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5113_, 0, v___x_5112_);
lean_ctor_set(v___x_5113_, 1, v___x_5108_);
lean_ctor_set(v___x_5113_, 2, v___x_5111_);
v___x_5114_ = lean_box(0);
v___x_5115_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5115_, 0, v___x_5114_);
lean_ctor_set_uint8(v___x_5115_, sizeof(void*)*1, v___y_5099_);
lean_ctor_set_uint8(v___x_5115_, sizeof(void*)*1 + 1, v___y_5099_);
lean_ctor_set_uint8(v___x_5115_, sizeof(void*)*1 + 2, v___y_5099_);
lean_ctor_set_uint8(v___x_5115_, sizeof(void*)*1 + 3, v___y_5099_);
lean_ctor_set_uint8(v___x_5115_, sizeof(void*)*1 + 4, v___y_5099_);
v___x_5116_ = lean_box(2);
v___x_5117_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5115_, v___x_5116_, v___x_5113_, v___y_5089_, v_dec_5076_, v___y_5090_, v___y_5101_, v___y_5096_, v___y_5094_, v___y_5100_, v___y_5088_, v___y_5092_);
return v___x_5117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5191_, lean_object* v_dec_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5191_, v_dec_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_, v_a_5198_, v_a_5199_);
lean_dec(v_a_5199_);
lean_dec_ref(v_a_5198_);
lean_dec(v_a_5197_);
lean_dec_ref(v_a_5196_);
lean_dec(v_a_5195_);
lean_dec_ref(v_a_5194_);
lean_dec_ref(v_a_5193_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
v___x_5209_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5210_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_5211_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5212_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5213_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5209_, v___x_5210_, v___x_5211_, v___x_5212_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5214_){
_start:
{
lean_object* v_res_5215_; 
v_res_5215_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_){
_start:
{
uint8_t v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
v___x_5225_ = 0;
v___x_5226_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5216_, v___x_5225_);
v___x_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5226_);
return v___x_5227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec_ref(v___y_5229_);
lean_dec(v_____do__lift_5228_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5238_, size_t v_sz_5239_, size_t v_i_5240_, lean_object* v_b_5241_, lean_object* v___y_5242_){
_start:
{
uint8_t v___x_5244_; 
v___x_5244_ = lean_usize_dec_lt(v_i_5240_, v_sz_5239_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5245_; 
v___x_5245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5245_, 0, v_b_5241_);
return v___x_5245_;
}
else
{
lean_object* v_ref_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v_a_5249_; uint8_t v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; size_t v___x_5283_; size_t v___x_5284_; 
v_ref_5246_ = lean_ctor_get(v___y_5242_, 2);
v___x_5247_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5248_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5249_ = lean_array_uget_borrowed(v_as_5238_, v_i_5240_);
v___x_5250_ = 0;
v___x_5251_ = l_Lean_SourceInfo_fromRef(v_ref_5246_, v___x_5250_);
v___x_5252_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5253_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5254_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5255_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5251_, 17);
v___x_5256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5256_, 0, v___x_5251_);
lean_ctor_set(v___x_5256_, 1, v___x_5255_);
v___x_5257_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5258_, 0, v___x_5251_);
lean_ctor_set(v___x_5258_, 1, v___x_5257_);
v___x_5259_ = l_Lean_Syntax_node1(v___x_5251_, v___x_5252_, v___x_5258_);
v___x_5260_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5251_);
lean_ctor_set(v___x_5261_, 1, v___x_5252_);
lean_ctor_set(v___x_5261_, 2, v___x_5260_);
lean_inc_ref_n(v___x_5261_, 3);
v___x_5262_ = l_Lean_Syntax_node1(v___x_5251_, v___x_5247_, v___x_5261_);
v___x_5263_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5264_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5265_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5249_, 2);
v___x_5266_ = l_Lean_Syntax_node1(v___x_5251_, v___x_5265_, v_a_5249_);
v___x_5267_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5268_, 0, v___x_5251_);
lean_ctor_set(v___x_5268_, 1, v___x_5267_);
v___x_5269_ = l_Lean_Syntax_node5(v___x_5251_, v___x_5264_, v___x_5266_, v___x_5261_, v___x_5261_, v___x_5268_, v_a_5249_);
v___x_5270_ = l_Lean_Syntax_node1(v___x_5251_, v___x_5263_, v___x_5269_);
v___x_5271_ = l_Lean_Syntax_node4(v___x_5251_, v___x_5254_, v___x_5256_, v___x_5259_, v___x_5262_, v___x_5270_);
v___x_5272_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5273_, 0, v___x_5251_);
lean_ctor_set(v___x_5273_, 1, v___x_5272_);
v___x_5274_ = l_Lean_Syntax_node1(v___x_5251_, v___x_5252_, v___x_5273_);
v___x_5275_ = l_Lean_Syntax_node2(v___x_5251_, v___x_5253_, v___x_5271_, v___x_5274_);
v___x_5276_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5277_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5251_);
lean_ctor_set(v___x_5278_, 1, v___x_5277_);
v___x_5279_ = l_Lean_Syntax_node2(v___x_5251_, v___x_5276_, v___x_5278_, v_b_5241_);
v___x_5280_ = l_Lean_Syntax_node2(v___x_5251_, v___x_5253_, v___x_5279_, v___x_5261_);
v___x_5281_ = l_Lean_Syntax_node2(v___x_5251_, v___x_5252_, v___x_5275_, v___x_5280_);
v___x_5282_ = l_Lean_Syntax_node1(v___x_5251_, v___x_5248_, v___x_5281_);
v___x_5283_ = ((size_t)1ULL);
v___x_5284_ = lean_usize_add(v_i_5240_, v___x_5283_);
v_i_5240_ = v___x_5284_;
v_b_5241_ = v___x_5282_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5286_, lean_object* v_sz_5287_, lean_object* v_i_5288_, lean_object* v_b_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
size_t v_sz_boxed_5292_; size_t v_i_boxed_5293_; lean_object* v_res_5294_; 
v_sz_boxed_5292_ = lean_unbox_usize(v_sz_5287_);
lean_dec(v_sz_5287_);
v_i_boxed_5293_ = lean_unbox_usize(v_i_5288_);
lean_dec(v_i_5288_);
v_res_5294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5286_, v_sz_boxed_5292_, v_i_boxed_5293_, v_b_5289_, v___y_5290_);
lean_dec_ref(v___y_5290_);
lean_dec_ref(v_as_5286_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5295_, size_t v_sz_5296_, size_t v_i_5297_, lean_object* v_b_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
uint8_t v___x_5307_; 
v___x_5307_ = lean_usize_dec_lt(v_i_5297_, v_sz_5296_);
if (v___x_5307_ == 0)
{
lean_object* v___x_5308_; 
v___x_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5308_, 0, v_b_5298_);
return v___x_5308_;
}
else
{
lean_object* v_ref_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v_a_5312_; uint8_t v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; size_t v___x_5346_; size_t v___x_5347_; lean_object* v___x_5348_; 
v_ref_5309_ = lean_ctor_get(v___y_5304_, 2);
v___x_5310_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5311_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5312_ = lean_array_uget_borrowed(v_as_5295_, v_i_5297_);
v___x_5313_ = 0;
v___x_5314_ = l_Lean_SourceInfo_fromRef(v_ref_5309_, v___x_5313_);
v___x_5315_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5316_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5317_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5318_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5314_, 17);
v___x_5319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5319_, 0, v___x_5314_);
lean_ctor_set(v___x_5319_, 1, v___x_5318_);
v___x_5320_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5314_);
lean_ctor_set(v___x_5321_, 1, v___x_5320_);
v___x_5322_ = l_Lean_Syntax_node1(v___x_5314_, v___x_5315_, v___x_5321_);
v___x_5323_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5314_);
lean_ctor_set(v___x_5324_, 1, v___x_5315_);
lean_ctor_set(v___x_5324_, 2, v___x_5323_);
lean_inc_ref_n(v___x_5324_, 3);
v___x_5325_ = l_Lean_Syntax_node1(v___x_5314_, v___x_5310_, v___x_5324_);
v___x_5326_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5327_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5328_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5312_, 2);
v___x_5329_ = l_Lean_Syntax_node1(v___x_5314_, v___x_5328_, v_a_5312_);
v___x_5330_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5314_);
lean_ctor_set(v___x_5331_, 1, v___x_5330_);
v___x_5332_ = l_Lean_Syntax_node5(v___x_5314_, v___x_5327_, v___x_5329_, v___x_5324_, v___x_5324_, v___x_5331_, v_a_5312_);
v___x_5333_ = l_Lean_Syntax_node1(v___x_5314_, v___x_5326_, v___x_5332_);
v___x_5334_ = l_Lean_Syntax_node4(v___x_5314_, v___x_5317_, v___x_5319_, v___x_5322_, v___x_5325_, v___x_5333_);
v___x_5335_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5336_, 0, v___x_5314_);
lean_ctor_set(v___x_5336_, 1, v___x_5335_);
v___x_5337_ = l_Lean_Syntax_node1(v___x_5314_, v___x_5315_, v___x_5336_);
v___x_5338_ = l_Lean_Syntax_node2(v___x_5314_, v___x_5316_, v___x_5334_, v___x_5337_);
v___x_5339_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5340_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5314_);
lean_ctor_set(v___x_5341_, 1, v___x_5340_);
v___x_5342_ = l_Lean_Syntax_node2(v___x_5314_, v___x_5339_, v___x_5341_, v_b_5298_);
v___x_5343_ = l_Lean_Syntax_node2(v___x_5314_, v___x_5316_, v___x_5342_, v___x_5324_);
v___x_5344_ = l_Lean_Syntax_node2(v___x_5314_, v___x_5315_, v___x_5338_, v___x_5343_);
v___x_5345_ = l_Lean_Syntax_node1(v___x_5314_, v___x_5311_, v___x_5344_);
v___x_5346_ = ((size_t)1ULL);
v___x_5347_ = lean_usize_add(v_i_5297_, v___x_5346_);
v___x_5348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5295_, v_sz_5296_, v___x_5347_, v___x_5345_, v___y_5304_);
return v___x_5348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5349_, lean_object* v_sz_5350_, lean_object* v_i_5351_, lean_object* v_b_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_){
_start:
{
size_t v_sz_boxed_5361_; size_t v_i_boxed_5362_; lean_object* v_res_5363_; 
v_sz_boxed_5361_ = lean_unbox_usize(v_sz_5350_);
lean_dec(v_sz_5350_);
v_i_boxed_5362_ = lean_unbox_usize(v_i_5351_);
lean_dec(v_i_5351_);
v_res_5363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5349_, v_sz_boxed_5361_, v_i_boxed_5362_, v_b_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
lean_dec(v___y_5359_);
lean_dec_ref(v___y_5358_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec_ref(v_as_5349_);
return v_res_5363_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5403_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5404_ = l_String_toRawSubstring_x27(v___x_5403_);
return v___x_5404_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5418_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5419_ = l_String_toRawSubstring_x27(v___x_5418_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5436_, lean_object* v_dec_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_){
_start:
{
lean_object* v___x_5446_; uint8_t v___x_5447_; 
v___x_5446_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
lean_inc(v_stx_5436_);
v___x_5447_ = l_Lean_Syntax_isOfKind(v_stx_5436_, v___x_5446_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5448_; 
lean_dec_ref(v_dec_5437_);
lean_dec(v_stx_5436_);
v___x_5448_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5448_;
}
else
{
uint8_t v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v_body_5455_; lean_object* v___y_5456_; lean_object* v___y_5457_; lean_object* v___y_5458_; lean_object* v___y_5459_; lean_object* v___y_5460_; lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___y_5536_; lean_object* v___y_5537_; lean_object* v___y_5538_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; uint8_t v___y_5544_; lean_object* v___y_5545_; lean_object* v___y_5546_; lean_object* v___y_5547_; lean_object* v___y_5548_; lean_object* v___y_5549_; lean_object* v_a_5550_; lean_object* v___y_5564_; lean_object* v___y_5565_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5569_; lean_object* v___y_5570_; lean_object* v___y_5571_; lean_object* v___y_5572_; lean_object* v___y_5573_; lean_object* v___y_5574_; lean_object* v___y_5575_; lean_object* v___y_5576_; lean_object* v_mutTk_x3f_5649_; lean_object* v___y_5650_; lean_object* v___y_5651_; lean_object* v___y_5652_; lean_object* v___y_5653_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___x_5680_; lean_object* v___x_5681_; uint8_t v___x_5682_; 
v___x_5680_ = lean_unsigned_to_nat(1u);
v___x_5681_ = l_Lean_Syntax_getArg(v_stx_5436_, v___x_5680_);
v___x_5682_ = l_Lean_Syntax_isNone(v___x_5681_);
if (v___x_5682_ == 0)
{
uint8_t v___x_5683_; 
lean_inc(v___x_5681_);
v___x_5683_ = l_Lean_Syntax_matchesNull(v___x_5681_, v___x_5680_);
if (v___x_5683_ == 0)
{
lean_object* v___x_5684_; 
lean_dec(v___x_5681_);
lean_dec_ref(v_dec_5437_);
lean_dec(v_stx_5436_);
v___x_5684_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5684_;
}
else
{
lean_object* v___x_5685_; lean_object* v_mutTk_x3f_5686_; lean_object* v___x_5687_; 
v___x_5685_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5686_ = l_Lean_Syntax_getArg(v___x_5681_, v___x_5685_);
lean_dec(v___x_5681_);
v___x_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5687_, 0, v_mutTk_x3f_5686_);
v_mutTk_x3f_5649_ = v___x_5687_;
v___y_5650_ = v_a_5438_;
v___y_5651_ = v_a_5439_;
v___y_5652_ = v_a_5440_;
v___y_5653_ = v_a_5441_;
v___y_5654_ = v_a_5442_;
v___y_5655_ = v_a_5443_;
v___y_5656_ = v_a_5444_;
goto v___jp_5648_;
}
}
else
{
lean_object* v___x_5688_; 
lean_dec(v___x_5681_);
v___x_5688_ = lean_box(0);
v_mutTk_x3f_5649_ = v___x_5688_;
v___y_5650_ = v_a_5438_;
v___y_5651_ = v_a_5439_;
v___y_5652_ = v_a_5440_;
v___y_5653_ = v_a_5441_;
v___y_5654_ = v_a_5442_;
v___y_5655_ = v_a_5443_;
v___y_5656_ = v_a_5444_;
goto v___jp_5648_;
}
v___jp_5449_:
{
lean_object* v_eq_x3f_5463_; 
v_eq_x3f_5463_ = lean_ctor_get(v___y_5453_, 0);
lean_inc(v_eq_x3f_5463_);
lean_dec_ref(v___y_5453_);
if (lean_obj_tag(v_eq_x3f_5463_) == 1)
{
lean_object* v_val_5464_; lean_object* v_ref_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; 
v_val_5464_ = lean_ctor_get(v_eq_x3f_5463_, 0);
lean_inc(v_val_5464_);
lean_dec_ref_known(v_eq_x3f_5463_, 1);
v_ref_5465_ = lean_ctor_get(v___y_5461_, 2);
v___x_5466_ = l_Lean_SourceInfo_fromRef(v_ref_5465_, v___y_5450_);
v___x_5467_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5468_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
lean_inc_n(v___x_5466_, 19);
v___x_5469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5469_, 0, v___x_5466_);
lean_ctor_set(v___x_5469_, 1, v___x_5468_);
v___x_5470_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5471_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5472_, 0, v___x_5466_);
lean_ctor_set(v___x_5472_, 1, v___x_5470_);
lean_ctor_set(v___x_5472_, 2, v___x_5471_);
v___x_5473_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5474_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5475_, 0, v___x_5466_);
lean_ctor_set(v___x_5475_, 1, v___x_5474_);
v___x_5476_ = l_Lean_Syntax_node2(v___x_5466_, v___x_5470_, v_val_5464_, v___x_5475_);
v___x_5477_ = l_Lean_Syntax_node2(v___x_5466_, v___x_5473_, v___x_5476_, v___y_5452_);
v___x_5478_ = l_Lean_Syntax_node1(v___x_5466_, v___x_5470_, v___x_5477_);
v___x_5479_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5480_, 0, v___x_5466_);
lean_ctor_set(v___x_5480_, 1, v___x_5479_);
v___x_5481_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5482_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5483_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5466_);
lean_ctor_set(v___x_5484_, 1, v___x_5483_);
v___x_5485_ = l_Lean_Syntax_node1(v___x_5466_, v___x_5470_, v___y_5451_);
v___x_5486_ = l_Lean_Syntax_node1(v___x_5466_, v___x_5470_, v___x_5485_);
v___x_5487_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5488_, 0, v___x_5466_);
lean_ctor_set(v___x_5488_, 1, v___x_5487_);
lean_inc_ref(v___x_5488_);
lean_inc_ref(v___x_5484_);
v___x_5489_ = l_Lean_Syntax_node4(v___x_5466_, v___x_5482_, v___x_5484_, v___x_5486_, v___x_5488_, v_body_5455_);
v___x_5490_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5491_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5492_, 0, v___x_5466_);
lean_ctor_set(v___x_5492_, 1, v___x_5491_);
v___x_5493_ = l_Lean_Syntax_node1(v___x_5466_, v___x_5490_, v___x_5492_);
v___x_5494_ = l_Lean_Syntax_node1(v___x_5466_, v___x_5470_, v___x_5493_);
v___x_5495_ = l_Lean_Syntax_node1(v___x_5466_, v___x_5470_, v___x_5494_);
v___x_5496_ = l_Lean_Syntax_node4(v___x_5466_, v___x_5482_, v___x_5484_, v___x_5495_, v___x_5488_, v___y_5454_);
v___x_5497_ = l_Lean_Syntax_node2(v___x_5466_, v___x_5470_, v___x_5489_, v___x_5496_);
v___x_5498_ = l_Lean_Syntax_node1(v___x_5466_, v___x_5481_, v___x_5497_);
lean_inc_ref_n(v___x_5472_, 2);
v___x_5499_ = l_Lean_Syntax_node7(v___x_5466_, v___x_5467_, v___x_5469_, v___x_5472_, v___x_5472_, v___x_5472_, v___x_5478_, v___x_5480_, v___x_5498_);
v___x_5500_ = l_Lean_Elab_Do_elabDoElem(v___x_5499_, v_dec_5437_, v___x_5447_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
return v___x_5500_;
}
else
{
lean_object* v_ref_5501_; lean_object* v___x_5502_; lean_object* v_a_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; 
lean_dec(v_eq_x3f_5463_);
v_ref_5501_ = lean_ctor_get(v___y_5461_, 2);
v___x_5502_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5501_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc_n(v_a_5503_, 18);
lean_dec_ref(v___x_5502_);
v___x_5504_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5505_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_5506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5506_, 0, v_a_5503_);
lean_ctor_set(v___x_5506_, 1, v___x_5505_);
v___x_5507_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5508_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5509_, 0, v_a_5503_);
lean_ctor_set(v___x_5509_, 1, v___x_5507_);
lean_ctor_set(v___x_5509_, 2, v___x_5508_);
v___x_5510_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
lean_inc_ref_n(v___x_5509_, 3);
v___x_5511_ = l_Lean_Syntax_node2(v_a_5503_, v___x_5510_, v___x_5509_, v___y_5452_);
v___x_5512_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5507_, v___x_5511_);
v___x_5513_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5514_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5514_, 0, v_a_5503_);
lean_ctor_set(v___x_5514_, 1, v___x_5513_);
v___x_5515_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5516_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5517_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5518_, 0, v_a_5503_);
lean_ctor_set(v___x_5518_, 1, v___x_5517_);
v___x_5519_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5507_, v___y_5451_);
v___x_5520_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5507_, v___x_5519_);
v___x_5521_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5522_, 0, v_a_5503_);
lean_ctor_set(v___x_5522_, 1, v___x_5521_);
lean_inc_ref(v___x_5522_);
lean_inc_ref(v___x_5518_);
v___x_5523_ = l_Lean_Syntax_node4(v_a_5503_, v___x_5516_, v___x_5518_, v___x_5520_, v___x_5522_, v_body_5455_);
v___x_5524_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5525_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5526_, 0, v_a_5503_);
lean_ctor_set(v___x_5526_, 1, v___x_5525_);
v___x_5527_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5524_, v___x_5526_);
v___x_5528_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5507_, v___x_5527_);
v___x_5529_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5507_, v___x_5528_);
v___x_5530_ = l_Lean_Syntax_node4(v_a_5503_, v___x_5516_, v___x_5518_, v___x_5529_, v___x_5522_, v___y_5454_);
v___x_5531_ = l_Lean_Syntax_node2(v_a_5503_, v___x_5507_, v___x_5523_, v___x_5530_);
v___x_5532_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5515_, v___x_5531_);
v___x_5533_ = l_Lean_Syntax_node7(v_a_5503_, v___x_5504_, v___x_5506_, v___x_5509_, v___x_5509_, v___x_5509_, v___x_5512_, v___x_5514_, v___x_5532_);
v___x_5534_ = l_Lean_Elab_Do_elabDoElem(v___x_5533_, v_dec_5437_, v___x_5447_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
return v___x_5534_;
}
}
v___jp_5535_:
{
if (lean_obj_tag(v___y_5538_) == 0)
{
lean_dec_ref(v___y_5537_);
v___y_5450_ = v___y_5544_;
v___y_5451_ = v___y_5540_;
v___y_5452_ = v___y_5548_;
v___y_5453_ = v___y_5541_;
v___y_5454_ = v___y_5542_;
v_body_5455_ = v_a_5550_;
v___y_5456_ = v___y_5549_;
v___y_5457_ = v___y_5545_;
v___y_5458_ = v___y_5543_;
v___y_5459_ = v___y_5539_;
v___y_5460_ = v___y_5547_;
v___y_5461_ = v___y_5546_;
v___y_5462_ = v___y_5536_;
goto v___jp_5449_;
}
else
{
lean_dec_ref_known(v___y_5538_, 1);
if (v___x_5447_ == 0)
{
lean_dec_ref(v___y_5537_);
v___y_5450_ = v___y_5544_;
v___y_5451_ = v___y_5540_;
v___y_5452_ = v___y_5548_;
v___y_5453_ = v___y_5541_;
v___y_5454_ = v___y_5542_;
v_body_5455_ = v_a_5550_;
v___y_5456_ = v___y_5549_;
v___y_5457_ = v___y_5545_;
v___y_5458_ = v___y_5543_;
v___y_5459_ = v___y_5539_;
v___y_5460_ = v___y_5547_;
v___y_5461_ = v___y_5546_;
v___y_5462_ = v___y_5536_;
goto v___jp_5449_;
}
else
{
size_t v_sz_5551_; size_t v___x_5552_; lean_object* v___x_5553_; 
v_sz_5551_ = lean_array_size(v___y_5537_);
v___x_5552_ = ((size_t)0ULL);
v___x_5553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5537_, v_sz_5551_, v___x_5552_, v_a_5550_, v___y_5549_, v___y_5545_, v___y_5543_, v___y_5539_, v___y_5547_, v___y_5546_, v___y_5536_);
lean_dec_ref(v___y_5537_);
if (lean_obj_tag(v___x_5553_) == 0)
{
lean_object* v_a_5554_; 
v_a_5554_ = lean_ctor_get(v___x_5553_, 0);
lean_inc(v_a_5554_);
lean_dec_ref_known(v___x_5553_, 1);
v___y_5450_ = v___y_5544_;
v___y_5451_ = v___y_5540_;
v___y_5452_ = v___y_5548_;
v___y_5453_ = v___y_5541_;
v___y_5454_ = v___y_5542_;
v_body_5455_ = v_a_5554_;
v___y_5456_ = v___y_5549_;
v___y_5457_ = v___y_5545_;
v___y_5458_ = v___y_5543_;
v___y_5459_ = v___y_5539_;
v___y_5460_ = v___y_5547_;
v___y_5461_ = v___y_5546_;
v___y_5462_ = v___y_5536_;
goto v___jp_5449_;
}
else
{
lean_object* v_a_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
lean_dec(v___y_5548_);
lean_dec(v___y_5542_);
lean_dec_ref(v___y_5541_);
lean_dec(v___y_5540_);
lean_dec_ref(v_dec_5437_);
v_a_5555_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5557_ = v___x_5553_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_a_5555_);
lean_dec(v___x_5553_);
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
}
}
v___jp_5563_:
{
lean_object* v___x_5577_; uint8_t v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; 
v___x_5577_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_5578_ = 0;
v___x_5579_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_5580_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v___y_5566_, v___y_5565_, v___x_5579_, v___y_5575_, v___y_5571_, v___y_5570_, v___y_5567_, v___y_5573_, v___y_5572_, v___y_5564_);
if (lean_obj_tag(v___x_5580_) == 0)
{
lean_object* v_a_5581_; lean_object* v___x_5582_; 
v_a_5581_ = lean_ctor_get(v___x_5580_, 0);
lean_inc(v_a_5581_);
lean_dec_ref_known(v___x_5580_, 1);
v___x_5582_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_5581_, v___y_5567_, v___y_5573_, v___y_5572_, v___y_5564_);
if (lean_obj_tag(v___x_5582_) == 0)
{
lean_object* v___x_5583_; lean_object* v___x_5584_; 
lean_dec_ref_known(v___x_5582_, 1);
lean_inc(v___y_5565_);
v___x_5583_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5583_, 0, v___y_5565_);
lean_ctor_set_uint8(v___x_5583_, sizeof(void*)*1, v___x_5578_);
lean_inc(v___y_5568_);
v___x_5584_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5568_, v___y_5571_, v___y_5570_, v___y_5567_, v___y_5573_, v___y_5572_, v___y_5564_);
if (lean_obj_tag(v___x_5584_) == 0)
{
lean_object* v_a_5585_; lean_object* v___x_5586_; 
v_a_5585_ = lean_ctor_get(v___x_5584_, 0);
lean_inc(v_a_5585_);
lean_dec_ref_known(v___x_5584_, 1);
v___x_5586_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5583_, v_a_5585_, v___y_5575_, v___y_5571_, v___y_5570_, v___y_5567_, v___y_5573_, v___y_5572_, v___y_5564_);
lean_dec_ref_known(v___x_5583_, 1);
if (lean_obj_tag(v___x_5586_) == 0)
{
lean_dec_ref_known(v___x_5586_, 1);
if (lean_obj_tag(v___y_5576_) == 0)
{
lean_object* v_toCold_5587_; lean_object* v_ref_5588_; lean_object* v___x_5589_; lean_object* v_a_5590_; lean_object* v_quotContext_5591_; lean_object* v_currMacroScope_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; 
v_toCold_5587_ = lean_ctor_get(v___y_5572_, 0);
v_ref_5588_ = lean_ctor_get(v___y_5572_, 2);
v___x_5589_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5588_, v___y_5575_, v___y_5571_, v___y_5570_, v___y_5567_, v___y_5573_, v___y_5572_, v___y_5564_);
v_a_5590_ = lean_ctor_get(v___x_5589_, 0);
lean_inc_n(v_a_5590_, 9);
lean_dec_ref(v___x_5589_);
v_quotContext_5591_ = lean_ctor_get(v_toCold_5587_, 8);
v_currMacroScope_5592_ = lean_ctor_get(v_toCold_5587_, 9);
v___x_5593_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5594_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5595_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5596_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1));
v___x_5597_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5598_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5592_, 2);
lean_inc_n(v_quotContext_5591_, 2);
v___x_5599_ = l_Lean_addMacroScope(v_quotContext_5591_, v___x_5598_, v_currMacroScope_5592_);
v___x_5600_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5601_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5601_, 0, v_a_5590_);
lean_ctor_set(v___x_5601_, 1, v___x_5597_);
lean_ctor_set(v___x_5601_, 2, v___x_5599_);
lean_ctor_set(v___x_5601_, 3, v___x_5600_);
v___x_5602_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5603_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5604_ = l_Lean_addMacroScope(v_quotContext_5591_, v___x_5603_, v_currMacroScope_5592_);
v___x_5605_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5606_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5606_, 0, v_a_5590_);
lean_ctor_set(v___x_5606_, 1, v___x_5602_);
lean_ctor_set(v___x_5606_, 2, v___x_5604_);
lean_ctor_set(v___x_5606_, 3, v___x_5605_);
v___x_5607_ = l_Lean_Syntax_node1(v_a_5590_, v___x_5593_, v___x_5606_);
v___x_5608_ = l_Lean_Syntax_node2(v_a_5590_, v___x_5596_, v___x_5601_, v___x_5607_);
v___x_5609_ = l_Lean_Syntax_node1(v_a_5590_, v___x_5595_, v___x_5608_);
v___x_5610_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5611_, 0, v_a_5590_);
lean_ctor_set(v___x_5611_, 1, v___x_5593_);
lean_ctor_set(v___x_5611_, 2, v___x_5610_);
v___x_5612_ = l_Lean_Syntax_node2(v_a_5590_, v___x_5594_, v___x_5609_, v___x_5611_);
v___x_5613_ = l_Lean_Syntax_node1(v_a_5590_, v___x_5593_, v___x_5612_);
v___x_5614_ = l_Lean_Syntax_node1(v_a_5590_, v___x_5577_, v___x_5613_);
v___y_5536_ = v___y_5564_;
v___y_5537_ = v_a_5585_;
v___y_5538_ = v___y_5565_;
v___y_5539_ = v___y_5567_;
v___y_5540_ = v___y_5568_;
v___y_5541_ = v_a_5581_;
v___y_5542_ = v___y_5569_;
v___y_5543_ = v___y_5570_;
v___y_5544_ = v___x_5578_;
v___y_5545_ = v___y_5571_;
v___y_5546_ = v___y_5572_;
v___y_5547_ = v___y_5573_;
v___y_5548_ = v___y_5574_;
v___y_5549_ = v___y_5575_;
v_a_5550_ = v___x_5614_;
goto v___jp_5535_;
}
else
{
lean_object* v_val_5615_; 
v_val_5615_ = lean_ctor_get(v___y_5576_, 0);
lean_inc(v_val_5615_);
lean_dec_ref_known(v___y_5576_, 1);
v___y_5536_ = v___y_5564_;
v___y_5537_ = v_a_5585_;
v___y_5538_ = v___y_5565_;
v___y_5539_ = v___y_5567_;
v___y_5540_ = v___y_5568_;
v___y_5541_ = v_a_5581_;
v___y_5542_ = v___y_5569_;
v___y_5543_ = v___y_5570_;
v___y_5544_ = v___x_5578_;
v___y_5545_ = v___y_5571_;
v___y_5546_ = v___y_5572_;
v___y_5547_ = v___y_5573_;
v___y_5548_ = v___y_5574_;
v___y_5549_ = v___y_5575_;
v_a_5550_ = v_val_5615_;
goto v___jp_5535_;
}
}
else
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec(v_a_5585_);
lean_dec(v_a_5581_);
lean_dec(v___y_5576_);
lean_dec(v___y_5574_);
lean_dec(v___y_5569_);
lean_dec(v___y_5568_);
lean_dec(v___y_5565_);
lean_dec_ref(v_dec_5437_);
v_a_5616_ = lean_ctor_get(v___x_5586_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5586_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5586_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5616_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
lean_dec_ref_known(v___x_5583_, 1);
lean_dec(v_a_5581_);
lean_dec(v___y_5576_);
lean_dec(v___y_5574_);
lean_dec(v___y_5569_);
lean_dec(v___y_5568_);
lean_dec(v___y_5565_);
lean_dec_ref(v_dec_5437_);
v_a_5624_ = lean_ctor_get(v___x_5584_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5584_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5584_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5584_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec(v_a_5581_);
lean_dec(v___y_5576_);
lean_dec(v___y_5574_);
lean_dec(v___y_5569_);
lean_dec(v___y_5568_);
lean_dec(v___y_5565_);
lean_dec_ref(v_dec_5437_);
v_a_5632_ = lean_ctor_get(v___x_5582_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5582_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5582_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5582_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
else
{
lean_object* v_a_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5647_; 
lean_dec(v___y_5576_);
lean_dec(v___y_5574_);
lean_dec(v___y_5569_);
lean_dec(v___y_5568_);
lean_dec(v___y_5565_);
lean_dec_ref(v_dec_5437_);
v_a_5640_ = lean_ctor_get(v___x_5580_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5642_ = v___x_5580_;
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_a_5640_);
lean_dec(v___x_5580_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v___x_5645_; 
if (v_isShared_5643_ == 0)
{
v___x_5645_ = v___x_5642_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_a_5640_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
v___jp_5648_:
{
lean_object* v___x_5657_; lean_object* v_cfg_5658_; lean_object* v___x_5659_; uint8_t v___x_5660_; 
v___x_5657_ = lean_unsigned_to_nat(2u);
v_cfg_5658_ = l_Lean_Syntax_getArg(v_stx_5436_, v___x_5657_);
v___x_5659_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_5658_);
v___x_5660_ = l_Lean_Syntax_isOfKind(v_cfg_5658_, v___x_5659_);
if (v___x_5660_ == 0)
{
lean_object* v___x_5661_; 
lean_dec(v_cfg_5658_);
lean_dec(v_mutTk_x3f_5649_);
lean_dec_ref(v_dec_5437_);
lean_dec(v_stx_5436_);
v___x_5661_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5661_;
}
else
{
lean_object* v___x_5662_; lean_object* v_pattern_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; 
v___x_5662_ = lean_unsigned_to_nat(3u);
v_pattern_5663_ = l_Lean_Syntax_getArg(v_stx_5436_, v___x_5662_);
v___x_5664_ = lean_unsigned_to_nat(5u);
v___x_5665_ = l_Lean_Syntax_getArg(v_stx_5436_, v___x_5664_);
v___x_5666_ = lean_unsigned_to_nat(7u);
v___x_5667_ = l_Lean_Syntax_getArg(v_stx_5436_, v___x_5666_);
v___x_5668_ = lean_unsigned_to_nat(8u);
v___x_5669_ = l_Lean_Syntax_getArg(v_stx_5436_, v___x_5668_);
lean_dec(v_stx_5436_);
v___x_5670_ = l_Lean_Syntax_getOptional_x3f(v___x_5669_);
lean_dec(v___x_5669_);
if (lean_obj_tag(v___x_5670_) == 0)
{
lean_object* v___x_5671_; 
v___x_5671_ = lean_box(0);
v___y_5564_ = v___y_5656_;
v___y_5565_ = v_mutTk_x3f_5649_;
v___y_5566_ = v_cfg_5658_;
v___y_5567_ = v___y_5653_;
v___y_5568_ = v_pattern_5663_;
v___y_5569_ = v___x_5667_;
v___y_5570_ = v___y_5652_;
v___y_5571_ = v___y_5651_;
v___y_5572_ = v___y_5655_;
v___y_5573_ = v___y_5654_;
v___y_5574_ = v___x_5665_;
v___y_5575_ = v___y_5650_;
v___y_5576_ = v___x_5671_;
goto v___jp_5563_;
}
else
{
lean_object* v_val_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5679_; 
v_val_5672_ = lean_ctor_get(v___x_5670_, 0);
v_isSharedCheck_5679_ = !lean_is_exclusive(v___x_5670_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5674_ = v___x_5670_;
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_val_5672_);
lean_dec(v___x_5670_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5677_; 
if (v_isShared_5675_ == 0)
{
v___x_5677_ = v___x_5674_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_val_5672_);
v___x_5677_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
v___y_5564_ = v___y_5656_;
v___y_5565_ = v_mutTk_x3f_5649_;
v___y_5566_ = v_cfg_5658_;
v___y_5567_ = v___y_5653_;
v___y_5568_ = v_pattern_5663_;
v___y_5569_ = v___x_5667_;
v___y_5570_ = v___y_5652_;
v___y_5571_ = v___y_5651_;
v___y_5572_ = v___y_5655_;
v___y_5573_ = v___y_5654_;
v___y_5574_ = v___x_5665_;
v___y_5575_ = v___y_5650_;
v___y_5576_ = v___x_5677_;
goto v___jp_5563_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5689_, lean_object* v_dec_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_){
_start:
{
lean_object* v_res_5699_; 
v_res_5699_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5689_, v_dec_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_);
lean_dec(v_a_5697_);
lean_dec_ref(v_a_5696_);
lean_dec(v_a_5695_);
lean_dec_ref(v_a_5694_);
lean_dec(v_a_5693_);
lean_dec_ref(v_a_5692_);
lean_dec_ref(v_a_5691_);
return v_res_5699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5700_, size_t v_sz_5701_, size_t v_i_5702_, lean_object* v_b_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_){
_start:
{
lean_object* v___x_5712_; 
v___x_5712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5700_, v_sz_5701_, v_i_5702_, v_b_5703_, v___y_5709_);
return v___x_5712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5713_, lean_object* v_sz_5714_, lean_object* v_i_5715_, lean_object* v_b_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_){
_start:
{
size_t v_sz_boxed_5725_; size_t v_i_boxed_5726_; lean_object* v_res_5727_; 
v_sz_boxed_5725_ = lean_unbox_usize(v_sz_5714_);
lean_dec(v_sz_5714_);
v_i_boxed_5726_ = lean_unbox_usize(v_i_5715_);
lean_dec(v_i_5715_);
v_res_5727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5713_, v_sz_boxed_5725_, v_i_boxed_5726_, v_b_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
lean_dec(v___y_5723_);
lean_dec_ref(v___y_5722_);
lean_dec(v___y_5721_);
lean_dec_ref(v___y_5720_);
lean_dec(v___y_5719_);
lean_dec_ref(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec_ref(v_as_5713_);
return v_res_5727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; 
v___x_5735_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5736_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
v___x_5737_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5738_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5739_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5735_, v___x_5736_, v___x_5737_, v___x_5738_);
return v___x_5739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5740_){
_start:
{
lean_object* v_res_5741_; 
v_res_5741_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0(lean_object* v_otherwise_x3f_5742_, uint8_t v___x_5743_, lean_object* v___x_5744_, lean_object* v___x_5745_, lean_object* v___x_5746_, lean_object* v___x_5747_, lean_object* v___x_5748_, lean_object* v___x_5749_, lean_object* v_dec_5750_, uint8_t v___x_5751_, lean_object* v_mutTk_x3f_5752_, lean_object* v___x_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5742_) == 0)
{
lean_object* v_ref_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___y_5772_; 
lean_dec(v___y_5754_);
v_ref_5763_ = lean_ctor_get(v___y_5760_, 2);
v___x_5764_ = l_Lean_SourceInfo_fromRef(v_ref_5763_, v___x_5743_);
v___x_5765_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5746_);
lean_inc_ref(v___x_5745_);
lean_inc_ref(v___x_5744_);
v___x_5766_ = l_Lean_Name_mkStr4(v___x_5744_, v___x_5745_, v___x_5746_, v___x_5765_);
v___x_5767_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5764_);
v___x_5768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5768_, 0, v___x_5764_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
v___x_5769_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5770_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5752_) == 1)
{
lean_object* v_val_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; 
v_val_5787_ = lean_ctor_get(v_mutTk_x3f_5752_, 0);
v___x_5788_ = l_Lean_SourceInfo_fromRef(v_val_5787_, v___x_5751_);
v___x_5789_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5790_, 0, v___x_5788_);
lean_ctor_set(v___x_5790_, 1, v___x_5789_);
v___x_5791_ = l_Array_mkArray1___redArg(v___x_5790_);
v___y_5772_ = v___x_5791_;
goto v___jp_5771_;
}
else
{
lean_object* v___x_5792_; 
v___x_5792_ = lean_mk_empty_array_with_capacity(v___x_5753_);
v___y_5772_ = v___x_5792_;
goto v___jp_5771_;
}
v___jp_5771_:
{
lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; 
v___x_5773_ = l_Array_append___redArg(v___x_5770_, v___y_5772_);
lean_dec_ref(v___y_5772_);
lean_inc_n(v___x_5764_, 6);
v___x_5774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5774_, 0, v___x_5764_);
lean_ctor_set(v___x_5774_, 1, v___x_5769_);
lean_ctor_set(v___x_5774_, 2, v___x_5773_);
v___x_5775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5775_, 0, v___x_5764_);
lean_ctor_set(v___x_5775_, 1, v___x_5769_);
lean_ctor_set(v___x_5775_, 2, v___x_5770_);
lean_inc_ref_n(v___x_5775_, 2);
v___x_5776_ = l_Lean_Syntax_node1(v___x_5764_, v___x_5747_, v___x_5775_);
v___x_5777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5746_);
lean_inc_ref(v___x_5745_);
lean_inc_ref(v___x_5744_);
v___x_5778_ = l_Lean_Name_mkStr4(v___x_5744_, v___x_5745_, v___x_5746_, v___x_5777_);
v___x_5779_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5780_ = l_Lean_Name_mkStr4(v___x_5744_, v___x_5745_, v___x_5746_, v___x_5779_);
v___x_5781_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5764_);
lean_ctor_set(v___x_5782_, 1, v___x_5781_);
v___x_5783_ = l_Lean_Syntax_node5(v___x_5764_, v___x_5780_, v___x_5748_, v___x_5775_, v___x_5775_, v___x_5782_, v___x_5749_);
v___x_5784_ = l_Lean_Syntax_node1(v___x_5764_, v___x_5778_, v___x_5783_);
v___x_5785_ = l_Lean_Syntax_node4(v___x_5764_, v___x_5766_, v___x_5768_, v___x_5774_, v___x_5776_, v___x_5784_);
v___x_5786_ = l_Lean_Elab_Do_elabDoElem(v___x_5785_, v_dec_5750_, v___x_5751_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_);
return v___x_5786_;
}
}
else
{
lean_object* v_val_5793_; lean_object* v_ref_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___y_5803_; lean_object* v___y_5804_; lean_object* v___y_5805_; lean_object* v___y_5806_; lean_object* v___y_5807_; lean_object* v___y_5824_; 
v_val_5793_ = lean_ctor_get(v_otherwise_x3f_5742_, 0);
lean_inc(v_val_5793_);
lean_dec_ref_known(v_otherwise_x3f_5742_, 1);
v_ref_5794_ = lean_ctor_get(v___y_5760_, 2);
v___x_5795_ = l_Lean_SourceInfo_fromRef(v_ref_5794_, v___x_5743_);
v___x_5796_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5797_ = l_Lean_Name_mkStr4(v___x_5744_, v___x_5745_, v___x_5746_, v___x_5796_);
v___x_5798_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5795_);
v___x_5799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5799_, 0, v___x_5795_);
lean_ctor_set(v___x_5799_, 1, v___x_5798_);
v___x_5800_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5801_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5752_) == 1)
{
lean_object* v_val_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; 
v_val_5837_ = lean_ctor_get(v_mutTk_x3f_5752_, 0);
v___x_5838_ = l_Lean_SourceInfo_fromRef(v_val_5837_, v___x_5751_);
v___x_5839_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5840_, 0, v___x_5838_);
lean_ctor_set(v___x_5840_, 1, v___x_5839_);
v___x_5841_ = l_Array_mkArray1___redArg(v___x_5840_);
v___y_5824_ = v___x_5841_;
goto v___jp_5823_;
}
else
{
lean_object* v___x_5842_; 
v___x_5842_ = lean_mk_empty_array_with_capacity(v___x_5753_);
v___y_5824_ = v___x_5842_;
goto v___jp_5823_;
}
v___jp_5802_:
{
lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5808_ = l_Array_append___redArg(v___x_5801_, v___y_5807_);
lean_dec_ref(v___y_5807_);
lean_inc(v___x_5795_);
v___x_5809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5809_, 0, v___x_5795_);
lean_ctor_set(v___x_5809_, 1, v___x_5800_);
lean_ctor_set(v___x_5809_, 2, v___x_5808_);
v___x_5810_ = lean_unsigned_to_nat(9u);
v___x_5811_ = lean_mk_empty_array_with_capacity(v___x_5810_);
v___x_5812_ = lean_array_push(v___x_5811_, v___x_5799_);
v___x_5813_ = lean_array_push(v___x_5812_, v___y_5804_);
v___x_5814_ = lean_array_push(v___x_5813_, v___y_5803_);
v___x_5815_ = lean_array_push(v___x_5814_, v___x_5748_);
v___x_5816_ = lean_array_push(v___x_5815_, v___y_5805_);
v___x_5817_ = lean_array_push(v___x_5816_, v___x_5749_);
v___x_5818_ = lean_array_push(v___x_5817_, v___y_5806_);
v___x_5819_ = lean_array_push(v___x_5818_, v_val_5793_);
v___x_5820_ = lean_array_push(v___x_5819_, v___x_5809_);
v___x_5821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5821_, 0, v___x_5795_);
lean_ctor_set(v___x_5821_, 1, v___x_5797_);
lean_ctor_set(v___x_5821_, 2, v___x_5820_);
v___x_5822_ = l_Lean_Elab_Do_elabDoElem(v___x_5821_, v_dec_5750_, v___x_5751_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_);
return v___x_5822_;
}
v___jp_5823_:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5825_ = l_Array_append___redArg(v___x_5801_, v___y_5824_);
lean_dec_ref(v___y_5824_);
lean_inc_n(v___x_5795_, 5);
v___x_5826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5795_);
lean_ctor_set(v___x_5826_, 1, v___x_5800_);
lean_ctor_set(v___x_5826_, 2, v___x_5825_);
v___x_5827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5827_, 0, v___x_5795_);
lean_ctor_set(v___x_5827_, 1, v___x_5800_);
lean_ctor_set(v___x_5827_, 2, v___x_5801_);
v___x_5828_ = l_Lean_Syntax_node1(v___x_5795_, v___x_5747_, v___x_5827_);
v___x_5829_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5830_, 0, v___x_5795_);
lean_ctor_set(v___x_5830_, 1, v___x_5829_);
v___x_5831_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5795_);
lean_ctor_set(v___x_5832_, 1, v___x_5831_);
if (lean_obj_tag(v___y_5754_) == 0)
{
lean_object* v___x_5833_; 
v___x_5833_ = lean_mk_empty_array_with_capacity(v___x_5753_);
v___y_5803_ = v___x_5828_;
v___y_5804_ = v___x_5826_;
v___y_5805_ = v___x_5830_;
v___y_5806_ = v___x_5832_;
v___y_5807_ = v___x_5833_;
goto v___jp_5802_;
}
else
{
lean_object* v_val_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; 
v_val_5834_ = lean_ctor_get(v___y_5754_, 0);
lean_inc(v_val_5834_);
lean_dec_ref_known(v___y_5754_, 1);
v___x_5835_ = lean_mk_empty_array_with_capacity(v___x_5753_);
v___x_5836_ = lean_array_push(v___x_5835_, v_val_5834_);
v___y_5803_ = v___x_5828_;
v___y_5804_ = v___x_5826_;
v___y_5805_ = v___x_5830_;
v___y_5806_ = v___x_5832_;
v___y_5807_ = v___x_5836_;
goto v___jp_5802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_5843_ = _args[0];
lean_object* v___x_5844_ = _args[1];
lean_object* v___x_5845_ = _args[2];
lean_object* v___x_5846_ = _args[3];
lean_object* v___x_5847_ = _args[4];
lean_object* v___x_5848_ = _args[5];
lean_object* v___x_5849_ = _args[6];
lean_object* v___x_5850_ = _args[7];
lean_object* v_dec_5851_ = _args[8];
lean_object* v___x_5852_ = _args[9];
lean_object* v_mutTk_x3f_5853_ = _args[10];
lean_object* v___x_5854_ = _args[11];
lean_object* v___y_5855_ = _args[12];
lean_object* v___y_5856_ = _args[13];
lean_object* v___y_5857_ = _args[14];
lean_object* v___y_5858_ = _args[15];
lean_object* v___y_5859_ = _args[16];
lean_object* v___y_5860_ = _args[17];
lean_object* v___y_5861_ = _args[18];
lean_object* v___y_5862_ = _args[19];
lean_object* v___y_5863_ = _args[20];
_start:
{
uint8_t v___x_22862__boxed_5864_; uint8_t v___x_22869__boxed_5865_; lean_object* v_res_5866_; 
v___x_22862__boxed_5864_ = lean_unbox(v___x_5844_);
v___x_22869__boxed_5865_ = lean_unbox(v___x_5852_);
v_res_5866_ = l_Lean_Elab_Do_elabDoLetArrow___lam__0(v_otherwise_x3f_5843_, v___x_22862__boxed_5864_, v___x_5845_, v___x_5846_, v___x_5847_, v___x_5848_, v___x_5849_, v___x_5850_, v_dec_5851_, v___x_22869__boxed_5865_, v_mutTk_x3f_5853_, v___x_5854_, v___y_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_);
lean_dec(v___y_5862_);
lean_dec_ref(v___y_5861_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec(v___y_5858_);
lean_dec_ref(v___y_5857_);
lean_dec_ref(v___y_5856_);
lean_dec(v___x_5854_);
lean_dec(v_mutTk_x3f_5853_);
return v_res_5866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1(lean_object* v_otherwise_x3f_5867_, uint8_t v___x_5868_, lean_object* v___x_5869_, lean_object* v___x_5870_, lean_object* v___x_5871_, lean_object* v___x_5872_, lean_object* v___x_5873_, lean_object* v___x_5874_, lean_object* v_dec_5875_, uint8_t v___x_5876_, lean_object* v_mutTk_x3f_5877_, lean_object* v___x_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5867_) == 0)
{
lean_object* v_ref_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___y_5897_; 
lean_dec(v___y_5879_);
v_ref_5888_ = lean_ctor_get(v___y_5885_, 2);
v___x_5889_ = l_Lean_SourceInfo_fromRef(v_ref_5888_, v___x_5868_);
v___x_5890_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5871_);
lean_inc_ref(v___x_5870_);
lean_inc_ref(v___x_5869_);
v___x_5891_ = l_Lean_Name_mkStr4(v___x_5869_, v___x_5870_, v___x_5871_, v___x_5890_);
v___x_5892_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5889_);
v___x_5893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5889_);
lean_ctor_set(v___x_5893_, 1, v___x_5892_);
v___x_5894_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5895_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5877_) == 1)
{
lean_object* v_val_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; 
v_val_5912_ = lean_ctor_get(v_mutTk_x3f_5877_, 0);
v___x_5913_ = l_Lean_SourceInfo_fromRef(v_val_5912_, v___x_5876_);
v___x_5914_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5913_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = l_Array_mkArray1___redArg(v___x_5915_);
v___y_5897_ = v___x_5916_;
goto v___jp_5896_;
}
else
{
lean_object* v___x_5917_; 
v___x_5917_ = lean_mk_empty_array_with_capacity(v___x_5878_);
v___y_5897_ = v___x_5917_;
goto v___jp_5896_;
}
v___jp_5896_:
{
lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; 
v___x_5898_ = l_Array_append___redArg(v___x_5895_, v___y_5897_);
lean_dec_ref(v___y_5897_);
lean_inc_n(v___x_5889_, 6);
v___x_5899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5889_);
lean_ctor_set(v___x_5899_, 1, v___x_5894_);
lean_ctor_set(v___x_5899_, 2, v___x_5898_);
v___x_5900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5889_);
lean_ctor_set(v___x_5900_, 1, v___x_5894_);
lean_ctor_set(v___x_5900_, 2, v___x_5895_);
lean_inc_ref_n(v___x_5900_, 2);
v___x_5901_ = l_Lean_Syntax_node1(v___x_5889_, v___x_5872_, v___x_5900_);
v___x_5902_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5871_);
lean_inc_ref(v___x_5870_);
lean_inc_ref(v___x_5869_);
v___x_5903_ = l_Lean_Name_mkStr4(v___x_5869_, v___x_5870_, v___x_5871_, v___x_5902_);
v___x_5904_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5905_ = l_Lean_Name_mkStr4(v___x_5869_, v___x_5870_, v___x_5871_, v___x_5904_);
v___x_5906_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5889_);
lean_ctor_set(v___x_5907_, 1, v___x_5906_);
v___x_5908_ = l_Lean_Syntax_node5(v___x_5889_, v___x_5905_, v___x_5873_, v___x_5900_, v___x_5900_, v___x_5907_, v___x_5874_);
v___x_5909_ = l_Lean_Syntax_node1(v___x_5889_, v___x_5903_, v___x_5908_);
v___x_5910_ = l_Lean_Syntax_node4(v___x_5889_, v___x_5891_, v___x_5893_, v___x_5899_, v___x_5901_, v___x_5909_);
v___x_5911_ = l_Lean_Elab_Do_elabDoElem(v___x_5910_, v_dec_5875_, v___x_5876_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_);
return v___x_5911_;
}
}
else
{
lean_object* v_val_5918_; lean_object* v_ref_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___y_5928_; lean_object* v___y_5929_; lean_object* v___y_5930_; lean_object* v___y_5931_; lean_object* v___y_5932_; lean_object* v___y_5949_; 
v_val_5918_ = lean_ctor_get(v_otherwise_x3f_5867_, 0);
lean_inc(v_val_5918_);
lean_dec_ref_known(v_otherwise_x3f_5867_, 1);
v_ref_5919_ = lean_ctor_get(v___y_5885_, 2);
v___x_5920_ = l_Lean_SourceInfo_fromRef(v_ref_5919_, v___x_5868_);
v___x_5921_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5922_ = l_Lean_Name_mkStr4(v___x_5869_, v___x_5870_, v___x_5871_, v___x_5921_);
v___x_5923_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5920_);
v___x_5924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5920_);
lean_ctor_set(v___x_5924_, 1, v___x_5923_);
v___x_5925_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5926_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5877_) == 1)
{
lean_object* v_val_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; 
v_val_5962_ = lean_ctor_get(v_mutTk_x3f_5877_, 0);
v___x_5963_ = l_Lean_SourceInfo_fromRef(v_val_5962_, v___x_5876_);
v___x_5964_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5963_);
lean_ctor_set(v___x_5965_, 1, v___x_5964_);
v___x_5966_ = l_Array_mkArray1___redArg(v___x_5965_);
v___y_5949_ = v___x_5966_;
goto v___jp_5948_;
}
else
{
lean_object* v___x_5967_; 
v___x_5967_ = lean_mk_empty_array_with_capacity(v___x_5878_);
v___y_5949_ = v___x_5967_;
goto v___jp_5948_;
}
v___jp_5927_:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; 
v___x_5933_ = l_Array_append___redArg(v___x_5926_, v___y_5932_);
lean_dec_ref(v___y_5932_);
lean_inc(v___x_5920_);
v___x_5934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5920_);
lean_ctor_set(v___x_5934_, 1, v___x_5925_);
lean_ctor_set(v___x_5934_, 2, v___x_5933_);
v___x_5935_ = lean_unsigned_to_nat(9u);
v___x_5936_ = lean_mk_empty_array_with_capacity(v___x_5935_);
v___x_5937_ = lean_array_push(v___x_5936_, v___x_5924_);
v___x_5938_ = lean_array_push(v___x_5937_, v___y_5931_);
v___x_5939_ = lean_array_push(v___x_5938_, v___y_5929_);
v___x_5940_ = lean_array_push(v___x_5939_, v___x_5873_);
v___x_5941_ = lean_array_push(v___x_5940_, v___y_5930_);
v___x_5942_ = lean_array_push(v___x_5941_, v___x_5874_);
v___x_5943_ = lean_array_push(v___x_5942_, v___y_5928_);
v___x_5944_ = lean_array_push(v___x_5943_, v_val_5918_);
v___x_5945_ = lean_array_push(v___x_5944_, v___x_5934_);
v___x_5946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5920_);
lean_ctor_set(v___x_5946_, 1, v___x_5922_);
lean_ctor_set(v___x_5946_, 2, v___x_5945_);
v___x_5947_ = l_Lean_Elab_Do_elabDoElem(v___x_5946_, v_dec_5875_, v___x_5876_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_);
return v___x_5947_;
}
v___jp_5948_:
{
lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5950_ = l_Array_append___redArg(v___x_5926_, v___y_5949_);
lean_dec_ref(v___y_5949_);
lean_inc_n(v___x_5920_, 5);
v___x_5951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5920_);
lean_ctor_set(v___x_5951_, 1, v___x_5925_);
lean_ctor_set(v___x_5951_, 2, v___x_5950_);
v___x_5952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5920_);
lean_ctor_set(v___x_5952_, 1, v___x_5925_);
lean_ctor_set(v___x_5952_, 2, v___x_5926_);
v___x_5953_ = l_Lean_Syntax_node1(v___x_5920_, v___x_5872_, v___x_5952_);
v___x_5954_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5920_);
lean_ctor_set(v___x_5955_, 1, v___x_5954_);
v___x_5956_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5920_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
if (lean_obj_tag(v___y_5879_) == 0)
{
lean_object* v___x_5958_; 
v___x_5958_ = lean_mk_empty_array_with_capacity(v___x_5878_);
v___y_5928_ = v___x_5957_;
v___y_5929_ = v___x_5953_;
v___y_5930_ = v___x_5955_;
v___y_5931_ = v___x_5951_;
v___y_5932_ = v___x_5958_;
goto v___jp_5927_;
}
else
{
lean_object* v_val_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; 
v_val_5959_ = lean_ctor_get(v___y_5879_, 0);
lean_inc(v_val_5959_);
lean_dec_ref_known(v___y_5879_, 1);
v___x_5960_ = lean_mk_empty_array_with_capacity(v___x_5878_);
v___x_5961_ = lean_array_push(v___x_5960_, v_val_5959_);
v___y_5928_ = v___x_5957_;
v___y_5929_ = v___x_5953_;
v___y_5930_ = v___x_5955_;
v___y_5931_ = v___x_5951_;
v___y_5932_ = v___x_5961_;
goto v___jp_5927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_5968_ = _args[0];
lean_object* v___x_5969_ = _args[1];
lean_object* v___x_5970_ = _args[2];
lean_object* v___x_5971_ = _args[3];
lean_object* v___x_5972_ = _args[4];
lean_object* v___x_5973_ = _args[5];
lean_object* v___x_5974_ = _args[6];
lean_object* v___x_5975_ = _args[7];
lean_object* v_dec_5976_ = _args[8];
lean_object* v___x_5977_ = _args[9];
lean_object* v_mutTk_x3f_5978_ = _args[10];
lean_object* v___x_5979_ = _args[11];
lean_object* v___y_5980_ = _args[12];
lean_object* v___y_5981_ = _args[13];
lean_object* v___y_5982_ = _args[14];
lean_object* v___y_5983_ = _args[15];
lean_object* v___y_5984_ = _args[16];
lean_object* v___y_5985_ = _args[17];
lean_object* v___y_5986_ = _args[18];
lean_object* v___y_5987_ = _args[19];
lean_object* v___y_5988_ = _args[20];
_start:
{
uint8_t v___x_23093__boxed_5989_; uint8_t v___x_23100__boxed_5990_; lean_object* v_res_5991_; 
v___x_23093__boxed_5989_ = lean_unbox(v___x_5969_);
v___x_23100__boxed_5990_ = lean_unbox(v___x_5977_);
v_res_5991_ = l_Lean_Elab_Do_elabDoLetArrow___lam__1(v_otherwise_x3f_5968_, v___x_23093__boxed_5989_, v___x_5970_, v___x_5971_, v___x_5972_, v___x_5973_, v___x_5974_, v___x_5975_, v_dec_5976_, v___x_23100__boxed_5990_, v_mutTk_x3f_5978_, v___x_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
lean_dec(v___y_5987_);
lean_dec_ref(v___y_5986_);
lean_dec(v___y_5985_);
lean_dec_ref(v___y_5984_);
lean_dec(v___y_5983_);
lean_dec_ref(v___y_5982_);
lean_dec_ref(v___y_5981_);
lean_dec(v___x_5979_);
lean_dec(v_mutTk_x3f_5978_);
return v_res_5991_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1(void){
_start:
{
lean_object* v___x_5993_; lean_object* v___x_5994_; 
v___x_5993_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__0));
v___x_5994_ = l_Lean_stringToMessageData(v___x_5993_);
return v___x_5994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_6001_, lean_object* v_dec_6002_, lean_object* v_a_6003_, lean_object* v_a_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_){
_start:
{
lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; uint8_t v___x_6015_; 
v___x_6011_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_6012_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_6013_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_6014_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
lean_inc(v_stx_6001_);
v___x_6015_ = l_Lean_Syntax_isOfKind(v_stx_6001_, v___x_6014_);
if (v___x_6015_ == 0)
{
lean_object* v___x_6016_; 
lean_dec_ref(v_dec_6002_);
lean_dec(v_stx_6001_);
v___x_6016_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6016_;
}
else
{
lean_object* v___x_6017_; lean_object* v___y_6019_; lean_object* v___y_6020_; lean_object* v___y_6021_; uint8_t v___y_6022_; lean_object* v___y_6023_; lean_object* v___y_6024_; lean_object* v___y_6025_; lean_object* v___y_6026_; lean_object* v___y_6027_; uint8_t v___y_6028_; lean_object* v___y_6029_; lean_object* v___y_6030_; lean_object* v___y_6031_; lean_object* v___y_6032_; lean_object* v___y_6033_; lean_object* v___y_6034_; lean_object* v___y_6035_; lean_object* v___y_6054_; uint8_t v___y_6055_; lean_object* v___y_6056_; lean_object* v___y_6057_; uint8_t v___y_6058_; lean_object* v___y_6059_; lean_object* v___y_6060_; lean_object* v___y_6061_; lean_object* v___y_6062_; lean_object* v___y_6063_; lean_object* v___y_6064_; lean_object* v___y_6065_; lean_object* v___y_6066_; lean_object* v___y_6067_; lean_object* v___y_6068_; lean_object* v___y_6069_; lean_object* v___y_6070_; lean_object* v___y_6073_; lean_object* v___y_6074_; lean_object* v___y_6075_; lean_object* v___y_6076_; lean_object* v___y_6077_; lean_object* v___y_6078_; lean_object* v___y_6079_; uint8_t v___y_6080_; lean_object* v___y_6081_; lean_object* v___y_6082_; lean_object* v___y_6083_; lean_object* v___y_6084_; lean_object* v___y_6085_; uint8_t v___y_6086_; lean_object* v___y_6087_; lean_object* v___y_6088_; lean_object* v___y_6089_; uint8_t v___y_6108_; lean_object* v___y_6109_; lean_object* v___y_6110_; lean_object* v___y_6111_; uint8_t v___y_6112_; lean_object* v___y_6113_; lean_object* v___y_6114_; lean_object* v___y_6115_; lean_object* v___y_6116_; lean_object* v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6119_; lean_object* v___y_6120_; lean_object* v___y_6121_; lean_object* v___y_6122_; lean_object* v___y_6123_; lean_object* v___y_6124_; lean_object* v_tk_6126_; lean_object* v___x_6127_; lean_object* v___y_6129_; lean_object* v___y_6130_; uint8_t v___y_6131_; lean_object* v___y_6132_; lean_object* v___y_6133_; uint8_t v___y_6134_; lean_object* v___y_6135_; lean_object* v___y_6136_; lean_object* v___y_6137_; lean_object* v___y_6138_; lean_object* v___y_6139_; lean_object* v_patType_x3f_6140_; lean_object* v___y_6141_; lean_object* v___y_6142_; lean_object* v___y_6143_; lean_object* v___y_6144_; lean_object* v___y_6145_; lean_object* v___y_6146_; lean_object* v___y_6147_; uint8_t v___y_6192_; lean_object* v___y_6193_; lean_object* v___y_6194_; lean_object* v___y_6195_; lean_object* v___y_6196_; uint8_t v___y_6197_; lean_object* v___y_6198_; lean_object* v___y_6199_; lean_object* v___y_6200_; lean_object* v___y_6201_; lean_object* v_patType_x3f_6202_; lean_object* v___y_6203_; lean_object* v___y_6204_; lean_object* v___y_6205_; lean_object* v___y_6206_; lean_object* v___y_6207_; lean_object* v___y_6208_; lean_object* v___y_6209_; uint8_t v___y_6228_; lean_object* v___y_6229_; lean_object* v___y_6230_; lean_object* v___y_6231_; lean_object* v___y_6232_; lean_object* v_xType_x3f_6233_; lean_object* v___y_6234_; lean_object* v___y_6235_; lean_object* v___y_6236_; lean_object* v___y_6237_; lean_object* v___y_6238_; lean_object* v___y_6239_; lean_object* v___y_6240_; lean_object* v___y_6269_; lean_object* v___y_6270_; lean_object* v___y_6271_; lean_object* v___y_6272_; uint8_t v___y_6273_; lean_object* v___y_6274_; lean_object* v___y_6275_; lean_object* v___y_6276_; lean_object* v___y_6277_; lean_object* v___y_6278_; lean_object* v___y_6279_; lean_object* v___y_6280_; lean_object* v___y_6281_; lean_object* v___y_6282_; lean_object* v___y_6283_; lean_object* v___y_6284_; lean_object* v___y_6285_; lean_object* v___y_6328_; lean_object* v___y_6329_; lean_object* v___y_6330_; lean_object* v___y_6331_; uint8_t v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6335_; lean_object* v___y_6336_; lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___y_6339_; lean_object* v___y_6340_; lean_object* v___y_6341_; lean_object* v___y_6342_; lean_object* v___y_6343_; lean_object* v___y_6344_; lean_object* v___y_6345_; lean_object* v___y_6357_; lean_object* v___y_6358_; lean_object* v___y_6359_; lean_object* v___y_6360_; uint8_t v___y_6361_; lean_object* v___y_6362_; lean_object* v___y_6363_; lean_object* v___y_6364_; lean_object* v___y_6365_; lean_object* v___y_6366_; lean_object* v___y_6367_; lean_object* v___y_6368_; lean_object* v___y_6369_; lean_object* v___y_6370_; lean_object* v___y_6371_; lean_object* v___y_6372_; lean_object* v___y_6373_; lean_object* v___y_6374_; lean_object* v___y_6375_; uint8_t v___y_6376_; lean_object* v___y_6379_; lean_object* v___y_6380_; lean_object* v___y_6381_; lean_object* v___y_6382_; uint8_t v___y_6383_; lean_object* v___y_6384_; lean_object* v___y_6385_; lean_object* v___y_6386_; lean_object* v___y_6387_; lean_object* v___y_6388_; lean_object* v___y_6389_; lean_object* v___y_6390_; lean_object* v___y_6391_; lean_object* v___y_6392_; lean_object* v___y_6393_; lean_object* v___y_6394_; lean_object* v___y_6395_; lean_object* v___y_6396_; lean_object* v___y_6397_; uint8_t v___y_6398_; lean_object* v_mutTk_x3f_6401_; lean_object* v___y_6402_; lean_object* v___y_6403_; lean_object* v___y_6404_; lean_object* v___y_6405_; lean_object* v___y_6406_; lean_object* v___y_6407_; lean_object* v___y_6408_; lean_object* v___x_6442_; uint8_t v___x_6443_; 
v___x_6017_ = lean_unsigned_to_nat(0u);
v_tk_6126_ = l_Lean_Syntax_getArg(v_stx_6001_, v___x_6017_);
v___x_6127_ = lean_unsigned_to_nat(1u);
v___x_6442_ = l_Lean_Syntax_getArg(v_stx_6001_, v___x_6127_);
v___x_6443_ = l_Lean_Syntax_isNone(v___x_6442_);
if (v___x_6443_ == 0)
{
uint8_t v___x_6444_; 
lean_inc(v___x_6442_);
v___x_6444_ = l_Lean_Syntax_matchesNull(v___x_6442_, v___x_6127_);
if (v___x_6444_ == 0)
{
lean_object* v___x_6445_; 
lean_dec(v___x_6442_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
lean_dec(v_stx_6001_);
v___x_6445_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6445_;
}
else
{
lean_object* v_mutTk_x3f_6446_; lean_object* v___x_6447_; 
v_mutTk_x3f_6446_ = l_Lean_Syntax_getArg(v___x_6442_, v___x_6017_);
lean_dec(v___x_6442_);
v___x_6447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6447_, 0, v_mutTk_x3f_6446_);
v_mutTk_x3f_6401_ = v___x_6447_;
v___y_6402_ = v_a_6003_;
v___y_6403_ = v_a_6004_;
v___y_6404_ = v_a_6005_;
v___y_6405_ = v_a_6006_;
v___y_6406_ = v_a_6007_;
v___y_6407_ = v_a_6008_;
v___y_6408_ = v_a_6009_;
goto v___jp_6400_;
}
}
else
{
lean_object* v___x_6448_; 
lean_dec(v___x_6442_);
v___x_6448_ = lean_box(0);
v_mutTk_x3f_6401_ = v___x_6448_;
v___y_6402_ = v_a_6003_;
v___y_6403_ = v_a_6004_;
v___y_6404_ = v_a_6005_;
v___y_6405_ = v_a_6006_;
v___y_6406_ = v_a_6007_;
v___y_6407_ = v_a_6008_;
v___y_6408_ = v_a_6009_;
goto v___jp_6400_;
}
v___jp_6018_:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6036_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6037_ = l_Lean_Core_mkFreshUserName(v___x_6036_, v___y_6032_, v___y_6033_);
if (lean_obj_tag(v___x_6037_) == 0)
{
lean_object* v_a_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___y_6042_; uint8_t v___x_6043_; lean_object* v___x_6044_; 
v_a_6038_ = lean_ctor_get(v___x_6037_, 0);
lean_inc(v_a_6038_);
lean_dec_ref_known(v___x_6037_, 1);
v___x_6039_ = l_Lean_mkIdentFrom(v___y_6020_, v_a_6038_, v___y_6022_);
lean_dec(v___y_6020_);
v___x_6040_ = lean_box(v___y_6028_);
v___x_6041_ = lean_box(v___x_6015_);
lean_inc(v___x_6039_);
lean_inc(v___y_6027_);
v___y_6042_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_6042_, 0, v___y_6026_);
lean_closure_set(v___y_6042_, 1, v___x_6040_);
lean_closure_set(v___y_6042_, 2, v___x_6011_);
lean_closure_set(v___y_6042_, 3, v___x_6012_);
lean_closure_set(v___y_6042_, 4, v___x_6013_);
lean_closure_set(v___y_6042_, 5, v___y_6027_);
lean_closure_set(v___y_6042_, 6, v___y_6029_);
lean_closure_set(v___y_6042_, 7, v___x_6039_);
lean_closure_set(v___y_6042_, 8, v_dec_6002_);
lean_closure_set(v___y_6042_, 9, v___x_6041_);
lean_closure_set(v___y_6042_, 10, v___y_6023_);
lean_closure_set(v___y_6042_, 11, v___x_6017_);
lean_closure_set(v___y_6042_, 12, v___y_6035_);
v___x_6043_ = 0;
v___x_6044_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6039_, v___y_6024_, v___y_6025_, v___y_6042_, v___x_6043_, v___y_6031_, v___y_6019_, v___y_6021_, v___y_6030_, v___y_6034_, v___y_6032_, v___y_6033_);
return v___x_6044_;
}
else
{
lean_object* v_a_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6052_; 
lean_dec(v___y_6035_);
lean_dec(v___y_6029_);
lean_dec(v___y_6026_);
lean_dec(v___y_6025_);
lean_dec(v___y_6024_);
lean_dec(v___y_6023_);
lean_dec(v___y_6020_);
lean_dec_ref(v_dec_6002_);
v_a_6045_ = lean_ctor_get(v___x_6037_, 0);
v_isSharedCheck_6052_ = !lean_is_exclusive(v___x_6037_);
if (v_isSharedCheck_6052_ == 0)
{
v___x_6047_ = v___x_6037_;
v_isShared_6048_ = v_isSharedCheck_6052_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_a_6045_);
lean_dec(v___x_6037_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6052_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v___x_6050_; 
if (v_isShared_6048_ == 0)
{
v___x_6050_ = v___x_6047_;
goto v_reusejp_6049_;
}
else
{
lean_object* v_reuseFailAlloc_6051_; 
v_reuseFailAlloc_6051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_a_6045_);
v___x_6050_ = v_reuseFailAlloc_6051_;
goto v_reusejp_6049_;
}
v_reusejp_6049_:
{
return v___x_6050_;
}
}
}
}
v___jp_6053_:
{
lean_object* v___x_6071_; 
v___x_6071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6071_, 0, v___y_6059_);
v___y_6019_ = v___y_6067_;
v___y_6020_ = v___y_6065_;
v___y_6021_ = v___y_6068_;
v___y_6022_ = v___y_6058_;
v___y_6023_ = v___y_6057_;
v___y_6024_ = v___y_6061_;
v___y_6025_ = v___y_6066_;
v___y_6026_ = v___x_6071_;
v___y_6027_ = v___y_6054_;
v___y_6028_ = v___y_6055_;
v___y_6029_ = v___y_6056_;
v___y_6030_ = v___y_6069_;
v___y_6031_ = v___y_6063_;
v___y_6032_ = v___y_6064_;
v___y_6033_ = v___y_6060_;
v___y_6034_ = v___y_6062_;
v___y_6035_ = v___y_6070_;
goto v___jp_6018_;
}
v___jp_6072_:
{
lean_object* v___x_6090_; lean_object* v___x_6091_; 
v___x_6090_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6091_ = l_Lean_Core_mkFreshUserName(v___x_6090_, v___y_6079_, v___y_6073_);
if (lean_obj_tag(v___x_6091_) == 0)
{
lean_object* v_a_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___y_6096_; uint8_t v___x_6097_; lean_object* v___x_6098_; 
v_a_6092_ = lean_ctor_get(v___x_6091_, 0);
lean_inc(v_a_6092_);
lean_dec_ref_known(v___x_6091_, 1);
v___x_6093_ = l_Lean_mkIdentFrom(v___y_6088_, v_a_6092_, v___y_6086_);
lean_dec(v___y_6088_);
v___x_6094_ = lean_box(v___y_6080_);
v___x_6095_ = lean_box(v___x_6015_);
lean_inc(v___x_6093_);
lean_inc(v___y_6081_);
v___y_6096_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed), 21, 13);
lean_closure_set(v___y_6096_, 0, v___y_6074_);
lean_closure_set(v___y_6096_, 1, v___x_6094_);
lean_closure_set(v___y_6096_, 2, v___x_6011_);
lean_closure_set(v___y_6096_, 3, v___x_6012_);
lean_closure_set(v___y_6096_, 4, v___x_6013_);
lean_closure_set(v___y_6096_, 5, v___y_6081_);
lean_closure_set(v___y_6096_, 6, v___y_6084_);
lean_closure_set(v___y_6096_, 7, v___x_6093_);
lean_closure_set(v___y_6096_, 8, v_dec_6002_);
lean_closure_set(v___y_6096_, 9, v___x_6095_);
lean_closure_set(v___y_6096_, 10, v___y_6076_);
lean_closure_set(v___y_6096_, 11, v___x_6017_);
lean_closure_set(v___y_6096_, 12, v___y_6089_);
v___x_6097_ = 0;
v___x_6098_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6093_, v___y_6085_, v___y_6075_, v___y_6096_, v___x_6097_, v___y_6082_, v___y_6083_, v___y_6087_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6073_);
return v___x_6098_;
}
else
{
lean_object* v_a_6099_; lean_object* v___x_6101_; uint8_t v_isShared_6102_; uint8_t v_isSharedCheck_6106_; 
lean_dec(v___y_6089_);
lean_dec(v___y_6088_);
lean_dec(v___y_6085_);
lean_dec(v___y_6084_);
lean_dec(v___y_6076_);
lean_dec(v___y_6075_);
lean_dec(v___y_6074_);
lean_dec_ref(v_dec_6002_);
v_a_6099_ = lean_ctor_get(v___x_6091_, 0);
v_isSharedCheck_6106_ = !lean_is_exclusive(v___x_6091_);
if (v_isSharedCheck_6106_ == 0)
{
v___x_6101_ = v___x_6091_;
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
else
{
lean_inc(v_a_6099_);
lean_dec(v___x_6091_);
v___x_6101_ = lean_box(0);
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
v_resetjp_6100_:
{
lean_object* v___x_6104_; 
if (v_isShared_6102_ == 0)
{
v___x_6104_ = v___x_6101_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v_a_6099_);
v___x_6104_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
return v___x_6104_;
}
}
}
}
v___jp_6107_:
{
lean_object* v___x_6125_; 
v___x_6125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6125_, 0, v___y_6117_);
v___y_6073_ = v___y_6116_;
v___y_6074_ = v___x_6125_;
v___y_6075_ = v___y_6118_;
v___y_6076_ = v___y_6111_;
v___y_6077_ = v___y_6122_;
v___y_6078_ = v___y_6123_;
v___y_6079_ = v___y_6115_;
v___y_6080_ = v___y_6108_;
v___y_6081_ = v___y_6109_;
v___y_6082_ = v___y_6120_;
v___y_6083_ = v___y_6114_;
v___y_6084_ = v___y_6110_;
v___y_6085_ = v___y_6113_;
v___y_6086_ = v___y_6112_;
v___y_6087_ = v___y_6121_;
v___y_6088_ = v___y_6119_;
v___y_6089_ = v___y_6124_;
goto v___jp_6072_;
}
v___jp_6128_:
{
lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; uint8_t v___x_6151_; 
v___x_6148_ = l_Lean_Syntax_getArg(v___y_6138_, v___y_6137_);
v___x_6149_ = lean_unsigned_to_nat(4u);
v___x_6150_ = l_Lean_Syntax_getArg(v___y_6138_, v___x_6149_);
lean_dec(v___y_6138_);
lean_inc(v___x_6150_);
v___x_6151_ = l_Lean_Syntax_matchesNull(v___x_6150_, v___x_6017_);
if (v___x_6151_ == 0)
{
uint8_t v___x_6152_; 
lean_dec(v___y_6139_);
lean_dec(v_tk_6126_);
v___x_6152_ = l_Lean_Syntax_isNone(v___x_6150_);
if (v___x_6152_ == 0)
{
uint8_t v___x_6153_; 
lean_inc(v___x_6150_);
v___x_6153_ = l_Lean_Syntax_matchesNull(v___x_6150_, v___y_6137_);
if (v___x_6153_ == 0)
{
lean_object* v___x_6154_; 
lean_dec(v___x_6150_);
lean_dec(v___x_6148_);
lean_dec(v_patType_x3f_6140_);
lean_dec(v___y_6136_);
lean_dec(v___y_6132_);
lean_dec(v___y_6130_);
lean_dec_ref(v_dec_6002_);
v___x_6154_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6154_;
}
else
{
lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; 
v___x_6155_ = l_Lean_Syntax_getArg(v___x_6150_, v___x_6127_);
v___x_6156_ = l_Lean_Syntax_getArg(v___x_6150_, v___y_6133_);
lean_dec(v___x_6150_);
v___x_6157_ = l_Lean_Syntax_getOptional_x3f(v___x_6156_);
lean_dec(v___x_6156_);
if (lean_obj_tag(v___x_6157_) == 0)
{
lean_inc(v___y_6135_);
v___y_6054_ = v___y_6129_;
v___y_6055_ = v___y_6131_;
v___y_6056_ = v___y_6130_;
v___y_6057_ = v___y_6132_;
v___y_6058_ = v___y_6134_;
v___y_6059_ = v___x_6155_;
v___y_6060_ = v___y_6147_;
v___y_6061_ = v_patType_x3f_6140_;
v___y_6062_ = v___y_6145_;
v___y_6063_ = v___y_6141_;
v___y_6064_ = v___y_6146_;
v___y_6065_ = v___y_6136_;
v___y_6066_ = v___x_6148_;
v___y_6067_ = v___y_6142_;
v___y_6068_ = v___y_6143_;
v___y_6069_ = v___y_6144_;
v___y_6070_ = v___y_6135_;
goto v___jp_6053_;
}
else
{
lean_object* v_val_6158_; lean_object* v___x_6160_; uint8_t v_isShared_6161_; uint8_t v_isSharedCheck_6165_; 
v_val_6158_ = lean_ctor_get(v___x_6157_, 0);
v_isSharedCheck_6165_ = !lean_is_exclusive(v___x_6157_);
if (v_isSharedCheck_6165_ == 0)
{
v___x_6160_ = v___x_6157_;
v_isShared_6161_ = v_isSharedCheck_6165_;
goto v_resetjp_6159_;
}
else
{
lean_inc(v_val_6158_);
lean_dec(v___x_6157_);
v___x_6160_ = lean_box(0);
v_isShared_6161_ = v_isSharedCheck_6165_;
goto v_resetjp_6159_;
}
v_resetjp_6159_:
{
lean_object* v___x_6163_; 
if (v_isShared_6161_ == 0)
{
v___x_6163_ = v___x_6160_;
goto v_reusejp_6162_;
}
else
{
lean_object* v_reuseFailAlloc_6164_; 
v_reuseFailAlloc_6164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6164_, 0, v_val_6158_);
v___x_6163_ = v_reuseFailAlloc_6164_;
goto v_reusejp_6162_;
}
v_reusejp_6162_:
{
v___y_6054_ = v___y_6129_;
v___y_6055_ = v___y_6131_;
v___y_6056_ = v___y_6130_;
v___y_6057_ = v___y_6132_;
v___y_6058_ = v___y_6134_;
v___y_6059_ = v___x_6155_;
v___y_6060_ = v___y_6147_;
v___y_6061_ = v_patType_x3f_6140_;
v___y_6062_ = v___y_6145_;
v___y_6063_ = v___y_6141_;
v___y_6064_ = v___y_6146_;
v___y_6065_ = v___y_6136_;
v___y_6066_ = v___x_6148_;
v___y_6067_ = v___y_6142_;
v___y_6068_ = v___y_6143_;
v___y_6069_ = v___y_6144_;
v___y_6070_ = v___x_6163_;
goto v___jp_6053_;
}
}
}
}
}
else
{
lean_dec(v___x_6150_);
lean_inc_n(v___y_6135_, 2);
v___y_6019_ = v___y_6142_;
v___y_6020_ = v___y_6136_;
v___y_6021_ = v___y_6143_;
v___y_6022_ = v___y_6134_;
v___y_6023_ = v___y_6132_;
v___y_6024_ = v_patType_x3f_6140_;
v___y_6025_ = v___x_6148_;
v___y_6026_ = v___y_6135_;
v___y_6027_ = v___y_6129_;
v___y_6028_ = v___y_6131_;
v___y_6029_ = v___y_6130_;
v___y_6030_ = v___y_6144_;
v___y_6031_ = v___y_6141_;
v___y_6032_ = v___y_6146_;
v___y_6033_ = v___y_6147_;
v___y_6034_ = v___y_6145_;
v___y_6035_ = v___y_6135_;
goto v___jp_6018_;
}
}
else
{
lean_object* v___x_6166_; lean_object* v___x_6167_; 
lean_dec(v___x_6150_);
lean_dec(v___y_6136_);
lean_dec(v___y_6132_);
lean_dec(v___y_6130_);
v___x_6166_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6167_ = l_Lean_Core_mkFreshUserName(v___x_6166_, v___y_6146_, v___y_6147_);
if (lean_obj_tag(v___x_6167_) == 0)
{
lean_object* v_a_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; 
v_a_6168_ = lean_ctor_get(v___x_6167_, 0);
lean_inc(v_a_6168_);
lean_dec_ref_known(v___x_6167_, 1);
v___x_6169_ = l_Lean_mkIdentFrom(v___y_6139_, v_a_6168_, v___y_6134_);
lean_dec(v___y_6139_);
v___x_6170_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_6002_, v_tk_6126_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
lean_dec(v_tk_6126_);
if (lean_obj_tag(v___x_6170_) == 0)
{
lean_object* v_a_6171_; uint8_t v_kind_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; 
v_a_6171_ = lean_ctor_get(v___x_6170_, 0);
lean_inc(v_a_6171_);
lean_dec_ref_known(v___x_6170_, 1);
v_kind_6172_ = lean_ctor_get_uint8(v_a_6171_, sizeof(void*)*3);
v___x_6173_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6173_, 0, v_a_6171_);
v___x_6174_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6169_, v_patType_x3f_6140_, v___x_6148_, v___x_6173_, v_kind_6172_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
return v___x_6174_;
}
else
{
lean_object* v_a_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6182_; 
lean_dec(v___x_6169_);
lean_dec(v___x_6148_);
lean_dec(v_patType_x3f_6140_);
v_a_6175_ = lean_ctor_get(v___x_6170_, 0);
v_isSharedCheck_6182_ = !lean_is_exclusive(v___x_6170_);
if (v_isSharedCheck_6182_ == 0)
{
v___x_6177_ = v___x_6170_;
v_isShared_6178_ = v_isSharedCheck_6182_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_a_6175_);
lean_dec(v___x_6170_);
v___x_6177_ = lean_box(0);
v_isShared_6178_ = v_isSharedCheck_6182_;
goto v_resetjp_6176_;
}
v_resetjp_6176_:
{
lean_object* v___x_6180_; 
if (v_isShared_6178_ == 0)
{
v___x_6180_ = v___x_6177_;
goto v_reusejp_6179_;
}
else
{
lean_object* v_reuseFailAlloc_6181_; 
v_reuseFailAlloc_6181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_a_6175_);
v___x_6180_ = v_reuseFailAlloc_6181_;
goto v_reusejp_6179_;
}
v_reusejp_6179_:
{
return v___x_6180_;
}
}
}
}
else
{
lean_object* v_a_6183_; lean_object* v___x_6185_; uint8_t v_isShared_6186_; uint8_t v_isSharedCheck_6190_; 
lean_dec(v___x_6148_);
lean_dec(v_patType_x3f_6140_);
lean_dec(v___y_6139_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v_a_6183_ = lean_ctor_get(v___x_6167_, 0);
v_isSharedCheck_6190_ = !lean_is_exclusive(v___x_6167_);
if (v_isSharedCheck_6190_ == 0)
{
v___x_6185_ = v___x_6167_;
v_isShared_6186_ = v_isSharedCheck_6190_;
goto v_resetjp_6184_;
}
else
{
lean_inc(v_a_6183_);
lean_dec(v___x_6167_);
v___x_6185_ = lean_box(0);
v_isShared_6186_ = v_isSharedCheck_6190_;
goto v_resetjp_6184_;
}
v_resetjp_6184_:
{
lean_object* v___x_6188_; 
if (v_isShared_6186_ == 0)
{
v___x_6188_ = v___x_6185_;
goto v_reusejp_6187_;
}
else
{
lean_object* v_reuseFailAlloc_6189_; 
v_reuseFailAlloc_6189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6189_, 0, v_a_6183_);
v___x_6188_ = v_reuseFailAlloc_6189_;
goto v_reusejp_6187_;
}
v_reusejp_6187_:
{
return v___x_6188_;
}
}
}
}
}
v___jp_6191_:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; uint8_t v___x_6213_; 
v___x_6210_ = l_Lean_Syntax_getArg(v___y_6201_, v___y_6200_);
v___x_6211_ = lean_unsigned_to_nat(4u);
v___x_6212_ = l_Lean_Syntax_getArg(v___y_6201_, v___x_6211_);
lean_dec(v___y_6201_);
v___x_6213_ = l_Lean_Syntax_isNone(v___x_6212_);
if (v___x_6213_ == 0)
{
uint8_t v___x_6214_; 
lean_inc(v___x_6212_);
v___x_6214_ = l_Lean_Syntax_matchesNull(v___x_6212_, v___y_6200_);
if (v___x_6214_ == 0)
{
lean_object* v___x_6215_; 
lean_dec(v___x_6212_);
lean_dec(v___x_6210_);
lean_dec(v_patType_x3f_6202_);
lean_dec(v___y_6199_);
lean_dec(v___y_6195_);
lean_dec(v___y_6194_);
lean_dec_ref(v_dec_6002_);
v___x_6215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6215_;
}
else
{
lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; 
v___x_6216_ = l_Lean_Syntax_getArg(v___x_6212_, v___x_6127_);
v___x_6217_ = l_Lean_Syntax_getArg(v___x_6212_, v___y_6196_);
lean_dec(v___x_6212_);
v___x_6218_ = l_Lean_Syntax_getOptional_x3f(v___x_6217_);
lean_dec(v___x_6217_);
if (lean_obj_tag(v___x_6218_) == 0)
{
lean_inc(v___y_6198_);
v___y_6108_ = v___y_6192_;
v___y_6109_ = v___y_6193_;
v___y_6110_ = v___y_6194_;
v___y_6111_ = v___y_6195_;
v___y_6112_ = v___y_6197_;
v___y_6113_ = v_patType_x3f_6202_;
v___y_6114_ = v___y_6204_;
v___y_6115_ = v___y_6208_;
v___y_6116_ = v___y_6209_;
v___y_6117_ = v___x_6216_;
v___y_6118_ = v___x_6210_;
v___y_6119_ = v___y_6199_;
v___y_6120_ = v___y_6203_;
v___y_6121_ = v___y_6205_;
v___y_6122_ = v___y_6206_;
v___y_6123_ = v___y_6207_;
v___y_6124_ = v___y_6198_;
goto v___jp_6107_;
}
else
{
lean_object* v_val_6219_; lean_object* v___x_6221_; uint8_t v_isShared_6222_; uint8_t v_isSharedCheck_6226_; 
v_val_6219_ = lean_ctor_get(v___x_6218_, 0);
v_isSharedCheck_6226_ = !lean_is_exclusive(v___x_6218_);
if (v_isSharedCheck_6226_ == 0)
{
v___x_6221_ = v___x_6218_;
v_isShared_6222_ = v_isSharedCheck_6226_;
goto v_resetjp_6220_;
}
else
{
lean_inc(v_val_6219_);
lean_dec(v___x_6218_);
v___x_6221_ = lean_box(0);
v_isShared_6222_ = v_isSharedCheck_6226_;
goto v_resetjp_6220_;
}
v_resetjp_6220_:
{
lean_object* v___x_6224_; 
if (v_isShared_6222_ == 0)
{
v___x_6224_ = v___x_6221_;
goto v_reusejp_6223_;
}
else
{
lean_object* v_reuseFailAlloc_6225_; 
v_reuseFailAlloc_6225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6225_, 0, v_val_6219_);
v___x_6224_ = v_reuseFailAlloc_6225_;
goto v_reusejp_6223_;
}
v_reusejp_6223_:
{
v___y_6108_ = v___y_6192_;
v___y_6109_ = v___y_6193_;
v___y_6110_ = v___y_6194_;
v___y_6111_ = v___y_6195_;
v___y_6112_ = v___y_6197_;
v___y_6113_ = v_patType_x3f_6202_;
v___y_6114_ = v___y_6204_;
v___y_6115_ = v___y_6208_;
v___y_6116_ = v___y_6209_;
v___y_6117_ = v___x_6216_;
v___y_6118_ = v___x_6210_;
v___y_6119_ = v___y_6199_;
v___y_6120_ = v___y_6203_;
v___y_6121_ = v___y_6205_;
v___y_6122_ = v___y_6206_;
v___y_6123_ = v___y_6207_;
v___y_6124_ = v___x_6224_;
goto v___jp_6107_;
}
}
}
}
}
else
{
lean_dec(v___x_6212_);
lean_inc_n(v___y_6198_, 2);
v___y_6073_ = v___y_6209_;
v___y_6074_ = v___y_6198_;
v___y_6075_ = v___x_6210_;
v___y_6076_ = v___y_6195_;
v___y_6077_ = v___y_6206_;
v___y_6078_ = v___y_6207_;
v___y_6079_ = v___y_6208_;
v___y_6080_ = v___y_6192_;
v___y_6081_ = v___y_6193_;
v___y_6082_ = v___y_6203_;
v___y_6083_ = v___y_6204_;
v___y_6084_ = v___y_6194_;
v___y_6085_ = v_patType_x3f_6202_;
v___y_6086_ = v___y_6197_;
v___y_6087_ = v___y_6205_;
v___y_6088_ = v___y_6199_;
v___y_6089_ = v___y_6198_;
goto v___jp_6072_;
}
}
v___jp_6227_:
{
lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; 
v___x_6241_ = l_Lean_Syntax_getArg(v___y_6232_, v___y_6229_);
lean_dec(v___y_6232_);
v___x_6242_ = lean_mk_empty_array_with_capacity(v___x_6127_);
lean_inc(v___y_6231_);
v___x_6243_ = lean_array_push(v___x_6242_, v___y_6231_);
v___x_6244_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_6243_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_);
lean_dec_ref(v___x_6243_);
if (lean_obj_tag(v___x_6244_) == 0)
{
lean_object* v___x_6245_; 
lean_dec_ref_known(v___x_6244_, 1);
v___x_6245_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_6002_, v_tk_6126_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_);
lean_dec(v_tk_6126_);
if (lean_obj_tag(v___x_6245_) == 0)
{
lean_object* v_a_6246_; uint8_t v_kind_6247_; lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; 
v_a_6246_ = lean_ctor_get(v___x_6245_, 0);
lean_inc(v_a_6246_);
lean_dec_ref_known(v___x_6245_, 1);
v_kind_6247_ = lean_ctor_get_uint8(v_a_6246_, sizeof(void*)*3);
v___x_6248_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6248_, 0, v_a_6246_);
v___x_6249_ = lean_box(v___y_6228_);
lean_inc(v___y_6231_);
v___x_6250_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 13, 5);
lean_closure_set(v___x_6250_, 0, lean_box(0));
lean_closure_set(v___x_6250_, 1, v___y_6230_);
lean_closure_set(v___x_6250_, 2, v___y_6231_);
lean_closure_set(v___x_6250_, 3, v___x_6249_);
lean_closure_set(v___x_6250_, 4, v___x_6248_);
v___x_6251_ = l_Lean_Elab_Do_elabDoIdDecl(v___y_6231_, v_xType_x3f_6233_, v___x_6241_, v___x_6250_, v_kind_6247_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_);
return v___x_6251_;
}
else
{
lean_object* v_a_6252_; lean_object* v___x_6254_; uint8_t v_isShared_6255_; uint8_t v_isSharedCheck_6259_; 
lean_dec(v___x_6241_);
lean_dec(v_xType_x3f_6233_);
lean_dec(v___y_6231_);
lean_dec(v___y_6230_);
v_a_6252_ = lean_ctor_get(v___x_6245_, 0);
v_isSharedCheck_6259_ = !lean_is_exclusive(v___x_6245_);
if (v_isSharedCheck_6259_ == 0)
{
v___x_6254_ = v___x_6245_;
v_isShared_6255_ = v_isSharedCheck_6259_;
goto v_resetjp_6253_;
}
else
{
lean_inc(v_a_6252_);
lean_dec(v___x_6245_);
v___x_6254_ = lean_box(0);
v_isShared_6255_ = v_isSharedCheck_6259_;
goto v_resetjp_6253_;
}
v_resetjp_6253_:
{
lean_object* v___x_6257_; 
if (v_isShared_6255_ == 0)
{
v___x_6257_ = v___x_6254_;
goto v_reusejp_6256_;
}
else
{
lean_object* v_reuseFailAlloc_6258_; 
v_reuseFailAlloc_6258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6258_, 0, v_a_6252_);
v___x_6257_ = v_reuseFailAlloc_6258_;
goto v_reusejp_6256_;
}
v_reusejp_6256_:
{
return v___x_6257_;
}
}
}
}
else
{
lean_object* v_a_6260_; lean_object* v___x_6262_; uint8_t v_isShared_6263_; uint8_t v_isSharedCheck_6267_; 
lean_dec(v___x_6241_);
lean_dec(v_xType_x3f_6233_);
lean_dec(v___y_6231_);
lean_dec(v___y_6230_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v_a_6260_ = lean_ctor_get(v___x_6244_, 0);
v_isSharedCheck_6267_ = !lean_is_exclusive(v___x_6244_);
if (v_isSharedCheck_6267_ == 0)
{
v___x_6262_ = v___x_6244_;
v_isShared_6263_ = v_isSharedCheck_6267_;
goto v_resetjp_6261_;
}
else
{
lean_inc(v_a_6260_);
lean_dec(v___x_6244_);
v___x_6262_ = lean_box(0);
v_isShared_6263_ = v_isSharedCheck_6267_;
goto v_resetjp_6261_;
}
v_resetjp_6261_:
{
lean_object* v___x_6265_; 
if (v_isShared_6263_ == 0)
{
v___x_6265_ = v___x_6262_;
goto v_reusejp_6264_;
}
else
{
lean_object* v_reuseFailAlloc_6266_; 
v_reuseFailAlloc_6266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6266_, 0, v_a_6260_);
v___x_6265_ = v_reuseFailAlloc_6266_;
goto v_reusejp_6264_;
}
v_reusejp_6264_:
{
return v___x_6265_;
}
}
}
}
v___jp_6268_:
{
uint8_t v___x_6286_; 
lean_inc(v___y_6278_);
v___x_6286_ = l_Lean_Syntax_isOfKind(v___y_6278_, v___y_6276_);
if (v___x_6286_ == 0)
{
uint8_t v___x_6287_; 
lean_dec(v___y_6277_);
lean_inc(v___y_6278_);
v___x_6287_ = l_Lean_Syntax_isOfKind(v___y_6278_, v___y_6275_);
if (v___x_6287_ == 0)
{
lean_object* v___x_6288_; 
lean_dec(v___y_6278_);
lean_dec(v___y_6270_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v___x_6288_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6288_;
}
else
{
lean_object* v___x_6289_; lean_object* v___x_6290_; uint8_t v___x_6291_; 
v___x_6289_ = l_Lean_Syntax_getArg(v___y_6278_, v___x_6017_);
v___x_6290_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
lean_inc(v___x_6289_);
v___x_6291_ = l_Lean_Syntax_isOfKind(v___x_6289_, v___x_6290_);
if (v___x_6291_ == 0)
{
lean_object* v___x_6292_; uint8_t v___x_6293_; 
lean_dec(v_tk_6126_);
v___x_6292_ = l_Lean_Syntax_getArg(v___y_6278_, v___x_6127_);
v___x_6293_ = l_Lean_Syntax_isNone(v___x_6292_);
if (v___x_6293_ == 0)
{
uint8_t v___x_6294_; 
lean_inc(v___x_6292_);
v___x_6294_ = l_Lean_Syntax_matchesNull(v___x_6292_, v___x_6127_);
if (v___x_6294_ == 0)
{
lean_object* v___x_6295_; 
lean_dec(v___x_6292_);
lean_dec(v___x_6289_);
lean_dec(v___y_6278_);
lean_dec(v___y_6270_);
lean_dec_ref(v_dec_6002_);
v___x_6295_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6295_;
}
else
{
lean_object* v___x_6296_; lean_object* v___x_6297_; uint8_t v___x_6298_; 
v___x_6296_ = l_Lean_Syntax_getArg(v___x_6292_, v___x_6017_);
lean_dec(v___x_6292_);
v___x_6297_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6296_);
v___x_6298_ = l_Lean_Syntax_isOfKind(v___x_6296_, v___x_6297_);
if (v___x_6298_ == 0)
{
lean_object* v___x_6299_; 
lean_dec(v___x_6296_);
lean_dec(v___x_6289_);
lean_dec(v___y_6278_);
lean_dec(v___y_6270_);
lean_dec_ref(v_dec_6002_);
v___x_6299_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6299_;
}
else
{
lean_object* v___x_6300_; lean_object* v___x_6301_; 
v___x_6300_ = l_Lean_Syntax_getArg(v___x_6296_, v___x_6127_);
lean_dec(v___x_6296_);
v___x_6301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6301_, 0, v___x_6300_);
lean_inc(v___x_6289_);
v___y_6192_ = v___x_6291_;
v___y_6193_ = v___y_6269_;
v___y_6194_ = v___x_6289_;
v___y_6195_ = v___y_6270_;
v___y_6196_ = v___y_6271_;
v___y_6197_ = v___y_6273_;
v___y_6198_ = v___y_6272_;
v___y_6199_ = v___x_6289_;
v___y_6200_ = v___y_6274_;
v___y_6201_ = v___y_6278_;
v_patType_x3f_6202_ = v___x_6301_;
v___y_6203_ = v___y_6279_;
v___y_6204_ = v___y_6280_;
v___y_6205_ = v___y_6281_;
v___y_6206_ = v___y_6282_;
v___y_6207_ = v___y_6283_;
v___y_6208_ = v___y_6284_;
v___y_6209_ = v___y_6285_;
goto v___jp_6191_;
}
}
}
else
{
lean_dec(v___x_6292_);
lean_inc(v___y_6272_);
lean_inc(v___x_6289_);
v___y_6192_ = v___x_6291_;
v___y_6193_ = v___y_6269_;
v___y_6194_ = v___x_6289_;
v___y_6195_ = v___y_6270_;
v___y_6196_ = v___y_6271_;
v___y_6197_ = v___y_6273_;
v___y_6198_ = v___y_6272_;
v___y_6199_ = v___x_6289_;
v___y_6200_ = v___y_6274_;
v___y_6201_ = v___y_6278_;
v_patType_x3f_6202_ = v___y_6272_;
v___y_6203_ = v___y_6279_;
v___y_6204_ = v___y_6280_;
v___y_6205_ = v___y_6281_;
v___y_6206_ = v___y_6282_;
v___y_6207_ = v___y_6283_;
v___y_6208_ = v___y_6284_;
v___y_6209_ = v___y_6285_;
goto v___jp_6191_;
}
}
else
{
lean_object* v___x_6302_; lean_object* v___x_6303_; uint8_t v___x_6304_; 
v___x_6302_ = l_Lean_Syntax_getArg(v___x_6289_, v___x_6017_);
v___x_6303_ = l_Lean_Syntax_getArg(v___y_6278_, v___x_6127_);
v___x_6304_ = l_Lean_Syntax_isNone(v___x_6303_);
if (v___x_6304_ == 0)
{
uint8_t v___x_6305_; 
lean_inc(v___x_6303_);
v___x_6305_ = l_Lean_Syntax_matchesNull(v___x_6303_, v___x_6127_);
if (v___x_6305_ == 0)
{
lean_object* v___x_6306_; 
lean_dec(v___x_6303_);
lean_dec(v___x_6302_);
lean_dec(v___x_6289_);
lean_dec(v___y_6278_);
lean_dec(v___y_6270_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v___x_6306_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6306_;
}
else
{
lean_object* v___x_6307_; lean_object* v___x_6308_; uint8_t v___x_6309_; 
v___x_6307_ = l_Lean_Syntax_getArg(v___x_6303_, v___x_6017_);
lean_dec(v___x_6303_);
v___x_6308_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6307_);
v___x_6309_ = l_Lean_Syntax_isOfKind(v___x_6307_, v___x_6308_);
if (v___x_6309_ == 0)
{
lean_object* v___x_6310_; 
lean_dec(v___x_6307_);
lean_dec(v___x_6302_);
lean_dec(v___x_6289_);
lean_dec(v___y_6278_);
lean_dec(v___y_6270_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v___x_6310_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6310_;
}
else
{
lean_object* v___x_6311_; lean_object* v___x_6312_; 
v___x_6311_ = l_Lean_Syntax_getArg(v___x_6307_, v___x_6127_);
lean_dec(v___x_6307_);
v___x_6312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6312_, 0, v___x_6311_);
lean_inc(v___x_6289_);
v___y_6129_ = v___y_6269_;
v___y_6130_ = v___x_6289_;
v___y_6131_ = v___x_6286_;
v___y_6132_ = v___y_6270_;
v___y_6133_ = v___y_6271_;
v___y_6134_ = v___y_6273_;
v___y_6135_ = v___y_6272_;
v___y_6136_ = v___x_6289_;
v___y_6137_ = v___y_6274_;
v___y_6138_ = v___y_6278_;
v___y_6139_ = v___x_6302_;
v_patType_x3f_6140_ = v___x_6312_;
v___y_6141_ = v___y_6279_;
v___y_6142_ = v___y_6280_;
v___y_6143_ = v___y_6281_;
v___y_6144_ = v___y_6282_;
v___y_6145_ = v___y_6283_;
v___y_6146_ = v___y_6284_;
v___y_6147_ = v___y_6285_;
goto v___jp_6128_;
}
}
}
else
{
lean_dec(v___x_6303_);
lean_inc(v___y_6272_);
lean_inc(v___x_6289_);
v___y_6129_ = v___y_6269_;
v___y_6130_ = v___x_6289_;
v___y_6131_ = v___x_6286_;
v___y_6132_ = v___y_6270_;
v___y_6133_ = v___y_6271_;
v___y_6134_ = v___y_6273_;
v___y_6135_ = v___y_6272_;
v___y_6136_ = v___x_6289_;
v___y_6137_ = v___y_6274_;
v___y_6138_ = v___y_6278_;
v___y_6139_ = v___x_6302_;
v_patType_x3f_6140_ = v___y_6272_;
v___y_6141_ = v___y_6279_;
v___y_6142_ = v___y_6280_;
v___y_6143_ = v___y_6281_;
v___y_6144_ = v___y_6282_;
v___y_6145_ = v___y_6283_;
v___y_6146_ = v___y_6284_;
v___y_6147_ = v___y_6285_;
goto v___jp_6128_;
}
}
}
}
else
{
lean_object* v___x_6313_; lean_object* v___x_6314_; uint8_t v___x_6315_; 
lean_dec(v___y_6270_);
v___x_6313_ = l_Lean_Syntax_getArg(v___y_6278_, v___x_6017_);
v___x_6314_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_6313_);
v___x_6315_ = l_Lean_Syntax_isOfKind(v___x_6313_, v___x_6314_);
if (v___x_6315_ == 0)
{
lean_object* v___x_6316_; 
lean_dec(v___x_6313_);
lean_dec(v___y_6278_);
lean_dec(v___y_6277_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v___x_6316_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6316_;
}
else
{
lean_object* v___x_6317_; uint8_t v___x_6318_; 
v___x_6317_ = l_Lean_Syntax_getArg(v___y_6278_, v___x_6127_);
v___x_6318_ = l_Lean_Syntax_isNone(v___x_6317_);
if (v___x_6318_ == 0)
{
uint8_t v___x_6319_; 
lean_inc(v___x_6317_);
v___x_6319_ = l_Lean_Syntax_matchesNull(v___x_6317_, v___x_6127_);
if (v___x_6319_ == 0)
{
lean_object* v___x_6320_; 
lean_dec(v___x_6317_);
lean_dec(v___x_6313_);
lean_dec(v___y_6278_);
lean_dec(v___y_6277_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v___x_6320_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6320_;
}
else
{
lean_object* v___x_6321_; lean_object* v___x_6322_; uint8_t v___x_6323_; 
v___x_6321_ = l_Lean_Syntax_getArg(v___x_6317_, v___x_6017_);
lean_dec(v___x_6317_);
v___x_6322_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6321_);
v___x_6323_ = l_Lean_Syntax_isOfKind(v___x_6321_, v___x_6322_);
if (v___x_6323_ == 0)
{
lean_object* v___x_6324_; 
lean_dec(v___x_6321_);
lean_dec(v___x_6313_);
lean_dec(v___y_6278_);
lean_dec(v___y_6277_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v___x_6324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6324_;
}
else
{
lean_object* v___x_6325_; lean_object* v___x_6326_; 
v___x_6325_ = l_Lean_Syntax_getArg(v___x_6321_, v___x_6127_);
lean_dec(v___x_6321_);
v___x_6326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6326_, 0, v___x_6325_);
v___y_6228_ = v___y_6273_;
v___y_6229_ = v___y_6274_;
v___y_6230_ = v___y_6277_;
v___y_6231_ = v___x_6313_;
v___y_6232_ = v___y_6278_;
v_xType_x3f_6233_ = v___x_6326_;
v___y_6234_ = v___y_6279_;
v___y_6235_ = v___y_6280_;
v___y_6236_ = v___y_6281_;
v___y_6237_ = v___y_6282_;
v___y_6238_ = v___y_6283_;
v___y_6239_ = v___y_6284_;
v___y_6240_ = v___y_6285_;
goto v___jp_6227_;
}
}
}
else
{
lean_dec(v___x_6317_);
lean_inc(v___y_6272_);
v___y_6228_ = v___y_6273_;
v___y_6229_ = v___y_6274_;
v___y_6230_ = v___y_6277_;
v___y_6231_ = v___x_6313_;
v___y_6232_ = v___y_6278_;
v_xType_x3f_6233_ = v___y_6272_;
v___y_6234_ = v___y_6279_;
v___y_6235_ = v___y_6280_;
v___y_6236_ = v___y_6281_;
v___y_6237_ = v___y_6282_;
v___y_6238_ = v___y_6283_;
v___y_6239_ = v___y_6284_;
v___y_6240_ = v___y_6285_;
goto v___jp_6227_;
}
}
}
}
v___jp_6327_:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v_a_6348_; lean_object* v___x_6350_; uint8_t v_isShared_6351_; uint8_t v_isSharedCheck_6355_; 
lean_dec(v___y_6340_);
lean_dec(v___y_6337_);
lean_dec(v___y_6329_);
v___x_6346_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__1, &l_Lean_Elab_Do_elabDoLetArrow___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1);
v___x_6347_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v___y_6338_, v___x_6346_, v___y_6342_, v___y_6339_, v___y_6343_, v___y_6333_, v___y_6341_, v___y_6334_, v___y_6345_);
lean_dec(v___y_6338_);
v_a_6348_ = lean_ctor_get(v___x_6347_, 0);
v_isSharedCheck_6355_ = !lean_is_exclusive(v___x_6347_);
if (v_isSharedCheck_6355_ == 0)
{
v___x_6350_ = v___x_6347_;
v_isShared_6351_ = v_isSharedCheck_6355_;
goto v_resetjp_6349_;
}
else
{
lean_inc(v_a_6348_);
lean_dec(v___x_6347_);
v___x_6350_ = lean_box(0);
v_isShared_6351_ = v_isSharedCheck_6355_;
goto v_resetjp_6349_;
}
v_resetjp_6349_:
{
lean_object* v___x_6353_; 
if (v_isShared_6351_ == 0)
{
v___x_6353_ = v___x_6350_;
goto v_reusejp_6352_;
}
else
{
lean_object* v_reuseFailAlloc_6354_; 
v_reuseFailAlloc_6354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6354_, 0, v_a_6348_);
v___x_6353_ = v_reuseFailAlloc_6354_;
goto v_reusejp_6352_;
}
v_reusejp_6352_:
{
return v___x_6353_;
}
}
}
v___jp_6356_:
{
if (v___y_6376_ == 0)
{
lean_object* v_eq_x3f_6377_; 
v_eq_x3f_6377_ = lean_ctor_get(v___y_6375_, 0);
lean_inc(v_eq_x3f_6377_);
lean_dec_ref(v___y_6375_);
if (lean_obj_tag(v_eq_x3f_6377_) == 0)
{
lean_dec(v___y_6367_);
v___y_6269_ = v___y_6357_;
v___y_6270_ = v___y_6358_;
v___y_6271_ = v___y_6359_;
v___y_6272_ = v___y_6360_;
v___y_6273_ = v___y_6361_;
v___y_6274_ = v___y_6365_;
v___y_6275_ = v___y_6364_;
v___y_6276_ = v___y_6373_;
v___y_6277_ = v___y_6366_;
v___y_6278_ = v___y_6369_;
v___y_6279_ = v___y_6371_;
v___y_6280_ = v___y_6368_;
v___y_6281_ = v___y_6372_;
v___y_6282_ = v___y_6362_;
v___y_6283_ = v___y_6370_;
v___y_6284_ = v___y_6363_;
v___y_6285_ = v___y_6374_;
goto v___jp_6268_;
}
else
{
lean_dec_ref_known(v_eq_x3f_6377_, 1);
if (v___x_6015_ == 0)
{
lean_dec(v___y_6367_);
v___y_6269_ = v___y_6357_;
v___y_6270_ = v___y_6358_;
v___y_6271_ = v___y_6359_;
v___y_6272_ = v___y_6360_;
v___y_6273_ = v___y_6361_;
v___y_6274_ = v___y_6365_;
v___y_6275_ = v___y_6364_;
v___y_6276_ = v___y_6373_;
v___y_6277_ = v___y_6366_;
v___y_6278_ = v___y_6369_;
v___y_6279_ = v___y_6371_;
v___y_6280_ = v___y_6368_;
v___y_6281_ = v___y_6372_;
v___y_6282_ = v___y_6362_;
v___y_6283_ = v___y_6370_;
v___y_6284_ = v___y_6363_;
v___y_6285_ = v___y_6374_;
goto v___jp_6268_;
}
else
{
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v___y_6328_ = v___y_6357_;
v___y_6329_ = v___y_6358_;
v___y_6330_ = v___y_6359_;
v___y_6331_ = v___y_6360_;
v___y_6332_ = v___y_6361_;
v___y_6333_ = v___y_6362_;
v___y_6334_ = v___y_6363_;
v___y_6335_ = v___y_6364_;
v___y_6336_ = v___y_6365_;
v___y_6337_ = v___y_6366_;
v___y_6338_ = v___y_6367_;
v___y_6339_ = v___y_6368_;
v___y_6340_ = v___y_6369_;
v___y_6341_ = v___y_6370_;
v___y_6342_ = v___y_6371_;
v___y_6343_ = v___y_6372_;
v___y_6344_ = v___y_6373_;
v___y_6345_ = v___y_6374_;
goto v___jp_6327_;
}
}
}
else
{
lean_dec_ref(v___y_6375_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v___y_6328_ = v___y_6357_;
v___y_6329_ = v___y_6358_;
v___y_6330_ = v___y_6359_;
v___y_6331_ = v___y_6360_;
v___y_6332_ = v___y_6361_;
v___y_6333_ = v___y_6362_;
v___y_6334_ = v___y_6363_;
v___y_6335_ = v___y_6364_;
v___y_6336_ = v___y_6365_;
v___y_6337_ = v___y_6366_;
v___y_6338_ = v___y_6367_;
v___y_6339_ = v___y_6368_;
v___y_6340_ = v___y_6369_;
v___y_6341_ = v___y_6370_;
v___y_6342_ = v___y_6371_;
v___y_6343_ = v___y_6372_;
v___y_6344_ = v___y_6373_;
v___y_6345_ = v___y_6374_;
goto v___jp_6327_;
}
}
v___jp_6378_:
{
if (v___y_6398_ == 0)
{
uint8_t v_zeta_6399_; 
v_zeta_6399_ = lean_ctor_get_uint8(v___y_6397_, sizeof(void*)*1 + 2);
v___y_6357_ = v___y_6379_;
v___y_6358_ = v___y_6380_;
v___y_6359_ = v___y_6381_;
v___y_6360_ = v___y_6382_;
v___y_6361_ = v___y_6383_;
v___y_6362_ = v___y_6384_;
v___y_6363_ = v___y_6385_;
v___y_6364_ = v___y_6386_;
v___y_6365_ = v___y_6387_;
v___y_6366_ = v___y_6388_;
v___y_6367_ = v___y_6389_;
v___y_6368_ = v___y_6390_;
v___y_6369_ = v___y_6391_;
v___y_6370_ = v___y_6392_;
v___y_6371_ = v___y_6394_;
v___y_6372_ = v___y_6393_;
v___y_6373_ = v___y_6395_;
v___y_6374_ = v___y_6396_;
v___y_6375_ = v___y_6397_;
v___y_6376_ = v_zeta_6399_;
goto v___jp_6356_;
}
else
{
v___y_6357_ = v___y_6379_;
v___y_6358_ = v___y_6380_;
v___y_6359_ = v___y_6381_;
v___y_6360_ = v___y_6382_;
v___y_6361_ = v___y_6383_;
v___y_6362_ = v___y_6384_;
v___y_6363_ = v___y_6385_;
v___y_6364_ = v___y_6386_;
v___y_6365_ = v___y_6387_;
v___y_6366_ = v___y_6388_;
v___y_6367_ = v___y_6389_;
v___y_6368_ = v___y_6390_;
v___y_6369_ = v___y_6391_;
v___y_6370_ = v___y_6392_;
v___y_6371_ = v___y_6394_;
v___y_6372_ = v___y_6393_;
v___y_6373_ = v___y_6395_;
v___y_6374_ = v___y_6396_;
v___y_6375_ = v___y_6397_;
v___y_6376_ = v___x_6015_;
goto v___jp_6356_;
}
}
v___jp_6400_:
{
lean_object* v___x_6409_; lean_object* v_cfg_6410_; lean_object* v___x_6411_; uint8_t v___x_6412_; 
v___x_6409_ = lean_unsigned_to_nat(2u);
v_cfg_6410_ = l_Lean_Syntax_getArg(v_stx_6001_, v___x_6409_);
v___x_6411_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_6410_);
v___x_6412_ = l_Lean_Syntax_isOfKind(v_cfg_6410_, v___x_6411_);
if (v___x_6412_ == 0)
{
lean_object* v___x_6413_; 
lean_dec(v_cfg_6410_);
lean_dec(v_mutTk_x3f_6401_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
lean_dec(v_stx_6001_);
v___x_6413_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6413_;
}
else
{
lean_object* v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; uint8_t v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; 
v___x_6414_ = lean_unsigned_to_nat(3u);
v___x_6415_ = l_Lean_Syntax_getArg(v_stx_6001_, v___x_6414_);
lean_dec(v_stx_6001_);
v___x_6416_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
v___x_6417_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
v___x_6418_ = 0;
v___x_6419_ = lean_box(0);
v___x_6420_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
lean_inc(v_cfg_6410_);
v___x_6421_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_cfg_6410_, v_mutTk_x3f_6401_, v___x_6420_, v___y_6402_, v___y_6403_, v___y_6404_, v___y_6405_, v___y_6406_, v___y_6407_, v___y_6408_);
if (lean_obj_tag(v___x_6421_) == 0)
{
lean_object* v_a_6422_; lean_object* v___x_6423_; 
v_a_6422_ = lean_ctor_get(v___x_6421_, 0);
lean_inc(v_a_6422_);
lean_dec_ref_known(v___x_6421_, 1);
v___x_6423_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_6422_, v___y_6405_, v___y_6406_, v___y_6407_, v___y_6408_);
if (lean_obj_tag(v___x_6423_) == 0)
{
uint8_t v_nondep_6424_; 
lean_dec_ref_known(v___x_6423_, 1);
v_nondep_6424_ = lean_ctor_get_uint8(v_a_6422_, sizeof(void*)*1);
if (v_nondep_6424_ == 0)
{
uint8_t v_usedOnly_6425_; 
v_usedOnly_6425_ = lean_ctor_get_uint8(v_a_6422_, sizeof(void*)*1 + 1);
lean_inc(v_mutTk_x3f_6401_);
v___y_6379_ = v___x_6411_;
v___y_6380_ = v_mutTk_x3f_6401_;
v___y_6381_ = v___x_6409_;
v___y_6382_ = v___x_6419_;
v___y_6383_ = v___x_6418_;
v___y_6384_ = v___y_6405_;
v___y_6385_ = v___y_6407_;
v___y_6386_ = v___x_6417_;
v___y_6387_ = v___x_6414_;
v___y_6388_ = v_mutTk_x3f_6401_;
v___y_6389_ = v_cfg_6410_;
v___y_6390_ = v___y_6403_;
v___y_6391_ = v___x_6415_;
v___y_6392_ = v___y_6406_;
v___y_6393_ = v___y_6404_;
v___y_6394_ = v___y_6402_;
v___y_6395_ = v___x_6416_;
v___y_6396_ = v___y_6408_;
v___y_6397_ = v_a_6422_;
v___y_6398_ = v_usedOnly_6425_;
goto v___jp_6378_;
}
else
{
lean_inc(v_mutTk_x3f_6401_);
v___y_6379_ = v___x_6411_;
v___y_6380_ = v_mutTk_x3f_6401_;
v___y_6381_ = v___x_6409_;
v___y_6382_ = v___x_6419_;
v___y_6383_ = v___x_6418_;
v___y_6384_ = v___y_6405_;
v___y_6385_ = v___y_6407_;
v___y_6386_ = v___x_6417_;
v___y_6387_ = v___x_6414_;
v___y_6388_ = v_mutTk_x3f_6401_;
v___y_6389_ = v_cfg_6410_;
v___y_6390_ = v___y_6403_;
v___y_6391_ = v___x_6415_;
v___y_6392_ = v___y_6406_;
v___y_6393_ = v___y_6404_;
v___y_6394_ = v___y_6402_;
v___y_6395_ = v___x_6416_;
v___y_6396_ = v___y_6408_;
v___y_6397_ = v_a_6422_;
v___y_6398_ = v___x_6015_;
goto v___jp_6378_;
}
}
else
{
lean_object* v_a_6426_; lean_object* v___x_6428_; uint8_t v_isShared_6429_; uint8_t v_isSharedCheck_6433_; 
lean_dec(v_a_6422_);
lean_dec(v___x_6415_);
lean_dec(v_cfg_6410_);
lean_dec(v_mutTk_x3f_6401_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v_a_6426_ = lean_ctor_get(v___x_6423_, 0);
v_isSharedCheck_6433_ = !lean_is_exclusive(v___x_6423_);
if (v_isSharedCheck_6433_ == 0)
{
v___x_6428_ = v___x_6423_;
v_isShared_6429_ = v_isSharedCheck_6433_;
goto v_resetjp_6427_;
}
else
{
lean_inc(v_a_6426_);
lean_dec(v___x_6423_);
v___x_6428_ = lean_box(0);
v_isShared_6429_ = v_isSharedCheck_6433_;
goto v_resetjp_6427_;
}
v_resetjp_6427_:
{
lean_object* v___x_6431_; 
if (v_isShared_6429_ == 0)
{
v___x_6431_ = v___x_6428_;
goto v_reusejp_6430_;
}
else
{
lean_object* v_reuseFailAlloc_6432_; 
v_reuseFailAlloc_6432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6432_, 0, v_a_6426_);
v___x_6431_ = v_reuseFailAlloc_6432_;
goto v_reusejp_6430_;
}
v_reusejp_6430_:
{
return v___x_6431_;
}
}
}
}
else
{
lean_object* v_a_6434_; lean_object* v___x_6436_; uint8_t v_isShared_6437_; uint8_t v_isSharedCheck_6441_; 
lean_dec(v___x_6415_);
lean_dec(v_cfg_6410_);
lean_dec(v_mutTk_x3f_6401_);
lean_dec(v_tk_6126_);
lean_dec_ref(v_dec_6002_);
v_a_6434_ = lean_ctor_get(v___x_6421_, 0);
v_isSharedCheck_6441_ = !lean_is_exclusive(v___x_6421_);
if (v_isSharedCheck_6441_ == 0)
{
v___x_6436_ = v___x_6421_;
v_isShared_6437_ = v_isSharedCheck_6441_;
goto v_resetjp_6435_;
}
else
{
lean_inc(v_a_6434_);
lean_dec(v___x_6421_);
v___x_6436_ = lean_box(0);
v_isShared_6437_ = v_isSharedCheck_6441_;
goto v_resetjp_6435_;
}
v_resetjp_6435_:
{
lean_object* v___x_6439_; 
if (v_isShared_6437_ == 0)
{
v___x_6439_ = v___x_6436_;
goto v_reusejp_6438_;
}
else
{
lean_object* v_reuseFailAlloc_6440_; 
v_reuseFailAlloc_6440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6440_, 0, v_a_6434_);
v___x_6439_ = v_reuseFailAlloc_6440_;
goto v_reusejp_6438_;
}
v_reusejp_6438_:
{
return v___x_6439_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_6449_, lean_object* v_dec_6450_, lean_object* v_a_6451_, lean_object* v_a_6452_, lean_object* v_a_6453_, lean_object* v_a_6454_, lean_object* v_a_6455_, lean_object* v_a_6456_, lean_object* v_a_6457_, lean_object* v_a_6458_){
_start:
{
lean_object* v_res_6459_; 
v_res_6459_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_6449_, v_dec_6450_, v_a_6451_, v_a_6452_, v_a_6453_, v_a_6454_, v_a_6455_, v_a_6456_, v_a_6457_);
lean_dec(v_a_6457_);
lean_dec_ref(v_a_6456_);
lean_dec(v_a_6455_);
lean_dec_ref(v_a_6454_);
lean_dec(v_a_6453_);
lean_dec_ref(v_a_6452_);
lean_dec_ref(v_a_6451_);
return v_res_6459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; lean_object* v___x_6470_; lean_object* v___x_6471_; 
v___x_6467_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6468_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_6469_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_6470_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_6471_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6467_, v___x_6468_, v___x_6469_, v___x_6470_);
return v___x_6471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_6472_){
_start:
{
lean_object* v_res_6473_; 
v_res_6473_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_6473_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3(void){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; 
v___x_6481_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__2));
v___x_6482_ = l_Lean_stringToMessageData(v___x_6481_);
return v___x_6482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_6483_, lean_object* v_dec_6484_, lean_object* v_a_6485_, lean_object* v_a_6486_, lean_object* v_a_6487_, lean_object* v_a_6488_, lean_object* v_a_6489_, lean_object* v_a_6490_, lean_object* v_a_6491_){
_start:
{
lean_object* v___x_6493_; uint8_t v___x_6494_; 
v___x_6493_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_6483_);
v___x_6494_ = l_Lean_Syntax_isOfKind(v_stx_6483_, v___x_6493_);
if (v___x_6494_ == 0)
{
lean_object* v___x_6495_; 
lean_dec_ref(v_dec_6484_);
lean_dec(v_stx_6483_);
v___x_6495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6495_;
}
else
{
lean_object* v___x_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; uint8_t v___x_6499_; 
v___x_6496_ = lean_unsigned_to_nat(0u);
v___x_6497_ = l_Lean_Syntax_getArg(v_stx_6483_, v___x_6496_);
lean_dec(v_stx_6483_);
v___x_6498_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_6497_);
v___x_6499_ = l_Lean_Syntax_isOfKind(v___x_6497_, v___x_6498_);
if (v___x_6499_ == 0)
{
lean_object* v___x_6500_; uint8_t v___x_6501_; 
v___x_6500_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
lean_inc(v___x_6497_);
v___x_6501_ = l_Lean_Syntax_isOfKind(v___x_6497_, v___x_6500_);
if (v___x_6501_ == 0)
{
lean_object* v___x_6502_; 
lean_dec(v___x_6497_);
lean_dec_ref(v_dec_6484_);
v___x_6502_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6502_;
}
else
{
lean_object* v___x_6503_; lean_object* v___y_6505_; lean_object* v___y_6506_; lean_object* v___y_6507_; lean_object* v___y_6508_; lean_object* v___y_6509_; lean_object* v___y_6510_; lean_object* v___y_6511_; lean_object* v___y_6512_; lean_object* v___y_6513_; lean_object* v___y_6542_; lean_object* v___y_6543_; lean_object* v___y_6544_; lean_object* v___y_6545_; lean_object* v___y_6546_; lean_object* v___y_6547_; lean_object* v___y_6548_; lean_object* v___y_6549_; lean_object* v___y_6550_; uint8_t v___y_6551_; lean_object* v___y_6563_; lean_object* v___y_6564_; lean_object* v___y_6565_; lean_object* v___y_6566_; lean_object* v___y_6567_; lean_object* v___y_6568_; lean_object* v___y_6569_; lean_object* v___y_6570_; lean_object* v___y_6571_; lean_object* v___y_6572_; uint8_t v___y_6573_; lean_object* v___y_6576_; lean_object* v___y_6577_; lean_object* v___y_6578_; lean_object* v___y_6579_; lean_object* v___y_6580_; lean_object* v___y_6581_; lean_object* v___y_6582_; lean_object* v___y_6583_; lean_object* v___y_6584_; lean_object* v___y_6585_; lean_object* v___y_6586_; lean_object* v___x_6588_; lean_object* v_t_x3f_6590_; lean_object* v___y_6591_; lean_object* v___y_6592_; lean_object* v___y_6593_; lean_object* v___y_6594_; lean_object* v___y_6595_; lean_object* v___y_6596_; lean_object* v___y_6597_; lean_object* v___x_6619_; uint8_t v___x_6620_; 
v___x_6503_ = l_Lean_Syntax_getArg(v___x_6497_, v___x_6496_);
v___x_6588_ = lean_unsigned_to_nat(1u);
v___x_6619_ = l_Lean_Syntax_getArg(v___x_6497_, v___x_6588_);
v___x_6620_ = l_Lean_Syntax_isNone(v___x_6619_);
if (v___x_6620_ == 0)
{
uint8_t v___x_6621_; 
lean_inc(v___x_6619_);
v___x_6621_ = l_Lean_Syntax_matchesNull(v___x_6619_, v___x_6588_);
if (v___x_6621_ == 0)
{
lean_object* v___x_6622_; 
lean_dec(v___x_6619_);
lean_dec(v___x_6503_);
lean_dec(v___x_6497_);
lean_dec_ref(v_dec_6484_);
v___x_6622_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6622_;
}
else
{
lean_object* v___x_6623_; lean_object* v___x_6624_; uint8_t v___x_6625_; 
v___x_6623_ = l_Lean_Syntax_getArg(v___x_6619_, v___x_6496_);
lean_dec(v___x_6619_);
v___x_6624_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6623_);
v___x_6625_ = l_Lean_Syntax_isOfKind(v___x_6623_, v___x_6624_);
if (v___x_6625_ == 0)
{
lean_object* v___x_6626_; 
lean_dec(v___x_6623_);
lean_dec(v___x_6503_);
lean_dec(v___x_6497_);
lean_dec_ref(v_dec_6484_);
v___x_6626_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6626_;
}
else
{
lean_object* v_t_x3f_6627_; lean_object* v___x_6628_; 
v_t_x3f_6627_ = l_Lean_Syntax_getArg(v___x_6623_, v___x_6588_);
lean_dec(v___x_6623_);
v___x_6628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6628_, 0, v_t_x3f_6627_);
v_t_x3f_6590_ = v___x_6628_;
v___y_6591_ = v_a_6485_;
v___y_6592_ = v_a_6486_;
v___y_6593_ = v_a_6487_;
v___y_6594_ = v_a_6488_;
v___y_6595_ = v_a_6489_;
v___y_6596_ = v_a_6490_;
v___y_6597_ = v_a_6491_;
goto v___jp_6589_;
}
}
}
else
{
lean_object* v___x_6629_; 
lean_dec(v___x_6619_);
v___x_6629_ = lean_box(0);
v_t_x3f_6590_ = v___x_6629_;
v___y_6591_ = v_a_6485_;
v___y_6592_ = v_a_6486_;
v___y_6593_ = v_a_6487_;
v___y_6594_ = v_a_6488_;
v___y_6595_ = v_a_6489_;
v___y_6596_ = v_a_6490_;
v___y_6597_ = v_a_6491_;
goto v___jp_6589_;
}
v___jp_6504_:
{
lean_object* v___x_6514_; lean_object* v___x_6515_; 
v___x_6514_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6515_ = l_Lean_Core_mkFreshUserName(v___x_6514_, v___y_6512_, v___y_6513_);
if (lean_obj_tag(v___x_6515_) == 0)
{
lean_object* v_a_6516_; lean_object* v_ref_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; uint8_t v_kind_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; 
v_a_6516_ = lean_ctor_get(v___x_6515_, 0);
lean_inc(v_a_6516_);
lean_dec_ref_known(v___x_6515_, 1);
v_ref_6517_ = lean_ctor_get(v___y_6512_, 2);
v___x_6518_ = l_Lean_mkIdentFrom(v___x_6503_, v_a_6516_, v___x_6499_);
v___x_6519_ = l_Lean_SourceInfo_fromRef(v_ref_6517_, v___x_6499_);
v___x_6520_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6521_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
v___x_6522_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6523_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_6519_, 3);
v___x_6524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6524_, 0, v___x_6519_);
lean_ctor_set(v___x_6524_, 1, v___x_6522_);
lean_ctor_set(v___x_6524_, 2, v___x_6523_);
v___x_6525_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6526_, 0, v___x_6519_);
lean_ctor_set(v___x_6526_, 1, v___x_6525_);
lean_inc(v___x_6518_);
lean_inc_ref(v___x_6524_);
v___x_6527_ = l_Lean_Syntax_node5(v___x_6519_, v___x_6521_, v___x_6503_, v___x_6524_, v___x_6524_, v___x_6526_, v___x_6518_);
v_kind_6528_ = lean_ctor_get_uint8(v_dec_6484_, sizeof(void*)*3);
v___x_6529_ = l_Lean_Syntax_node1(v___x_6519_, v___x_6520_, v___x_6527_);
v___x_6530_ = lean_box(v___x_6494_);
v___x_6531_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6531_, 0, v___x_6529_);
lean_closure_set(v___x_6531_, 1, v_dec_6484_);
lean_closure_set(v___x_6531_, 2, v___x_6530_);
v___x_6532_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6518_, v___y_6506_, v___y_6505_, v___x_6531_, v_kind_6528_, v___y_6507_, v___y_6508_, v___y_6509_, v___y_6510_, v___y_6511_, v___y_6512_, v___y_6513_);
return v___x_6532_;
}
else
{
lean_object* v_a_6533_; lean_object* v___x_6535_; uint8_t v_isShared_6536_; uint8_t v_isSharedCheck_6540_; 
lean_dec(v___y_6506_);
lean_dec(v___y_6505_);
lean_dec(v___x_6503_);
lean_dec_ref(v_dec_6484_);
v_a_6533_ = lean_ctor_get(v___x_6515_, 0);
v_isSharedCheck_6540_ = !lean_is_exclusive(v___x_6515_);
if (v_isSharedCheck_6540_ == 0)
{
v___x_6535_ = v___x_6515_;
v_isShared_6536_ = v_isSharedCheck_6540_;
goto v_resetjp_6534_;
}
else
{
lean_inc(v_a_6533_);
lean_dec(v___x_6515_);
v___x_6535_ = lean_box(0);
v_isShared_6536_ = v_isSharedCheck_6540_;
goto v_resetjp_6534_;
}
v_resetjp_6534_:
{
lean_object* v___x_6538_; 
if (v_isShared_6536_ == 0)
{
v___x_6538_ = v___x_6535_;
goto v_reusejp_6537_;
}
else
{
lean_object* v_reuseFailAlloc_6539_; 
v_reuseFailAlloc_6539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6539_, 0, v_a_6533_);
v___x_6538_ = v_reuseFailAlloc_6539_;
goto v_reusejp_6537_;
}
v_reusejp_6537_:
{
return v___x_6538_;
}
}
}
}
v___jp_6541_:
{
if (v___y_6551_ == 0)
{
lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v_a_6554_; lean_object* v___x_6556_; uint8_t v_isShared_6557_; uint8_t v_isSharedCheck_6561_; 
lean_dec(v___y_6550_);
lean_dec(v___y_6543_);
lean_dec(v___x_6503_);
lean_dec_ref(v_dec_6484_);
v___x_6552_ = lean_obj_once(&l_Lean_Elab_Do_elabDoReassignArrow___closed__3, &l_Lean_Elab_Do_elabDoReassignArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3);
v___x_6553_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v___x_6552_, v___y_6542_, v___y_6549_, v___y_6548_, v___y_6547_);
v_a_6554_ = lean_ctor_get(v___x_6553_, 0);
v_isSharedCheck_6561_ = !lean_is_exclusive(v___x_6553_);
if (v_isSharedCheck_6561_ == 0)
{
v___x_6556_ = v___x_6553_;
v_isShared_6557_ = v_isSharedCheck_6561_;
goto v_resetjp_6555_;
}
else
{
lean_inc(v_a_6554_);
lean_dec(v___x_6553_);
v___x_6556_ = lean_box(0);
v_isShared_6557_ = v_isSharedCheck_6561_;
goto v_resetjp_6555_;
}
v_resetjp_6555_:
{
lean_object* v___x_6559_; 
if (v_isShared_6557_ == 0)
{
v___x_6559_ = v___x_6556_;
goto v_reusejp_6558_;
}
else
{
lean_object* v_reuseFailAlloc_6560_; 
v_reuseFailAlloc_6560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6560_, 0, v_a_6554_);
v___x_6559_ = v_reuseFailAlloc_6560_;
goto v_reusejp_6558_;
}
v_reusejp_6558_:
{
return v___x_6559_;
}
}
}
else
{
v___y_6505_ = v___y_6543_;
v___y_6506_ = v___y_6550_;
v___y_6507_ = v___y_6545_;
v___y_6508_ = v___y_6544_;
v___y_6509_ = v___y_6546_;
v___y_6510_ = v___y_6542_;
v___y_6511_ = v___y_6549_;
v___y_6512_ = v___y_6548_;
v___y_6513_ = v___y_6547_;
goto v___jp_6504_;
}
}
v___jp_6562_:
{
if (v___y_6573_ == 0)
{
lean_dec(v___y_6565_);
v___y_6542_ = v___y_6563_;
v___y_6543_ = v___y_6564_;
v___y_6544_ = v___y_6566_;
v___y_6545_ = v___y_6567_;
v___y_6546_ = v___y_6568_;
v___y_6547_ = v___y_6569_;
v___y_6548_ = v___y_6571_;
v___y_6549_ = v___y_6570_;
v___y_6550_ = v___y_6572_;
v___y_6551_ = v___x_6499_;
goto v___jp_6541_;
}
else
{
if (lean_obj_tag(v___y_6565_) == 0)
{
v___y_6542_ = v___y_6563_;
v___y_6543_ = v___y_6564_;
v___y_6544_ = v___y_6566_;
v___y_6545_ = v___y_6567_;
v___y_6546_ = v___y_6568_;
v___y_6547_ = v___y_6569_;
v___y_6548_ = v___y_6571_;
v___y_6549_ = v___y_6570_;
v___y_6550_ = v___y_6572_;
v___y_6551_ = v___x_6501_;
goto v___jp_6541_;
}
else
{
lean_object* v_val_6574_; 
v_val_6574_ = lean_ctor_get(v___y_6565_, 0);
lean_inc(v_val_6574_);
lean_dec_ref_known(v___y_6565_, 1);
if (lean_obj_tag(v_val_6574_) == 0)
{
v___y_6542_ = v___y_6563_;
v___y_6543_ = v___y_6564_;
v___y_6544_ = v___y_6566_;
v___y_6545_ = v___y_6567_;
v___y_6546_ = v___y_6568_;
v___y_6547_ = v___y_6569_;
v___y_6548_ = v___y_6571_;
v___y_6549_ = v___y_6570_;
v___y_6550_ = v___y_6572_;
v___y_6551_ = v___x_6501_;
goto v___jp_6541_;
}
else
{
lean_dec_ref_known(v_val_6574_, 1);
v___y_6542_ = v___y_6563_;
v___y_6543_ = v___y_6564_;
v___y_6544_ = v___y_6566_;
v___y_6545_ = v___y_6567_;
v___y_6546_ = v___y_6568_;
v___y_6547_ = v___y_6569_;
v___y_6548_ = v___y_6571_;
v___y_6549_ = v___y_6570_;
v___y_6550_ = v___y_6572_;
v___y_6551_ = v___x_6499_;
goto v___jp_6541_;
}
}
}
}
v___jp_6575_:
{
lean_object* v___x_6587_; 
lean_dec(v___y_6581_);
v___x_6587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6587_, 0, v___y_6586_);
v___y_6563_ = v___y_6584_;
v___y_6564_ = v___y_6577_;
v___y_6565_ = v___x_6587_;
v___y_6566_ = v___y_6579_;
v___y_6567_ = v___y_6580_;
v___y_6568_ = v___y_6576_;
v___y_6569_ = v___y_6585_;
v___y_6570_ = v___y_6578_;
v___y_6571_ = v___y_6583_;
v___y_6572_ = v___y_6582_;
v___y_6573_ = v___x_6499_;
goto v___jp_6562_;
}
v___jp_6589_:
{
lean_object* v___x_6598_; lean_object* v_rhs_6599_; lean_object* v___x_6600_; lean_object* v___x_6601_; uint8_t v___x_6602_; 
v___x_6598_ = lean_unsigned_to_nat(3u);
v_rhs_6599_ = l_Lean_Syntax_getArg(v___x_6497_, v___x_6598_);
v___x_6600_ = lean_unsigned_to_nat(4u);
v___x_6601_ = l_Lean_Syntax_getArg(v___x_6497_, v___x_6600_);
lean_dec(v___x_6497_);
v___x_6602_ = l_Lean_Syntax_isNone(v___x_6601_);
if (v___x_6602_ == 0)
{
uint8_t v___x_6603_; 
lean_inc(v___x_6601_);
v___x_6603_ = l_Lean_Syntax_matchesNull(v___x_6601_, v___x_6598_);
if (v___x_6603_ == 0)
{
lean_object* v___x_6604_; 
lean_dec(v___x_6601_);
lean_dec(v_rhs_6599_);
lean_dec(v_t_x3f_6590_);
lean_dec(v___x_6503_);
lean_dec_ref(v_dec_6484_);
v___x_6604_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6604_;
}
else
{
lean_object* v___x_6605_; lean_object* v_otherwise_x3f_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; 
v___x_6605_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_6606_ = l_Lean_Syntax_getArg(v___x_6601_, v___x_6588_);
v___x_6607_ = l_Lean_Syntax_getArg(v___x_6601_, v___x_6605_);
lean_dec(v___x_6601_);
v___x_6608_ = l_Lean_Syntax_getOptional_x3f(v___x_6607_);
lean_dec(v___x_6607_);
if (lean_obj_tag(v___x_6608_) == 0)
{
lean_object* v___x_6609_; 
v___x_6609_ = lean_box(0);
v___y_6576_ = v___y_6593_;
v___y_6577_ = v_rhs_6599_;
v___y_6578_ = v___y_6595_;
v___y_6579_ = v___y_6592_;
v___y_6580_ = v___y_6591_;
v___y_6581_ = v_otherwise_x3f_6606_;
v___y_6582_ = v_t_x3f_6590_;
v___y_6583_ = v___y_6596_;
v___y_6584_ = v___y_6594_;
v___y_6585_ = v___y_6597_;
v___y_6586_ = v___x_6609_;
goto v___jp_6575_;
}
else
{
lean_object* v_val_6610_; lean_object* v___x_6612_; uint8_t v_isShared_6613_; uint8_t v_isSharedCheck_6617_; 
v_val_6610_ = lean_ctor_get(v___x_6608_, 0);
v_isSharedCheck_6617_ = !lean_is_exclusive(v___x_6608_);
if (v_isSharedCheck_6617_ == 0)
{
v___x_6612_ = v___x_6608_;
v_isShared_6613_ = v_isSharedCheck_6617_;
goto v_resetjp_6611_;
}
else
{
lean_inc(v_val_6610_);
lean_dec(v___x_6608_);
v___x_6612_ = lean_box(0);
v_isShared_6613_ = v_isSharedCheck_6617_;
goto v_resetjp_6611_;
}
v_resetjp_6611_:
{
lean_object* v___x_6615_; 
if (v_isShared_6613_ == 0)
{
v___x_6615_ = v___x_6612_;
goto v_reusejp_6614_;
}
else
{
lean_object* v_reuseFailAlloc_6616_; 
v_reuseFailAlloc_6616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6616_, 0, v_val_6610_);
v___x_6615_ = v_reuseFailAlloc_6616_;
goto v_reusejp_6614_;
}
v_reusejp_6614_:
{
v___y_6576_ = v___y_6593_;
v___y_6577_ = v_rhs_6599_;
v___y_6578_ = v___y_6595_;
v___y_6579_ = v___y_6592_;
v___y_6580_ = v___y_6591_;
v___y_6581_ = v_otherwise_x3f_6606_;
v___y_6582_ = v_t_x3f_6590_;
v___y_6583_ = v___y_6596_;
v___y_6584_ = v___y_6594_;
v___y_6585_ = v___y_6597_;
v___y_6586_ = v___x_6615_;
goto v___jp_6575_;
}
}
}
}
}
else
{
lean_object* v___x_6618_; 
lean_dec(v___x_6601_);
v___x_6618_ = lean_box(0);
v___y_6563_ = v___y_6594_;
v___y_6564_ = v_rhs_6599_;
v___y_6565_ = v___x_6618_;
v___y_6566_ = v___y_6592_;
v___y_6567_ = v___y_6591_;
v___y_6568_ = v___y_6593_;
v___y_6569_ = v___y_6597_;
v___y_6570_ = v___y_6595_;
v___y_6571_ = v___y_6596_;
v___y_6572_ = v_t_x3f_6590_;
v___y_6573_ = v___x_6501_;
goto v___jp_6562_;
}
}
}
}
else
{
lean_object* v_x_6630_; lean_object* v___y_6632_; lean_object* v_t_6633_; lean_object* v___y_6634_; lean_object* v___y_6635_; lean_object* v___y_6636_; lean_object* v___y_6637_; lean_object* v___y_6638_; lean_object* v___y_6639_; lean_object* v___y_6640_; lean_object* v_t_x3f_6673_; lean_object* v___y_6674_; lean_object* v___y_6675_; lean_object* v___y_6676_; lean_object* v___y_6677_; lean_object* v___y_6678_; lean_object* v___y_6679_; lean_object* v___y_6680_; lean_object* v___x_6715_; uint8_t v___x_6716_; 
v_x_6630_ = l_Lean_Syntax_getArg(v___x_6497_, v___x_6496_);
v___x_6715_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_6630_);
v___x_6716_ = l_Lean_Syntax_isOfKind(v_x_6630_, v___x_6715_);
if (v___x_6716_ == 0)
{
lean_object* v___x_6717_; 
lean_dec(v_x_6630_);
lean_dec(v___x_6497_);
lean_dec_ref(v_dec_6484_);
v___x_6717_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6717_;
}
else
{
lean_object* v___x_6718_; lean_object* v___x_6719_; uint8_t v___x_6720_; 
v___x_6718_ = lean_unsigned_to_nat(1u);
v___x_6719_ = l_Lean_Syntax_getArg(v___x_6497_, v___x_6718_);
v___x_6720_ = l_Lean_Syntax_isNone(v___x_6719_);
if (v___x_6720_ == 0)
{
uint8_t v___x_6721_; 
lean_inc(v___x_6719_);
v___x_6721_ = l_Lean_Syntax_matchesNull(v___x_6719_, v___x_6718_);
if (v___x_6721_ == 0)
{
lean_object* v___x_6722_; 
lean_dec(v___x_6719_);
lean_dec(v_x_6630_);
lean_dec(v___x_6497_);
lean_dec_ref(v_dec_6484_);
v___x_6722_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6722_;
}
else
{
lean_object* v___x_6723_; lean_object* v___x_6724_; uint8_t v___x_6725_; 
v___x_6723_ = l_Lean_Syntax_getArg(v___x_6719_, v___x_6496_);
lean_dec(v___x_6719_);
v___x_6724_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6723_);
v___x_6725_ = l_Lean_Syntax_isOfKind(v___x_6723_, v___x_6724_);
if (v___x_6725_ == 0)
{
lean_object* v___x_6726_; 
lean_dec(v___x_6723_);
lean_dec(v_x_6630_);
lean_dec(v___x_6497_);
lean_dec_ref(v_dec_6484_);
v___x_6726_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6726_;
}
else
{
lean_object* v_t_x3f_6727_; lean_object* v___x_6728_; 
v_t_x3f_6727_ = l_Lean_Syntax_getArg(v___x_6723_, v___x_6718_);
lean_dec(v___x_6723_);
v___x_6728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6728_, 0, v_t_x3f_6727_);
v_t_x3f_6673_ = v___x_6728_;
v___y_6674_ = v_a_6485_;
v___y_6675_ = v_a_6486_;
v___y_6676_ = v_a_6487_;
v___y_6677_ = v_a_6488_;
v___y_6678_ = v_a_6489_;
v___y_6679_ = v_a_6490_;
v___y_6680_ = v_a_6491_;
goto v___jp_6672_;
}
}
}
else
{
lean_object* v___x_6729_; 
lean_dec(v___x_6719_);
v___x_6729_ = lean_box(0);
v_t_x3f_6673_ = v___x_6729_;
v___y_6674_ = v_a_6485_;
v___y_6675_ = v_a_6486_;
v___y_6676_ = v_a_6487_;
v___y_6677_ = v_a_6488_;
v___y_6678_ = v_a_6489_;
v___y_6679_ = v_a_6490_;
v___y_6680_ = v_a_6491_;
goto v___jp_6672_;
}
}
v___jp_6631_:
{
lean_object* v___x_6641_; lean_object* v___x_6642_; 
v___x_6641_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6642_ = l_Lean_Core_mkFreshUserName(v___x_6641_, v___y_6639_, v___y_6640_);
if (lean_obj_tag(v___x_6642_) == 0)
{
lean_object* v_a_6643_; lean_object* v_ref_6644_; uint8_t v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; uint8_t v_kind_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; lean_object* v___x_6663_; 
v_a_6643_ = lean_ctor_get(v___x_6642_, 0);
lean_inc(v_a_6643_);
lean_dec_ref_known(v___x_6642_, 1);
v_ref_6644_ = lean_ctor_get(v___y_6639_, 2);
v___x_6645_ = 0;
v___x_6646_ = l_Lean_mkIdentFrom(v_x_6630_, v_a_6643_, v___x_6645_);
v___x_6647_ = l_Lean_SourceInfo_fromRef(v_ref_6644_, v___x_6645_);
v___x_6648_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6649_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_6650_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v___x_6647_, 4);
v___x_6651_ = l_Lean_Syntax_node1(v___x_6647_, v___x_6650_, v_x_6630_);
v___x_6652_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6653_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_6654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6654_, 0, v___x_6647_);
lean_ctor_set(v___x_6654_, 1, v___x_6652_);
lean_ctor_set(v___x_6654_, 2, v___x_6653_);
v___x_6655_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6656_, 0, v___x_6647_);
lean_ctor_set(v___x_6656_, 1, v___x_6655_);
lean_inc(v___x_6646_);
lean_inc_ref(v___x_6654_);
v___x_6657_ = l_Lean_Syntax_node5(v___x_6647_, v___x_6649_, v___x_6651_, v___x_6654_, v___x_6654_, v___x_6656_, v___x_6646_);
v_kind_6658_ = lean_ctor_get_uint8(v_dec_6484_, sizeof(void*)*3);
v___x_6659_ = l_Lean_Syntax_node1(v___x_6647_, v___x_6648_, v___x_6657_);
v___x_6660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6660_, 0, v_t_6633_);
v___x_6661_ = lean_box(v___x_6494_);
v___x_6662_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6662_, 0, v___x_6659_);
lean_closure_set(v___x_6662_, 1, v_dec_6484_);
lean_closure_set(v___x_6662_, 2, v___x_6661_);
v___x_6663_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6646_, v___x_6660_, v___y_6632_, v___x_6662_, v_kind_6658_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
return v___x_6663_;
}
else
{
lean_object* v_a_6664_; lean_object* v___x_6666_; uint8_t v_isShared_6667_; uint8_t v_isSharedCheck_6671_; 
lean_dec(v_t_6633_);
lean_dec(v___y_6632_);
lean_dec(v_x_6630_);
lean_dec_ref(v_dec_6484_);
v_a_6664_ = lean_ctor_get(v___x_6642_, 0);
v_isSharedCheck_6671_ = !lean_is_exclusive(v___x_6642_);
if (v_isSharedCheck_6671_ == 0)
{
v___x_6666_ = v___x_6642_;
v_isShared_6667_ = v_isSharedCheck_6671_;
goto v_resetjp_6665_;
}
else
{
lean_inc(v_a_6664_);
lean_dec(v___x_6642_);
v___x_6666_ = lean_box(0);
v_isShared_6667_ = v_isSharedCheck_6671_;
goto v_resetjp_6665_;
}
v_resetjp_6665_:
{
lean_object* v___x_6669_; 
if (v_isShared_6667_ == 0)
{
v___x_6669_ = v___x_6666_;
goto v_reusejp_6668_;
}
else
{
lean_object* v_reuseFailAlloc_6670_; 
v_reuseFailAlloc_6670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6670_, 0, v_a_6664_);
v___x_6669_ = v_reuseFailAlloc_6670_;
goto v_reusejp_6668_;
}
v_reusejp_6668_:
{
return v___x_6669_;
}
}
}
}
v___jp_6672_:
{
lean_object* v___x_6681_; lean_object* v_rhs_6682_; lean_object* v___x_6683_; 
v___x_6681_ = lean_unsigned_to_nat(3u);
v_rhs_6682_ = l_Lean_Syntax_getArg(v___x_6497_, v___x_6681_);
lean_dec(v___x_6497_);
v___x_6683_ = l_Lean_Elab_Do_throwUnlessMutVarDeclared(v_x_6630_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_, v___y_6678_, v___y_6679_, v___y_6680_);
if (lean_obj_tag(v___x_6683_) == 0)
{
lean_dec_ref_known(v___x_6683_, 1);
if (lean_obj_tag(v_t_x3f_6673_) == 0)
{
lean_object* v___x_6684_; lean_object* v___x_6685_; 
v___x_6684_ = l_Lean_TSyntax_getId(v_x_6630_);
v___x_6685_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_6684_, v___y_6677_, v___y_6678_, v___y_6679_, v___y_6680_);
if (lean_obj_tag(v___x_6685_) == 0)
{
lean_object* v_a_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; 
v_a_6686_ = lean_ctor_get(v___x_6685_, 0);
lean_inc(v_a_6686_);
lean_dec_ref_known(v___x_6685_, 1);
v___x_6687_ = l_Lean_LocalDecl_type(v_a_6686_);
lean_dec(v_a_6686_);
v___x_6688_ = l_Lean_Elab_Term_exprToSyntax(v___x_6687_, v___y_6675_, v___y_6676_, v___y_6677_, v___y_6678_, v___y_6679_, v___y_6680_);
if (lean_obj_tag(v___x_6688_) == 0)
{
lean_object* v_a_6689_; 
v_a_6689_ = lean_ctor_get(v___x_6688_, 0);
lean_inc(v_a_6689_);
lean_dec_ref_known(v___x_6688_, 1);
v___y_6632_ = v_rhs_6682_;
v_t_6633_ = v_a_6689_;
v___y_6634_ = v___y_6674_;
v___y_6635_ = v___y_6675_;
v___y_6636_ = v___y_6676_;
v___y_6637_ = v___y_6677_;
v___y_6638_ = v___y_6678_;
v___y_6639_ = v___y_6679_;
v___y_6640_ = v___y_6680_;
goto v___jp_6631_;
}
else
{
lean_object* v_a_6690_; lean_object* v___x_6692_; uint8_t v_isShared_6693_; uint8_t v_isSharedCheck_6697_; 
lean_dec(v_rhs_6682_);
lean_dec(v_x_6630_);
lean_dec_ref(v_dec_6484_);
v_a_6690_ = lean_ctor_get(v___x_6688_, 0);
v_isSharedCheck_6697_ = !lean_is_exclusive(v___x_6688_);
if (v_isSharedCheck_6697_ == 0)
{
v___x_6692_ = v___x_6688_;
v_isShared_6693_ = v_isSharedCheck_6697_;
goto v_resetjp_6691_;
}
else
{
lean_inc(v_a_6690_);
lean_dec(v___x_6688_);
v___x_6692_ = lean_box(0);
v_isShared_6693_ = v_isSharedCheck_6697_;
goto v_resetjp_6691_;
}
v_resetjp_6691_:
{
lean_object* v___x_6695_; 
if (v_isShared_6693_ == 0)
{
v___x_6695_ = v___x_6692_;
goto v_reusejp_6694_;
}
else
{
lean_object* v_reuseFailAlloc_6696_; 
v_reuseFailAlloc_6696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6696_, 0, v_a_6690_);
v___x_6695_ = v_reuseFailAlloc_6696_;
goto v_reusejp_6694_;
}
v_reusejp_6694_:
{
return v___x_6695_;
}
}
}
}
else
{
lean_object* v_a_6698_; lean_object* v___x_6700_; uint8_t v_isShared_6701_; uint8_t v_isSharedCheck_6705_; 
lean_dec(v_rhs_6682_);
lean_dec(v_x_6630_);
lean_dec_ref(v_dec_6484_);
v_a_6698_ = lean_ctor_get(v___x_6685_, 0);
v_isSharedCheck_6705_ = !lean_is_exclusive(v___x_6685_);
if (v_isSharedCheck_6705_ == 0)
{
v___x_6700_ = v___x_6685_;
v_isShared_6701_ = v_isSharedCheck_6705_;
goto v_resetjp_6699_;
}
else
{
lean_inc(v_a_6698_);
lean_dec(v___x_6685_);
v___x_6700_ = lean_box(0);
v_isShared_6701_ = v_isSharedCheck_6705_;
goto v_resetjp_6699_;
}
v_resetjp_6699_:
{
lean_object* v___x_6703_; 
if (v_isShared_6701_ == 0)
{
v___x_6703_ = v___x_6700_;
goto v_reusejp_6702_;
}
else
{
lean_object* v_reuseFailAlloc_6704_; 
v_reuseFailAlloc_6704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6704_, 0, v_a_6698_);
v___x_6703_ = v_reuseFailAlloc_6704_;
goto v_reusejp_6702_;
}
v_reusejp_6702_:
{
return v___x_6703_;
}
}
}
}
else
{
lean_object* v_val_6706_; 
v_val_6706_ = lean_ctor_get(v_t_x3f_6673_, 0);
lean_inc(v_val_6706_);
lean_dec_ref_known(v_t_x3f_6673_, 1);
v___y_6632_ = v_rhs_6682_;
v_t_6633_ = v_val_6706_;
v___y_6634_ = v___y_6674_;
v___y_6635_ = v___y_6675_;
v___y_6636_ = v___y_6676_;
v___y_6637_ = v___y_6677_;
v___y_6638_ = v___y_6678_;
v___y_6639_ = v___y_6679_;
v___y_6640_ = v___y_6680_;
goto v___jp_6631_;
}
}
else
{
lean_object* v_a_6707_; lean_object* v___x_6709_; uint8_t v_isShared_6710_; uint8_t v_isSharedCheck_6714_; 
lean_dec(v_rhs_6682_);
lean_dec(v_t_x3f_6673_);
lean_dec(v_x_6630_);
lean_dec_ref(v_dec_6484_);
v_a_6707_ = lean_ctor_get(v___x_6683_, 0);
v_isSharedCheck_6714_ = !lean_is_exclusive(v___x_6683_);
if (v_isSharedCheck_6714_ == 0)
{
v___x_6709_ = v___x_6683_;
v_isShared_6710_ = v_isSharedCheck_6714_;
goto v_resetjp_6708_;
}
else
{
lean_inc(v_a_6707_);
lean_dec(v___x_6683_);
v___x_6709_ = lean_box(0);
v_isShared_6710_ = v_isSharedCheck_6714_;
goto v_resetjp_6708_;
}
v_resetjp_6708_:
{
lean_object* v___x_6712_; 
if (v_isShared_6710_ == 0)
{
v___x_6712_ = v___x_6709_;
goto v_reusejp_6711_;
}
else
{
lean_object* v_reuseFailAlloc_6713_; 
v_reuseFailAlloc_6713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6713_, 0, v_a_6707_);
v___x_6712_ = v_reuseFailAlloc_6713_;
goto v_reusejp_6711_;
}
v_reusejp_6711_:
{
return v___x_6712_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_6730_, lean_object* v_dec_6731_, lean_object* v_a_6732_, lean_object* v_a_6733_, lean_object* v_a_6734_, lean_object* v_a_6735_, lean_object* v_a_6736_, lean_object* v_a_6737_, lean_object* v_a_6738_, lean_object* v_a_6739_){
_start:
{
lean_object* v_res_6740_; 
v_res_6740_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_6730_, v_dec_6731_, v_a_6732_, v_a_6733_, v_a_6734_, v_a_6735_, v_a_6736_, v_a_6737_, v_a_6738_);
lean_dec(v_a_6738_);
lean_dec_ref(v_a_6737_);
lean_dec(v_a_6736_);
lean_dec_ref(v_a_6735_);
lean_dec(v_a_6734_);
lean_dec_ref(v_a_6733_);
lean_dec_ref(v_a_6732_);
return v_res_6740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_6748_; lean_object* v___x_6749_; lean_object* v___x_6750_; lean_object* v___x_6751_; lean_object* v___x_6752_; 
v___x_6748_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6749_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_6750_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_6751_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_6752_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6748_, v___x_6749_, v___x_6750_, v___x_6751_);
return v___x_6752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_6753_){
_start:
{
lean_object* v_res_6754_; 
v_res_6754_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_6754_;
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
