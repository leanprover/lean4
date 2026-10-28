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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toCold_186_; lean_object* v_currRecDepth_187_; lean_object* v_ref_188_; uint16_t v_optionFlags_189_; uint8_t v_suppressElabErrors_190_; uint8_t v_checkDeprecated_191_; uint8_t v_isRecordingDeps_192_; lean_object* v_ref_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_toCold_186_ = lean_ctor_get(v___y_183_, 0);
v_currRecDepth_187_ = lean_ctor_get(v___y_183_, 1);
v_ref_188_ = lean_ctor_get(v___y_183_, 2);
v_optionFlags_189_ = lean_ctor_get_uint16(v___y_183_, sizeof(void*)*3);
v_suppressElabErrors_190_ = lean_ctor_get_uint8(v___y_183_, sizeof(void*)*3 + 2);
v_checkDeprecated_191_ = lean_ctor_get_uint8(v___y_183_, sizeof(void*)*3 + 3);
v_isRecordingDeps_192_ = lean_ctor_get_uint8(v___y_183_, sizeof(void*)*3 + 4);
v_ref_193_ = l_Lean_replaceRef(v_ref_176_, v_ref_188_);
lean_inc(v_currRecDepth_187_);
lean_inc_ref(v_toCold_186_);
v___x_194_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_194_, 0, v_toCold_186_);
lean_ctor_set(v___x_194_, 1, v_currRecDepth_187_);
lean_ctor_set(v___x_194_, 2, v_ref_193_);
lean_ctor_set_uint16(v___x_194_, sizeof(void*)*3, v_optionFlags_189_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*3 + 2, v_suppressElabErrors_190_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*3 + 3, v_checkDeprecated_191_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*3 + 4, v_isRecordingDeps_192_);
v___x_195_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v_msg_177_, v___y_181_, v___y_182_, v___x_194_, v___y_184_);
lean_dec_ref_known(v___x_194_, 3);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg___boxed(lean_object* v_ref_196_, lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_ref_196_, v_msg_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v_ref_196_);
return v_res_206_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__0));
v___x_209_ = l_Lean_stringToMessageData(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__2));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(lean_object* v_as_213_, size_t v_sz_214_, size_t v_i_215_, lean_object* v_b_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_a_226_; uint8_t v___x_230_; 
v___x_230_ = lean_usize_dec_lt(v_i_215_, v_sz_214_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_b_216_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v_a_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_232_ = lean_box(0);
v_a_233_ = lean_array_uget_borrowed(v_as_213_, v_i_215_);
v___x_234_ = l_Lean_TSyntax_getId(v_a_233_);
v___x_235_ = l_Lean_Elab_Do_findMutVar_x3f___redArg(v___x_234_, v___y_217_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
if (lean_obj_tag(v_a_236_) == 0)
{
lean_dec(v___x_234_);
v_a_226_ = v___x_232_;
goto v___jp_225_;
}
else
{
lean_object* v_val_237_; uint8_t v_erased_238_; 
v_val_237_ = lean_ctor_get(v_a_236_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v_a_236_, 1);
v_erased_238_ = lean_ctor_get_uint8(v_val_237_, sizeof(void*)*2);
lean_dec(v_val_237_);
if (v_erased_238_ == 0)
{
lean_dec(v___x_234_);
v_a_226_ = v___x_232_;
goto v___jp_225_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_239_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1);
v___x_240_ = l_Lean_MessageData_ofName(v___x_234_);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_a_233_, v___x_243_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_dec_ref_known(v___x_244_, 1);
v_a_226_ = v___x_232_;
goto v___jp_225_;
}
else
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec(v___x_234_);
v_a_245_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_235_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_235_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
v___jp_225_:
{
size_t v___x_227_; size_t v___x_228_; 
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_add(v_i_215_, v___x_227_);
v_i_215_ = v___x_228_;
v_b_216_ = v_a_226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___boxed(lean_object* v_as_253_, lean_object* v_sz_254_, lean_object* v_i_255_, lean_object* v_b_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
size_t v_sz_boxed_265_; size_t v_i_boxed_266_; lean_object* v_res_267_; 
v_sz_boxed_265_ = lean_unbox_usize(v_sz_254_);
lean_dec(v_sz_254_);
v_i_boxed_266_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(v_as_253_, v_sz_boxed_265_, v_i_boxed_266_, v_b_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec_ref(v_as_253_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars(lean_object* v_letOrReassign_268_, lean_object* v_vars_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
if (lean_obj_tag(v_letOrReassign_268_) == 2)
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Elab_Do_throwUnlessMutVarsDeclared(v_vars_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_301_; 
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v___x_278_, 0);
lean_dec(v_unused_302_);
v___x_280_ = v___x_278_;
v_isShared_281_ = v_isSharedCheck_301_;
goto v_resetjp_279_;
}
else
{
lean_dec(v___x_278_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_301_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_282_ = lean_array_get_size(v_vars_269_);
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_dec_eq(v___x_282_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; size_t v_sz_286_; size_t v___x_287_; lean_object* v___x_288_; 
lean_del_object(v___x_280_);
v___x_285_ = lean_box(0);
v_sz_286_ = lean_array_size(v_vars_269_);
v___x_287_ = ((size_t)0ULL);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(v_vars_269_, v_sz_286_, v___x_287_, v___x_285_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_288_, 0);
lean_dec(v_unused_296_);
v___x_290_ = v___x_288_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_dec(v___x_288_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_285_);
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_285_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
return v___x_288_;
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_297_);
v___x_299_ = v___x_280_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
return v___x_278_;
}
}
else
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v_vars_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars___boxed(lean_object* v_letOrReassign_304_, lean_object* v_vars_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_304_, v_vars_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_vars_305_);
lean_dec(v_letOrReassign_304_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0(lean_object* v_00_u03b1_315_, lean_object* v_ref_316_, lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_ref_316_, v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___boxed(lean_object* v_00_u03b1_327_, lean_object* v_ref_328_, lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0(v_00_u03b1_327_, v_ref_328_, v_msg_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v_ref_328_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0(lean_object* v_00_u03b1_339_, lean_object* v_msg_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v_msg_340_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_350_, lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0(v_00_u03b1_350_, v_msg_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object* v_as_361_, size_t v_sz_362_, size_t v_i_363_, lean_object* v_b_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_lt(v_i_363_, v_sz_362_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_b_364_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; lean_object* v_a_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_375_ = lean_box(0);
v_a_376_ = lean_array_uget_borrowed(v_as_361_, v_i_363_);
v___x_377_ = l_Lean_TSyntax_getId(v_a_376_);
v___x_378_ = l_Lean_Elab_Do_registerMutVarAlias(v___x_377_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_378_) == 0)
{
size_t v___x_379_; size_t v___x_380_; 
lean_dec_ref_known(v___x_378_, 1);
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_363_, v___x_379_);
v_i_363_ = v___x_380_;
v_b_364_ = v___x_375_;
goto _start;
}
else
{
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object* v_as_382_, lean_object* v_sz_383_, lean_object* v_i_384_, lean_object* v_b_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
size_t v_sz_boxed_394_; size_t v_i_boxed_395_; lean_object* v_res_396_; 
v_sz_boxed_394_ = lean_unbox_usize(v_sz_383_);
lean_dec(v_sz_383_);
v_i_boxed_395_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_as_382_, v_sz_boxed_394_, v_i_boxed_395_, v_b_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec_ref(v_as_382_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object* v_letOrReassign_397_, lean_object* v_vars_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
if (lean_obj_tag(v_letOrReassign_397_) == 2)
{
lean_object* v___x_407_; size_t v_sz_408_; size_t v___x_409_; lean_object* v___x_410_; 
v___x_407_ = lean_box(0);
v_sz_408_ = lean_array_size(v_vars_398_);
v___x_409_ = ((size_t)0ULL);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_vars_398_, v_sz_408_, v___x_409_, v___x_407_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; 
v_unused_418_ = lean_ctor_get(v___x_410_, 0);
lean_dec(v_unused_418_);
v___x_412_ = v___x_410_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_dec(v___x_410_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_407_);
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_407_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
else
{
return v___x_410_;
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_box(0);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object* v_letOrReassign_421_, lean_object* v_vars_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_421_, v_vars_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_vars_422_);
lean_dec(v_letOrReassign_421_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0(lean_object* v___x_432_, lean_object* v_b_433_, uint8_t v_a_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Elab_Do_withErasedProj(v___x_432_, v_b_433_, v_a_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0___boxed(lean_object* v___x_444_, lean_object* v_b_445_, lean_object* v_a_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
uint8_t v_a_720__boxed_455_; lean_object* v_res_456_; 
v_a_720__boxed_455_ = lean_unbox(v_a_446_);
v_res_456_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0(v___x_444_, v_b_445_, v_a_720__boxed_455_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(uint8_t v_a_457_, lean_object* v_as_458_, size_t v_i_459_, size_t v_stop_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = lean_usize_dec_eq(v_i_459_, v_stop_460_);
if (v___x_470_ == 0)
{
size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___f_475_; 
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_sub(v_i_459_, v___x_471_);
v___x_473_ = lean_array_uget_borrowed(v_as_458_, v___x_472_);
v___x_474_ = lean_box(v_a_457_);
lean_inc(v___x_473_);
v___f_475_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0___boxed), 11, 3);
lean_closure_set(v___f_475_, 0, v___x_473_);
lean_closure_set(v___f_475_, 1, v_b_461_);
lean_closure_set(v___f_475_, 2, v___x_474_);
v_i_459_ = v___x_472_;
v_b_461_ = v___f_475_;
goto _start;
}
else
{
lean_object* v___x_477_; 
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc_ref(v___y_462_);
v___x_477_ = lean_apply_8(v_b_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, lean_box(0));
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___boxed(lean_object* v_a_478_, lean_object* v_as_479_, lean_object* v_i_480_, lean_object* v_stop_481_, lean_object* v_b_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
uint8_t v_a_751__boxed_491_; size_t v_i_boxed_492_; size_t v_stop_boxed_493_; lean_object* v_res_494_; 
v_a_751__boxed_491_ = lean_unbox(v_a_478_);
v_i_boxed_492_ = lean_unbox_usize(v_i_480_);
lean_dec(v_i_480_);
v_stop_boxed_493_ = lean_unbox_usize(v_stop_481_);
lean_dec(v_stop_481_);
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(v_a_751__boxed_491_, v_as_479_, v_i_boxed_492_, v_stop_boxed_493_, v_b_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v_as_479_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___lam__0(lean_object* v_letOrReassign_495_, lean_object* v_vars_496_, lean_object* v_k_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_495_, v_vars_496_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_507_; 
lean_dec_ref_known(v___x_506_, 1);
v___x_507_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_495_, v_vars_496_, v___y_498_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; uint8_t v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = lean_unbox(v_a_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_dec(v_a_508_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc_ref(v___y_498_);
v___x_510_ = lean_apply_8(v_k_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, lean_box(0));
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_511_ = lean_array_get_size(v_vars_496_);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_nat_dec_lt(v___x_512_, v___x_511_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v_a_508_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc_ref(v___y_498_);
v___x_514_ = lean_apply_8(v_k_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, lean_box(0));
return v___x_514_;
}
else
{
size_t v___x_515_; size_t v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; 
v___x_515_ = lean_usize_of_nat(v___x_511_);
v___x_516_ = ((size_t)0ULL);
v___x_517_ = lean_unbox(v_a_508_);
lean_dec(v_a_508_);
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(v___x_517_, v_vars_496_, v___x_515_, v___x_516_, v_k_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_518_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec_ref(v_k_497_);
v_a_519_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_507_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_507_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v_k_497_);
v_a_527_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_506_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_506_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___lam__0___boxed(lean_object* v_letOrReassign_535_, lean_object* v_vars_536_, lean_object* v_k_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Elab_Do_elabWithReassignments___lam__0(v_letOrReassign_535_, v_vars_536_, v_k_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_vars_536_);
lean_dec(v_letOrReassign_535_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments(lean_object* v_letOrReassign_547_, lean_object* v_vars_548_, lean_object* v_k_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___f_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
lean_inc_ref(v_vars_548_);
lean_inc(v_letOrReassign_547_);
v___f_558_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___lam__0___boxed), 11, 3);
lean_closure_set(v___f_558_, 0, v_letOrReassign_547_);
lean_closure_set(v___f_558_, 1, v_vars_548_);
lean_closure_set(v___f_558_, 2, v_k_549_);
v___x_559_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_547_);
v___x_560_ = l_Lean_Elab_Do_LetOrReassign_isErasedDecl(v_letOrReassign_547_);
lean_dec(v_letOrReassign_547_);
v___x_561_ = l_Lean_Elab_Do_declareMutVars_x3f___redArg(v___x_559_, v_vars_548_, v___x_560_, v___f_558_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
lean_dec(v___x_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___boxed(lean_object* v_letOrReassign_562_, lean_object* v_vars_563_, lean_object* v_k_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_562_, v_vars_563_, v_k_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(lean_object* v_a_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg___boxed(lean_object* v_a_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(v_a_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(lean_object* v_00_u03b1_592_, lean_object* v_a_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___boxed(lean_object* v_00_u03b1_602_, lean_object* v_a_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(v_00_u03b1_602_, v_a_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_611_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_box(1);
v___x_613_ = l_Lean_MessageData_ofFormat(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__2));
v___x_618_ = l_Lean_MessageData_ofFormat(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3(lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
return v_x_619_;
}
else
{
lean_object* v_head_621_; lean_object* v_tail_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_644_; 
v_head_621_ = lean_ctor_get(v_x_620_, 0);
v_tail_622_ = lean_ctor_get(v_x_620_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_644_ == 0)
{
v___x_624_ = v_x_620_;
v_isShared_625_ = v_isSharedCheck_644_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_tail_622_);
lean_inc(v_head_621_);
lean_dec(v_x_620_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_644_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_before_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_642_; 
v_before_626_ = lean_ctor_get(v_head_621_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_head_621_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v_head_621_, 1);
lean_dec(v_unused_643_);
v___x_628_ = v_head_621_;
v_isShared_629_ = v_isSharedCheck_642_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_before_626_);
lean_dec(v_head_621_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_642_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 7);
lean_ctor_set(v___x_628_, 1, v___x_630_);
lean_ctor_set(v___x_628_, 0, v_x_619_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_x_619_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_641_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 7);
lean_ctor_set(v___x_624_, 1, v___x_633_);
lean_ctor_set(v___x_624_, 0, v___x_632_);
v___x_635_ = v___x_624_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_633_);
v___x_635_ = v_reuseFailAlloc_640_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = l_Lean_MessageData_ofSyntax(v_before_626_);
v___x_637_ = l_Lean_indentD(v___x_636_);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_635_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v_x_619_ = v___x_638_;
v_x_620_ = v_tail_622_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(lean_object* v_opts_645_, lean_object* v_opt_646_){
_start:
{
lean_object* v_name_647_; lean_object* v_defValue_648_; lean_object* v_map_649_; lean_object* v___x_650_; 
v_name_647_ = lean_ctor_get(v_opt_646_, 0);
v_defValue_648_ = lean_ctor_get(v_opt_646_, 1);
v_map_649_ = lean_ctor_get(v_opts_645_, 0);
v___x_650_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_649_, v_name_647_);
if (lean_obj_tag(v___x_650_) == 0)
{
uint8_t v___x_651_; 
v___x_651_ = lean_unbox(v_defValue_648_);
return v___x_651_;
}
else
{
lean_object* v_val_652_; 
v_val_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_652_);
lean_dec_ref_known(v___x_650_, 1);
if (lean_obj_tag(v_val_652_) == 1)
{
uint8_t v_v_653_; 
v_v_653_ = lean_ctor_get_uint8(v_val_652_, 0);
lean_dec_ref_known(v_val_652_, 0);
return v_v_653_;
}
else
{
uint8_t v___x_654_; 
lean_dec(v_val_652_);
v___x_654_ = lean_unbox(v_defValue_648_);
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_655_, lean_object* v_opt_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(v_opts_655_, v_opt_656_);
lean_dec_ref(v_opt_656_);
lean_dec_ref(v_opts_655_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__1));
v___x_663_ = l_Lean_MessageData_ofFormat(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(lean_object* v_msgData_664_, lean_object* v_macroStack_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_668_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_666_);
v___x_669_ = l_Lean_Elab_pp_macroStack;
v___x_670_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(v___x_668_, v___x_669_);
lean_dec_ref(v___x_668_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_dec(v_macroStack_665_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_msgData_664_);
return v___x_671_;
}
else
{
if (lean_obj_tag(v_macroStack_665_) == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v_msgData_664_);
return v___x_672_;
}
else
{
lean_object* v_head_673_; lean_object* v_after_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_689_; 
v_head_673_ = lean_ctor_get(v_macroStack_665_, 0);
lean_inc(v_head_673_);
v_after_674_ = lean_ctor_get(v_head_673_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_head_673_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v_head_673_, 0);
lean_dec(v_unused_690_);
v___x_676_ = v_head_673_;
v_isShared_677_ = v_isSharedCheck_689_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_after_674_);
lean_dec(v_head_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_689_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0);
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 7);
lean_ctor_set(v___x_676_, 1, v___x_678_);
lean_ctor_set(v___x_676_, 0, v_msgData_664_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_msgData_664_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_688_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_msgData_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_681_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_Lean_MessageData_ofSyntax(v_after_674_);
v___x_684_ = l_Lean_indentD(v___x_683_);
v_msgData_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_685_, 0, v___x_682_);
lean_ctor_set(v_msgData_685_, 1, v___x_684_);
v___x_686_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3(v_msgData_685_, v_macroStack_665_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_691_, lean_object* v_macroStack_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(v_msgData_691_, v_macroStack_692_, v___y_693_);
lean_dec_ref(v___y_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(lean_object* v_msg_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_ref_704_; lean_object* v_macroStack_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
v_ref_704_ = lean_ctor_get(v___y_701_, 2);
v_macroStack_705_ = lean_ctor_get(v___y_697_, 1);
v___x_706_ = l_Lean_Elab_getBetterRef(v_ref_704_, v_macroStack_705_);
v___x_707_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(v_msg_696_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
lean_inc(v_macroStack_705_);
v___x_709_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(v_a_708_, v_macroStack_705_, v___y_701_);
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_718_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_706_);
lean_ctor_set(v___x_714_, 1, v_a_710_);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 1);
lean_ctor_set(v___x_712_, 0, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg___boxed(lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_727_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5));
v___x_739_ = l_Lean_stringToMessageData(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13(void){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Array_mkArray0___redArg();
return v___x_755_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_775_ = l_String_toRawSubstring_x27(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(lean_object* v_letOrReassign_822_, lean_object* v_decl_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
if (lean_obj_tag(v_letOrReassign_822_) == 2)
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_823_);
v___x_832_ = l_Lean_Syntax_isOfKind(v_decl_823_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_833_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_834_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_835_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = l_Lean_Syntax_getArg(v_decl_823_, v___x_837_);
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_838_);
v___x_840_ = l_Lean_Syntax_isOfKind(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___y_843_; lean_object* v_pattern_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; uint8_t v___x_914_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_838_);
v___x_914_ = l_Lean_Syntax_isOfKind(v___x_838_, v___x_841_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec(v___x_838_);
v___x_915_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_916_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_917_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_918_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = l_Lean_Syntax_getArg(v___x_838_, v___x_919_);
v___x_921_ = l_Lean_Syntax_matchesNull(v___x_920_, v___x_837_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v___x_838_);
v___x_922_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_923_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_924_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_925_;
}
else
{
lean_object* v_pattern_926_; lean_object* v_xType_x3f_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_pattern_926_ = l_Lean_Syntax_getArg(v___x_838_, v___x_837_);
v___x_962_ = lean_unsigned_to_nat(2u);
v___x_963_ = l_Lean_Syntax_getArg(v___x_838_, v___x_962_);
v___x_964_ = l_Lean_Syntax_isNone(v___x_963_);
if (v___x_964_ == 0)
{
uint8_t v___x_965_; 
lean_inc(v___x_963_);
v___x_965_ = l_Lean_Syntax_matchesNull(v___x_963_, v___x_919_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v___x_963_);
lean_dec(v_pattern_926_);
lean_dec(v___x_838_);
v___x_966_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_967_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_968_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_970_ = l_Lean_Syntax_getArg(v___x_963_, v___x_837_);
lean_dec(v___x_963_);
v___x_971_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_970_);
v___x_972_ = l_Lean_Syntax_isOfKind(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v___x_970_);
lean_dec(v_pattern_926_);
lean_dec(v___x_838_);
v___x_973_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_974_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_975_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_976_;
}
else
{
lean_object* v_xType_x3f_977_; lean_object* v___x_978_; 
lean_dec(v_decl_823_);
v_xType_x3f_977_ = l_Lean_Syntax_getArg(v___x_970_, v___x_919_);
lean_dec(v___x_970_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v_xType_x3f_977_);
v_xType_x3f_928_ = v___x_978_;
v___y_929_ = v_a_824_;
v___y_930_ = v_a_825_;
v___y_931_ = v_a_826_;
v___y_932_ = v_a_827_;
v___y_933_ = v_a_828_;
v___y_934_ = v_a_829_;
goto v___jp_927_;
}
}
}
else
{
lean_object* v___x_979_; 
lean_dec(v___x_963_);
lean_dec(v_decl_823_);
v___x_979_ = lean_box(0);
v_xType_x3f_928_ = v___x_979_;
v___y_929_ = v_a_824_;
v___y_930_ = v_a_825_;
v___y_931_ = v_a_826_;
v___y_932_ = v_a_827_;
v___y_933_ = v_a_828_;
v___y_934_ = v_a_829_;
goto v___jp_927_;
}
v___jp_927_:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_unsigned_to_nat(4u);
v___x_936_ = l_Lean_Syntax_getArg(v___x_838_, v___x_935_);
lean_dec(v___x_838_);
if (lean_obj_tag(v_xType_x3f_928_) == 0)
{
v___y_843_ = v___x_936_;
v_pattern_844_ = v_pattern_926_;
v___y_845_ = v___y_929_;
v___y_846_ = v___y_930_;
v___y_847_ = v___y_931_;
v___y_848_ = v___y_932_;
v___y_849_ = v___y_933_;
v___y_850_ = v___y_934_;
goto v___jp_842_;
}
else
{
lean_object* v_toCold_937_; lean_object* v_val_938_; lean_object* v_ref_939_; lean_object* v_quotContext_940_; lean_object* v_currMacroScope_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_toCold_937_ = lean_ctor_get(v___y_933_, 0);
v_val_938_ = lean_ctor_get(v_xType_x3f_928_, 0);
lean_inc(v_val_938_);
lean_dec_ref_known(v_xType_x3f_928_, 1);
v_ref_939_ = lean_ctor_get(v___y_933_, 2);
v_quotContext_940_ = lean_ctor_get(v_toCold_937_, 8);
v_currMacroScope_941_ = lean_ctor_get(v_toCold_937_, 9);
v___x_942_ = l_Lean_SourceInfo_fromRef(v_ref_939_, v___x_840_);
v___x_943_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_944_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_945_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_942_, 7);
v___x_946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_942_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_948_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_949_ = lean_box(0);
lean_inc(v_currMacroScope_941_);
lean_inc(v_quotContext_940_);
v___x_950_ = l_Lean_addMacroScope(v_quotContext_940_, v___x_949_, v_currMacroScope_941_);
v___x_951_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_952_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_952_, 0, v___x_942_);
lean_ctor_set(v___x_952_, 1, v___x_948_);
lean_ctor_set(v___x_952_, 2, v___x_950_);
lean_ctor_set(v___x_952_, 3, v___x_951_);
v___x_953_ = l_Lean_Syntax_node1(v___x_942_, v___x_947_, v___x_952_);
v___x_954_ = l_Lean_Syntax_node2(v___x_942_, v___x_944_, v___x_946_, v___x_953_);
v___x_955_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_942_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_958_ = l_Lean_Syntax_node1(v___x_942_, v___x_957_, v_val_938_);
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_942_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l_Lean_Syntax_node5(v___x_942_, v___x_943_, v___x_954_, v_pattern_926_, v___x_956_, v___x_958_, v___x_960_);
v___y_843_ = v___x_936_;
v_pattern_844_ = v___x_961_;
v___y_845_ = v___y_929_;
v___y_846_ = v___y_930_;
v___y_847_ = v___y_931_;
v___y_848_ = v___y_932_;
v___y_849_ = v___y_933_;
v___y_850_ = v___y_934_;
goto v___jp_842_;
}
}
}
}
v___jp_842_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_851_ = lean_box(0);
v___x_852_ = lean_box(v___x_832_);
v___x_853_ = lean_box(v___x_832_);
lean_inc(v_pattern_844_);
v___x_854_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_854_, 0, v_pattern_844_);
lean_closure_set(v___x_854_, 1, v___x_851_);
lean_closure_set(v___x_854_, 2, v___x_852_);
lean_closure_set(v___x_854_, 3, v___x_853_);
v___x_855_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_854_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
v___x_857_ = lean_infer_type(v_a_856_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = l_Lean_Elab_Term_exprToSyntax(v_a_858_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_toCold_860_; lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_897_; 
v_toCold_860_ = lean_ctor_get(v___y_849_, 0);
v_a_861_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_897_ == 0)
{
v___x_863_ = v___x_859_;
v_isShared_864_ = v_isSharedCheck_897_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_897_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_ref_865_; lean_object* v_quotContext_866_; lean_object* v_currMacroScope_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v_ref_865_ = lean_ctor_get(v___y_849_, 2);
v_quotContext_866_ = lean_ctor_get(v_toCold_860_, 8);
v_currMacroScope_867_ = lean_ctor_get(v_toCold_860_, 9);
v___x_868_ = l_Lean_SourceInfo_fromRef(v_ref_865_, v___x_840_);
v___x_869_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_870_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_868_, 11);
v___x_871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_871_, 0, v___x_868_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
lean_ctor_set(v___x_871_, 2, v___x_870_);
v___x_872_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_868_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_875_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_876_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_868_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_879_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_880_ = lean_box(0);
lean_inc(v_currMacroScope_867_);
lean_inc(v_quotContext_866_);
v___x_881_ = l_Lean_addMacroScope(v_quotContext_866_, v___x_880_, v_currMacroScope_867_);
v___x_882_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_883_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_883_, 0, v___x_868_);
lean_ctor_set(v___x_883_, 1, v___x_879_);
lean_ctor_set(v___x_883_, 2, v___x_881_);
lean_ctor_set(v___x_883_, 3, v___x_882_);
v___x_884_ = l_Lean_Syntax_node1(v___x_868_, v___x_878_, v___x_883_);
v___x_885_ = l_Lean_Syntax_node2(v___x_868_, v___x_875_, v___x_877_, v___x_884_);
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_868_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_Syntax_node1(v___x_868_, v___x_869_, v_a_861_);
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_868_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_Lean_Syntax_node5(v___x_868_, v___x_874_, v___x_885_, v___y_843_, v___x_887_, v___x_888_, v___x_890_);
lean_inc_ref(v___x_871_);
v___x_892_ = l_Lean_Syntax_node5(v___x_868_, v___x_841_, v_pattern_844_, v___x_871_, v___x_871_, v___x_873_, v___x_891_);
v___x_893_ = l_Lean_Syntax_node1(v___x_868_, v___x_831_, v___x_892_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_893_);
v___x_895_ = v___x_863_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_dec(v_pattern_844_);
lean_dec(v___y_843_);
return v___x_859_;
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_pattern_844_);
lean_dec(v___y_843_);
v_a_898_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_857_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_857_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec(v_pattern_844_);
lean_dec(v___y_843_);
v_a_906_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_855_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_855_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = l_Lean_Syntax_getArg(v___x_838_, v___x_837_);
v___x_981_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_980_);
v___x_982_ = l_Lean_Syntax_isOfKind(v___x_980_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec(v___x_980_);
lean_dec(v___x_838_);
v___x_983_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_984_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_985_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_986_;
}
else
{
lean_object* v_x_987_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v_a_996_; lean_object* v_xType_x3f_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_x_987_ = l_Lean_Syntax_getArg(v___x_980_, v___x_837_);
lean_dec(v___x_980_);
v___x_1073_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_987_);
v___x_1074_ = l_Lean_Syntax_isOfKind(v_x_987_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v_x_987_);
lean_dec(v___x_838_);
v___x_1075_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_1076_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_1077_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = l_Lean_Syntax_getArg(v___x_838_, v___x_1079_);
v___x_1081_ = l_Lean_Syntax_matchesNull(v___x_1080_, v___x_837_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec(v_x_987_);
lean_dec(v___x_838_);
v___x_1082_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_1083_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_1084_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1086_ = lean_unsigned_to_nat(2u);
v___x_1087_ = l_Lean_Syntax_getArg(v___x_838_, v___x_1086_);
v___x_1088_ = l_Lean_Syntax_isNone(v___x_1087_);
if (v___x_1088_ == 0)
{
uint8_t v___x_1089_; 
lean_inc(v___x_1087_);
v___x_1089_ = l_Lean_Syntax_matchesNull(v___x_1087_, v___x_1079_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec(v___x_1087_);
lean_dec(v_x_987_);
lean_dec(v___x_838_);
v___x_1090_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_1091_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_1092_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1094_ = l_Lean_Syntax_getArg(v___x_1087_, v___x_837_);
lean_dec(v___x_1087_);
v___x_1095_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_1094_);
v___x_1096_ = l_Lean_Syntax_isOfKind(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec(v___x_1094_);
lean_dec(v_x_987_);
lean_dec(v___x_838_);
v___x_1097_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_1098_ = l_Lean_MessageData_ofSyntax(v_decl_823_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_1099_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_1100_;
}
else
{
lean_object* v_xType_x3f_1101_; lean_object* v___x_1102_; 
lean_dec(v_decl_823_);
v_xType_x3f_1101_ = l_Lean_Syntax_getArg(v___x_1094_, v___x_1079_);
lean_dec(v___x_1094_);
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_xType_x3f_1101_);
v_xType_x3f_1045_ = v___x_1102_;
v___y_1046_ = v_a_824_;
v___y_1047_ = v_a_825_;
v___y_1048_ = v_a_826_;
v___y_1049_ = v_a_827_;
v___y_1050_ = v_a_828_;
v___y_1051_ = v_a_829_;
goto v___jp_1044_;
}
}
}
else
{
lean_object* v___x_1103_; 
lean_dec(v___x_1087_);
lean_dec(v_decl_823_);
v___x_1103_ = lean_box(0);
v_xType_x3f_1045_ = v___x_1103_;
v___y_1046_ = v_a_824_;
v___y_1047_ = v_a_825_;
v___y_1048_ = v_a_826_;
v___y_1049_ = v_a_827_;
v___y_1050_ = v_a_828_;
v___y_1051_ = v_a_829_;
goto v___jp_1044_;
}
}
}
v___jp_988_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_box(0);
lean_inc(v_x_987_);
v___x_998_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_987_, v_a_996_, v___x_832_, v___x_832_, v___x_997_, v___y_995_, v___y_991_, v___y_989_, v___y_994_, v___y_992_, v___y_990_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec_ref_known(v___x_998_, 1);
v___x_999_ = l_Lean_TSyntax_getId(v_x_987_);
v___x_1000_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_999_, v___y_989_, v___y_994_, v___y_992_, v___y_990_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_LocalDecl_type(v_a_1001_);
lean_dec(v_a_1001_);
v___x_1003_ = l_Lean_Elab_Term_exprToSyntax(v___x_1002_, v___y_995_, v___y_991_, v___y_989_, v___y_994_, v___y_992_, v___y_990_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1027_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1027_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1027_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_ref_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v_ref_1008_ = lean_ctor_get(v___y_992_, 2);
v___x_1009_ = 0;
v___x_1010_ = l_Lean_SourceInfo_fromRef(v_ref_1008_, v___x_1009_);
lean_inc_n(v___x_1010_, 7);
v___x_1011_ = l_Lean_Syntax_node1(v___x_1010_, v___x_981_, v_x_987_);
v___x_1012_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_1013_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_1014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1010_);
lean_ctor_set(v___x_1014_, 1, v___x_1012_);
lean_ctor_set(v___x_1014_, 2, v___x_1013_);
v___x_1015_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_1017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1010_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_Syntax_node2(v___x_1010_, v___x_1015_, v___x_1017_, v_a_1004_);
v___x_1019_ = l_Lean_Syntax_node1(v___x_1010_, v___x_1012_, v___x_1018_);
v___x_1020_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_1021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1010_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_Syntax_node5(v___x_1010_, v___x_839_, v___x_1011_, v___x_1014_, v___x_1019_, v___x_1021_, v___y_993_);
v___x_1023_ = l_Lean_Syntax_node1(v___x_1010_, v___x_831_, v___x_1022_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1023_);
v___x_1025_ = v___x_1006_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
else
{
lean_dec(v___y_993_);
lean_dec(v_x_987_);
return v___x_1003_;
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v___y_993_);
lean_dec(v_x_987_);
v_a_1028_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1000_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1000_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v___y_993_);
lean_dec(v_x_987_);
v_a_1036_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_998_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_998_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
v___jp_1044_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_unsigned_to_nat(4u);
v___x_1053_ = l_Lean_Syntax_getArg(v___x_838_, v___x_1052_);
lean_dec(v___x_838_);
if (lean_obj_tag(v_xType_x3f_1045_) == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_box(0);
v___y_989_ = v___y_1048_;
v___y_990_ = v___y_1051_;
v___y_991_ = v___y_1047_;
v___y_992_ = v___y_1050_;
v___y_993_ = v___x_1053_;
v___y_994_ = v___y_1049_;
v___y_995_ = v___y_1046_;
v_a_996_ = v___x_1054_;
goto v___jp_988_;
}
else
{
lean_object* v_val_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1072_; 
v_val_1055_ = lean_ctor_get(v_xType_x3f_1045_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_xType_x3f_1045_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1057_ = v_xType_x3f_1045_;
v_isShared_1058_ = v_isSharedCheck_1072_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_val_1055_);
lean_dec(v_xType_x3f_1045_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1072_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Elab_Term_elabType(v_val_1055_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v_a_1060_);
v___x_1062_ = v___x_1057_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
v___y_989_ = v___y_1048_;
v___y_990_ = v___y_1051_;
v___y_991_ = v___y_1047_;
v___y_992_ = v___y_1050_;
v___y_993_ = v___x_1053_;
v___y_994_ = v___y_1049_;
v___y_995_ = v___y_1046_;
v_a_996_ = v___x_1062_;
goto v___jp_988_;
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_del_object(v___x_1057_);
lean_dec(v___x_1053_);
lean_dec(v_x_987_);
v_a_1064_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1059_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1059_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
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
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_decl_823_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object* v_letOrReassign_1105_, lean_object* v_decl_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_1105_, v_decl_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_letOrReassign_1105_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_1115_, lean_object* v_msg_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_msg_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(v_00_u03b1_1125_, v_msg_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(lean_object* v_msgData_1135_, lean_object* v_macroStack_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(v_msgData_1135_, v_macroStack_1136_, v___y_1141_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___boxed(lean_object* v_msgData_1145_, lean_object* v_macroStack_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msgData_1145_, v_macroStack_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1154_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__0));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__2));
v___x_1160_ = l_Lean_stringToMessageData(v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(lean_object* v_config_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
uint8_t v_postponeValue_1167_; uint8_t v_generalize_1168_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; 
v_postponeValue_1167_ = lean_ctor_get_uint8(v_config_1161_, sizeof(void*)*1 + 3);
v_generalize_1168_ = lean_ctor_get_uint8(v_config_1161_, sizeof(void*)*1 + 4);
if (v_postponeValue_1167_ == 0)
{
v___y_1170_ = v_a_1162_;
v___y_1171_ = v_a_1163_;
v___y_1172_ = v_a_1164_;
v___y_1173_ = v_a_1165_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3);
v___x_1179_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v___x_1178_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1179_;
}
v___jp_1169_:
{
if (v_generalize_1168_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1);
v___x_1177_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v___x_1176_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1177_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___boxed(lean_object* v_config_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_config_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec_ref(v_config_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object* v_config_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_config_1187_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object* v_config_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec_ref(v_config_1197_);
return v_res_1206_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg(){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0);
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___boxed(lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0(lean_object* v_00_u03b1_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___boxed(lean_object* v_00_u03b1_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0(v_00_u03b1_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1234_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__2));
v___x_1243_ = l_String_toRawSubstring_x27(v___x_1242_);
return v___x_1243_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__4));
v___x_1256_ = l_String_toRawSubstring_x27(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(lean_object* v_decl_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_1279_);
v___x_1289_ = l_Lean_Syntax_isOfKind(v_decl_1279_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec(v_decl_1279_);
v___x_1290_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = l_Lean_Syntax_getArg(v_decl_1279_, v___x_1291_);
lean_dec(v_decl_1279_);
v___x_1293_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_1292_);
v___x_1294_ = l_Lean_Syntax_isOfKind(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; 
lean_dec(v___x_1292_);
v___x_1295_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = l_Lean_Syntax_getArg(v___x_1292_, v___x_1291_);
v___x_1297_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_1296_);
v___x_1298_ = l_Lean_Syntax_isOfKind(v___x_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
lean_dec(v___x_1296_);
lean_dec(v___x_1292_);
v___x_1299_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v_t_x3f_1302_; lean_object* v___y_1303_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1300_ = l_Lean_Syntax_getArg(v___x_1296_, v___x_1291_);
lean_dec(v___x_1296_);
v___x_1386_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_1300_);
v___x_1387_ = l_Lean_Syntax_isOfKind(v___x_1300_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
lean_dec(v___x_1300_);
lean_dec(v___x_1292_);
v___x_1388_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1388_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = l_Lean_Syntax_getArg(v___x_1292_, v___x_1389_);
v___x_1391_ = l_Lean_Syntax_matchesNull(v___x_1390_, v___x_1291_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
lean_dec(v___x_1300_);
lean_dec(v___x_1292_);
v___x_1392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1392_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1393_ = lean_unsigned_to_nat(2u);
v___x_1394_ = l_Lean_Syntax_getArg(v___x_1292_, v___x_1393_);
v___x_1395_ = l_Lean_Syntax_isNone(v___x_1394_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; 
lean_inc(v___x_1394_);
v___x_1396_ = l_Lean_Syntax_matchesNull(v___x_1394_, v___x_1389_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v___x_1394_);
lean_dec(v___x_1300_);
lean_dec(v___x_1292_);
v___x_1397_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1398_ = l_Lean_Syntax_getArg(v___x_1394_, v___x_1291_);
lean_dec(v___x_1394_);
v___x_1399_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_1398_);
v___x_1400_ = l_Lean_Syntax_isOfKind(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v___x_1398_);
lean_dec(v___x_1300_);
lean_dec(v___x_1292_);
v___x_1401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1401_;
}
else
{
lean_object* v_t_x3f_1402_; lean_object* v___x_1403_; 
v_t_x3f_1402_ = l_Lean_Syntax_getArg(v___x_1398_, v___x_1389_);
lean_dec(v___x_1398_);
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_t_x3f_1402_);
v_t_x3f_1302_ = v___x_1403_;
v___y_1303_ = v_a_1285_;
goto v___jp_1301_;
}
}
}
else
{
lean_object* v___x_1404_; 
lean_dec(v___x_1394_);
v___x_1404_ = lean_box(0);
v_t_x3f_1302_ = v___x_1404_;
v___y_1303_ = v_a_1285_;
goto v___jp_1301_;
}
}
}
v___jp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_unsigned_to_nat(4u);
v___x_1305_ = l_Lean_Syntax_getArg(v___x_1292_, v___x_1304_);
lean_dec(v___x_1292_);
if (lean_obj_tag(v_t_x3f_1302_) == 0)
{
lean_object* v_toCold_1306_; lean_object* v_ref_1307_; lean_object* v_quotContext_1308_; lean_object* v_currMacroScope_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_toCold_1306_ = lean_ctor_get(v___y_1303_, 0);
v_ref_1307_ = lean_ctor_get(v___y_1303_, 2);
v_quotContext_1308_ = lean_ctor_get(v_toCold_1306_, 8);
v_currMacroScope_1309_ = lean_ctor_get(v_toCold_1306_, 9);
v___x_1310_ = 0;
v___x_1311_ = l_Lean_SourceInfo_fromRef(v_ref_1307_, v___x_1310_);
lean_inc_n(v___x_1311_, 7);
v___x_1312_ = l_Lean_Syntax_node1(v___x_1311_, v___x_1297_, v___x_1300_);
v___x_1313_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_1314_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_1315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1311_);
lean_ctor_set(v___x_1315_, 1, v___x_1313_);
lean_ctor_set(v___x_1315_, 2, v___x_1314_);
v___x_1316_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_1317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1311_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1));
v___x_1319_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3);
v___x_1320_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6));
lean_inc(v_currMacroScope_1309_);
lean_inc(v_quotContext_1308_);
v___x_1321_ = l_Lean_addMacroScope(v_quotContext_1308_, v___x_1320_, v_currMacroScope_1309_);
v___x_1322_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__8));
v___x_1323_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1311_);
lean_ctor_set(v___x_1323_, 1, v___x_1319_);
lean_ctor_set(v___x_1323_, 2, v___x_1321_);
lean_ctor_set(v___x_1323_, 3, v___x_1322_);
v___x_1324_ = l_Lean_Syntax_node1(v___x_1311_, v___x_1313_, v___x_1305_);
v___x_1325_ = l_Lean_Syntax_node2(v___x_1311_, v___x_1318_, v___x_1323_, v___x_1324_);
lean_inc_ref(v___x_1315_);
v___x_1326_ = l_Lean_Syntax_node5(v___x_1311_, v___x_1293_, v___x_1312_, v___x_1315_, v___x_1315_, v___x_1317_, v___x_1325_);
v___x_1327_ = l_Lean_Syntax_node1(v___x_1311_, v___x_1288_, v___x_1326_);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
else
{
lean_object* v_toCold_1329_; lean_object* v_val_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1385_; 
v_toCold_1329_ = lean_ctor_get(v___y_1303_, 0);
v_val_1330_ = lean_ctor_get(v_t_x3f_1302_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_t_x3f_1302_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1332_ = v_t_x3f_1302_;
v_isShared_1333_ = v_isSharedCheck_1385_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_val_1330_);
lean_dec(v_t_x3f_1302_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1385_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_ref_1334_; lean_object* v_quotContext_1335_; lean_object* v_currMacroScope_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v_ref_1334_ = lean_ctor_get(v___y_1303_, 2);
v_quotContext_1335_ = lean_ctor_get(v_toCold_1329_, 8);
v_currMacroScope_1336_ = lean_ctor_get(v_toCold_1329_, 9);
v___x_1337_ = 0;
v___x_1338_ = l_Lean_SourceInfo_fromRef(v_ref_1334_, v___x_1337_);
lean_inc_n(v___x_1338_, 19);
v___x_1339_ = l_Lean_Syntax_node1(v___x_1338_, v___x_1297_, v___x_1300_);
v___x_1340_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_1341_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_1342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1338_);
lean_ctor_set(v___x_1342_, 1, v___x_1340_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
v___x_1343_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_1344_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_1345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1338_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1));
v___x_1347_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9);
v___x_1348_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__10));
lean_inc_n(v_currMacroScope_1336_, 3);
lean_inc_n(v_quotContext_1335_, 3);
v___x_1349_ = l_Lean_addMacroScope(v_quotContext_1335_, v___x_1348_, v_currMacroScope_1336_);
v___x_1350_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__14));
v___x_1351_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1338_);
lean_ctor_set(v___x_1351_, 1, v___x_1347_);
lean_ctor_set(v___x_1351_, 2, v___x_1349_);
lean_ctor_set(v___x_1351_, 3, v___x_1350_);
v___x_1352_ = l_Lean_Syntax_node1(v___x_1338_, v___x_1340_, v_val_1330_);
lean_inc(v___x_1352_);
v___x_1353_ = l_Lean_Syntax_node2(v___x_1338_, v___x_1346_, v___x_1351_, v___x_1352_);
lean_inc_ref(v___x_1345_);
v___x_1354_ = l_Lean_Syntax_node2(v___x_1338_, v___x_1343_, v___x_1345_, v___x_1353_);
v___x_1355_ = l_Lean_Syntax_node1(v___x_1338_, v___x_1340_, v___x_1354_);
v___x_1356_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_1357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1338_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3);
v___x_1359_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6));
v___x_1360_ = l_Lean_addMacroScope(v_quotContext_1335_, v___x_1359_, v_currMacroScope_1336_);
v___x_1361_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__8));
v___x_1362_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1338_);
lean_ctor_set(v___x_1362_, 1, v___x_1358_);
lean_ctor_set(v___x_1362_, 2, v___x_1360_);
lean_ctor_set(v___x_1362_, 3, v___x_1361_);
v___x_1363_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_1364_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_1365_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_1366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1338_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_1368_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_1369_ = lean_box(0);
v___x_1370_ = l_Lean_addMacroScope(v_quotContext_1335_, v___x_1369_, v_currMacroScope_1336_);
v___x_1371_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__17));
v___x_1372_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1338_);
lean_ctor_set(v___x_1372_, 1, v___x_1368_);
lean_ctor_set(v___x_1372_, 2, v___x_1370_);
lean_ctor_set(v___x_1372_, 3, v___x_1371_);
v___x_1373_ = l_Lean_Syntax_node1(v___x_1338_, v___x_1367_, v___x_1372_);
v___x_1374_ = l_Lean_Syntax_node2(v___x_1338_, v___x_1364_, v___x_1366_, v___x_1373_);
v___x_1375_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_1376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1338_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_Syntax_node5(v___x_1338_, v___x_1363_, v___x_1374_, v___x_1305_, v___x_1345_, v___x_1352_, v___x_1376_);
v___x_1378_ = l_Lean_Syntax_node1(v___x_1338_, v___x_1340_, v___x_1377_);
v___x_1379_ = l_Lean_Syntax_node2(v___x_1338_, v___x_1346_, v___x_1362_, v___x_1378_);
v___x_1380_ = l_Lean_Syntax_node5(v___x_1338_, v___x_1293_, v___x_1339_, v___x_1342_, v___x_1355_, v___x_1357_, v___x_1379_);
v___x_1381_ = l_Lean_Syntax_node1(v___x_1338_, v___x_1288_, v___x_1380_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set_tag(v___x_1332_, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1381_);
v___x_1383_ = v___x_1332_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___boxed(lean_object* v_decl_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(v_decl_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg(lean_object* v_lctx_1415_, lean_object* v_x_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_keyedConfig_1424_; uint8_t v_trackZetaDelta_1425_; lean_object* v_zetaDeltaSet_1426_; lean_object* v_localInstances_1427_; lean_object* v_defEqCtx_x3f_1428_; lean_object* v_synthPendingDepth_1429_; lean_object* v_customCanUnfoldPredicate_x3f_1430_; uint8_t v_univApprox_1431_; uint8_t v_inTypeClassResolution_1432_; uint8_t v_cacheInferType_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_keyedConfig_1424_ = lean_ctor_get(v___y_1419_, 0);
v_trackZetaDelta_1425_ = lean_ctor_get_uint8(v___y_1419_, sizeof(void*)*7);
v_zetaDeltaSet_1426_ = lean_ctor_get(v___y_1419_, 1);
v_localInstances_1427_ = lean_ctor_get(v___y_1419_, 3);
v_defEqCtx_x3f_1428_ = lean_ctor_get(v___y_1419_, 4);
v_synthPendingDepth_1429_ = lean_ctor_get(v___y_1419_, 5);
v_customCanUnfoldPredicate_x3f_1430_ = lean_ctor_get(v___y_1419_, 6);
v_univApprox_1431_ = lean_ctor_get_uint8(v___y_1419_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1432_ = lean_ctor_get_uint8(v___y_1419_, sizeof(void*)*7 + 2);
v_cacheInferType_1433_ = lean_ctor_get_uint8(v___y_1419_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1430_);
lean_inc(v_synthPendingDepth_1429_);
lean_inc(v_defEqCtx_x3f_1428_);
lean_inc_ref(v_localInstances_1427_);
lean_inc(v_zetaDeltaSet_1426_);
lean_inc_ref(v_keyedConfig_1424_);
v___x_1434_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1434_, 0, v_keyedConfig_1424_);
lean_ctor_set(v___x_1434_, 1, v_zetaDeltaSet_1426_);
lean_ctor_set(v___x_1434_, 2, v_lctx_1415_);
lean_ctor_set(v___x_1434_, 3, v_localInstances_1427_);
lean_ctor_set(v___x_1434_, 4, v_defEqCtx_x3f_1428_);
lean_ctor_set(v___x_1434_, 5, v_synthPendingDepth_1429_);
lean_ctor_set(v___x_1434_, 6, v_customCanUnfoldPredicate_x3f_1430_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*7, v_trackZetaDelta_1425_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*7 + 1, v_univApprox_1431_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1432_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*7 + 3, v_cacheInferType_1433_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
lean_inc(v___y_1420_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
v___x_1435_ = lean_apply_7(v_x_1416_, v___y_1417_, v___y_1418_, v___x_1434_, v___y_1420_, v___y_1421_, v___y_1422_, lean_box(0));
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
else
{
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg___boxed(lean_object* v_lctx_1444_, lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg(v_lctx_1444_, v_x_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(lean_object* v_00_u03b1_1454_, lean_object* v_lctx_1455_, lean_object* v_x_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg(v_lctx_1455_, v_x_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_00_u03b1_1465_, lean_object* v_lctx_1466_, lean_object* v_x_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_00_u03b1_1465_, v_lctx_1466_, v_x_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0(lean_object* v_k_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc_ref(v___y_1477_);
v___x_1486_ = lean_apply_9(v_k_1476_, v_b_1480_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, lean_box(0));
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0___boxed(lean_object* v_k_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0(v_k_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v_b_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(lean_object* v_name_1498_, lean_object* v_type_1499_, lean_object* v_val_1500_, lean_object* v_k_1501_, uint8_t v_nondep_1502_, uint8_t v_kind_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___f_1512_; lean_object* v___x_1513_; 
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc_ref(v___y_1504_);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1512_, 0, v_k_1501_);
lean_closure_set(v___f_1512_, 1, v___y_1504_);
lean_closure_set(v___f_1512_, 2, v___y_1505_);
lean_closure_set(v___f_1512_, 3, v___y_1506_);
v___x_1513_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1498_, v_type_1499_, v_val_1500_, v___f_1512_, v_nondep_1502_, v_kind_1503_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1513_) == 0)
{
return v___x_1513_;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___boxed(lean_object* v_name_1522_, lean_object* v_type_1523_, lean_object* v_val_1524_, lean_object* v_k_1525_, lean_object* v_nondep_1526_, lean_object* v_kind_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v_nondep_boxed_1536_; uint8_t v_kind_boxed_1537_; lean_object* v_res_1538_; 
v_nondep_boxed_1536_ = lean_unbox(v_nondep_1526_);
v_kind_boxed_1537_ = lean_unbox(v_kind_1527_);
v_res_1538_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v_name_1522_, v_type_1523_, v_val_1524_, v_k_1525_, v_nondep_boxed_1536_, v_kind_boxed_1537_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_00_u03b1_1539_, lean_object* v_name_1540_, lean_object* v_type_1541_, lean_object* v_val_1542_, lean_object* v_k_1543_, uint8_t v_nondep_1544_, uint8_t v_kind_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v_name_1540_, v_type_1541_, v_val_1542_, v_k_1543_, v_nondep_1544_, v_kind_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_00_u03b1_1555_, lean_object* v_name_1556_, lean_object* v_type_1557_, lean_object* v_val_1558_, lean_object* v_k_1559_, lean_object* v_nondep_1560_, lean_object* v_kind_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v_nondep_boxed_1570_; uint8_t v_kind_boxed_1571_; lean_object* v_res_1572_; 
v_nondep_boxed_1570_ = lean_unbox(v_nondep_1560_);
v_kind_boxed_1571_ = lean_unbox(v_kind_1561_);
v_res_1572_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_00_u03b1_1555_, v_name_1556_, v_type_1557_, v_val_1558_, v_k_1559_, v_nondep_boxed_1570_, v_kind_boxed_1571_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v___y_1562_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1573_, lean_object* v___x_1574_, uint8_t v___x_1575_, lean_object* v___x_1576_, lean_object* v___x_1577_, uint8_t v___x_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1573_, v___x_1574_, v___x_1575_, v___x_1575_, v___x_1576_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = 1;
v___x_1589_ = l_Lean_Meta_mkLambdaFVars(v___x_1577_, v_a_1587_, v___x_1578_, v___x_1578_, v___x_1578_, v___x_1575_, v___x_1588_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v___x_1589_;
}
else
{
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1590_, lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v___x_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v___x_88434__boxed_1603_; uint8_t v___x_88437__boxed_1604_; lean_object* v_res_1605_; 
v___x_88434__boxed_1603_ = lean_unbox(v___x_1592_);
v___x_88437__boxed_1604_ = lean_unbox(v___x_1595_);
v_res_1605_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1590_, v___x_1591_, v___x_88434__boxed_1603_, v___x_1593_, v___x_1594_, v___x_88437__boxed_1604_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec_ref(v___x_1594_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(size_t v_sz_1606_, size_t v_i_1607_, lean_object* v_bs_1608_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_usize_dec_lt(v_i_1607_, v_sz_1606_);
if (v___x_1609_ == 0)
{
return v_bs_1608_;
}
else
{
lean_object* v_v_1610_; lean_object* v_snd_1611_; lean_object* v___x_1612_; lean_object* v_bs_x27_1613_; size_t v___x_1614_; size_t v___x_1615_; lean_object* v___x_1616_; 
v_v_1610_ = lean_array_uget_borrowed(v_bs_1608_, v_i_1607_);
v_snd_1611_ = lean_ctor_get(v_v_1610_, 1);
lean_inc(v_snd_1611_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v_bs_x27_1613_ = lean_array_uset(v_bs_1608_, v_i_1607_, v___x_1612_);
v___x_1614_ = ((size_t)1ULL);
v___x_1615_ = lean_usize_add(v_i_1607_, v___x_1614_);
v___x_1616_ = lean_array_uset(v_bs_x27_1613_, v_i_1607_, v_snd_1611_);
v_i_1607_ = v___x_1615_;
v_bs_1608_ = v___x_1616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_sz_1618_, lean_object* v_i_1619_, lean_object* v_bs_1620_){
_start:
{
size_t v_sz_boxed_1621_; size_t v_i_boxed_1622_; lean_object* v_res_1623_; 
v_sz_boxed_1621_ = lean_unbox_usize(v_sz_1618_);
lean_dec(v_sz_1618_);
v_i_boxed_1622_ = lean_unbox_usize(v_i_1619_);
lean_dec(v_i_1619_);
v_res_1623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_sz_boxed_1621_, v_i_boxed_1622_, v_bs_1620_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14___redArg(lean_object* v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v_ks_1628_; lean_object* v_vs_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1653_; 
v_ks_1628_ = lean_ctor_get(v_x_1624_, 0);
v_vs_1629_ = lean_ctor_get(v_x_1624_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_x_1624_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1631_ = v_x_1624_;
v_isShared_1632_ = v_isSharedCheck_1653_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_vs_1629_);
lean_inc(v_ks_1628_);
lean_dec(v_x_1624_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1653_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = lean_array_get_size(v_ks_1628_);
v___x_1634_ = lean_nat_dec_lt(v_x_1625_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
lean_dec(v_x_1625_);
v___x_1635_ = lean_array_push(v_ks_1628_, v_x_1626_);
v___x_1636_ = lean_array_push(v_vs_1629_, v_x_1627_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 1, v___x_1636_);
lean_ctor_set(v___x_1631_, 0, v___x_1635_);
v___x_1638_ = v___x_1631_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
else
{
lean_object* v_k_x27_1640_; uint8_t v___x_1641_; 
v_k_x27_1640_ = lean_array_fget_borrowed(v_ks_1628_, v_x_1625_);
v___x_1641_ = l_Lean_instBEqFVarId_beq(v_x_1626_, v_k_x27_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1643_; 
if (v_isShared_1632_ == 0)
{
v___x_1643_ = v___x_1631_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_ks_1628_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_vs_1629_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_add(v_x_1625_, v___x_1644_);
lean_dec(v_x_1625_);
v_x_1624_ = v___x_1643_;
v_x_1625_ = v___x_1645_;
goto _start;
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1648_ = lean_array_fset(v_ks_1628_, v_x_1625_, v_x_1626_);
v___x_1649_ = lean_array_fset(v_vs_1629_, v_x_1625_, v_x_1627_);
lean_dec(v_x_1625_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 1, v___x_1649_);
lean_ctor_set(v___x_1631_, 0, v___x_1648_);
v___x_1651_ = v___x_1631_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(lean_object* v_n_1654_, lean_object* v_k_1655_, lean_object* v_v_1656_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14___redArg(v_n_1654_, v___x_1657_, v_k_1655_, v_v_1656_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1660_, size_t v_x_1661_, size_t v_x_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
if (lean_obj_tag(v_x_1660_) == 0)
{
lean_object* v_es_1665_; size_t v___x_1666_; size_t v___x_1667_; lean_object* v_j_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v_es_1665_ = lean_ctor_get(v_x_1660_, 0);
v___x_1666_ = ((size_t)31ULL);
v___x_1667_ = lean_usize_land(v_x_1661_, v___x_1666_);
v_j_1668_ = lean_usize_to_nat(v___x_1667_);
v___x_1669_ = lean_array_get_size(v_es_1665_);
v___x_1670_ = lean_nat_dec_lt(v_j_1668_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_dec(v_j_1668_);
lean_dec(v_x_1664_);
lean_dec(v_x_1663_);
return v_x_1660_;
}
else
{
lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1709_; 
lean_inc_ref(v_es_1665_);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_x_1660_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v_x_1660_, 0);
lean_dec(v_unused_1710_);
v___x_1672_ = v_x_1660_;
v_isShared_1673_ = v_isSharedCheck_1709_;
goto v_resetjp_1671_;
}
else
{
lean_dec(v_x_1660_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1709_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_v_1674_; lean_object* v___x_1675_; lean_object* v_xs_x27_1676_; lean_object* v___y_1678_; 
v_v_1674_ = lean_array_fget(v_es_1665_, v_j_1668_);
v___x_1675_ = lean_box(0);
v_xs_x27_1676_ = lean_array_fset(v_es_1665_, v_j_1668_, v___x_1675_);
switch(lean_obj_tag(v_v_1674_))
{
case 0:
{
lean_object* v_key_1683_; lean_object* v_val_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1694_; 
v_key_1683_ = lean_ctor_get(v_v_1674_, 0);
v_val_1684_ = lean_ctor_get(v_v_1674_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_v_1674_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1686_ = v_v_1674_;
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_val_1684_);
lean_inc(v_key_1683_);
lean_dec(v_v_1674_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
uint8_t v___x_1688_; 
v___x_1688_ = l_Lean_instBEqFVarId_beq(v_x_1663_, v_key_1683_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_del_object(v___x_1686_);
v___x_1689_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1683_, v_val_1684_, v_x_1663_, v_x_1664_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
v___y_1678_ = v___x_1690_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1692_; 
lean_dec(v_val_1684_);
lean_dec(v_key_1683_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v_x_1664_);
lean_ctor_set(v___x_1686_, 0, v_x_1663_);
v___x_1692_ = v___x_1686_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_x_1663_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_x_1664_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
v___y_1678_ = v___x_1692_;
goto v___jp_1677_;
}
}
}
}
case 1:
{
lean_object* v_node_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1707_; 
v_node_1695_ = lean_ctor_get(v_v_1674_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_v_1674_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1697_ = v_v_1674_;
v_isShared_1698_ = v_isSharedCheck_1707_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_node_1695_);
lean_dec(v_v_1674_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1707_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
size_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1699_ = ((size_t)5ULL);
v___x_1700_ = lean_usize_shift_right(v_x_1661_, v___x_1699_);
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_x_1662_, v___x_1701_);
v___x_1703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1695_, v___x_1700_, v___x_1702_, v_x_1663_, v_x_1664_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1703_);
v___x_1705_ = v___x_1697_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
v___y_1678_ = v___x_1705_;
goto v___jp_1677_;
}
}
}
default: 
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v_x_1663_);
lean_ctor_set(v___x_1708_, 1, v_x_1664_);
v___y_1678_ = v___x_1708_;
goto v___jp_1677_;
}
}
v___jp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_array_fset(v_xs_x27_1676_, v_j_1668_, v___y_1678_);
lean_dec(v_j_1668_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1679_);
v___x_1681_ = v___x_1672_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
else
{
lean_object* v_ks_1711_; lean_object* v_vs_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1730_; 
v_ks_1711_ = lean_ctor_get(v_x_1660_, 0);
v_vs_1712_ = lean_ctor_get(v_x_1660_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_x_1660_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1714_ = v_x_1660_;
v_isShared_1715_ = v_isSharedCheck_1730_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_vs_1712_);
lean_inc(v_ks_1711_);
lean_dec(v_x_1660_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1730_;
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
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_ks_1711_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_vs_1712_);
v___x_1717_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v_newNode_1718_; size_t v___x_1719_; uint8_t v___x_1720_; 
v_newNode_1718_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(v___x_1717_, v_x_1663_, v_x_1664_);
v___x_1719_ = ((size_t)7ULL);
v___x_1720_ = lean_usize_dec_le(v___x_1719_, v_x_1662_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1718_);
v___x_1722_ = lean_unsigned_to_nat(4u);
v___x_1723_ = lean_nat_dec_lt(v___x_1721_, v___x_1722_);
lean_dec(v___x_1721_);
if (v___x_1723_ == 0)
{
lean_object* v_ks_1724_; lean_object* v_vs_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_ks_1724_ = lean_ctor_get(v_newNode_1718_, 0);
lean_inc_ref(v_ks_1724_);
v_vs_1725_ = lean_ctor_get(v_newNode_1718_, 1);
lean_inc_ref(v_vs_1725_);
lean_dec_ref(v_newNode_1718_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1728_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_x_1662_, v_ks_1724_, v_vs_1725_, v___x_1726_, v___x_1727_);
lean_dec_ref(v_vs_1725_);
lean_dec_ref(v_ks_1724_);
return v___x_1728_;
}
else
{
return v_newNode_1718_;
}
}
else
{
return v_newNode_1718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(size_t v_depth_1731_, lean_object* v_keys_1732_, lean_object* v_vals_1733_, lean_object* v_i_1734_, lean_object* v_entries_1735_){
_start:
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = lean_array_get_size(v_keys_1732_);
v___x_1737_ = lean_nat_dec_lt(v_i_1734_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_dec(v_i_1734_);
return v_entries_1735_;
}
else
{
lean_object* v_k_1738_; lean_object* v_v_1739_; uint64_t v___x_1740_; size_t v_h_1741_; size_t v___x_1742_; lean_object* v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; size_t v___x_1746_; size_t v_h_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_k_1738_ = lean_array_fget_borrowed(v_keys_1732_, v_i_1734_);
v_v_1739_ = lean_array_fget_borrowed(v_vals_1733_, v_i_1734_);
v___x_1740_ = l_Lean_instHashableFVarId_hash(v_k_1738_);
v_h_1741_ = lean_uint64_to_usize(v___x_1740_);
v___x_1742_ = ((size_t)5ULL);
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_sub(v_depth_1731_, v___x_1744_);
v___x_1746_ = lean_usize_mul(v___x_1742_, v___x_1745_);
v_h_1747_ = lean_usize_shift_right(v_h_1741_, v___x_1746_);
v___x_1748_ = lean_nat_add(v_i_1734_, v___x_1743_);
lean_dec(v_i_1734_);
lean_inc(v_v_1739_);
lean_inc(v_k_1738_);
v___x_1749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1735_, v_h_1747_, v_depth_1731_, v_k_1738_, v_v_1739_);
v_i_1734_ = v___x_1748_;
v_entries_1735_ = v___x_1749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_depth_1751_, lean_object* v_keys_1752_, lean_object* v_vals_1753_, lean_object* v_i_1754_, lean_object* v_entries_1755_){
_start:
{
size_t v_depth_boxed_1756_; lean_object* v_res_1757_; 
v_depth_boxed_1756_ = lean_unbox_usize(v_depth_1751_);
lean_dec(v_depth_1751_);
v_res_1757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_depth_boxed_1756_, v_keys_1752_, v_vals_1753_, v_i_1754_, v_entries_1755_);
lean_dec_ref(v_vals_1753_);
lean_dec_ref(v_keys_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_){
_start:
{
size_t v_x_88569__boxed_1763_; size_t v_x_88570__boxed_1764_; lean_object* v_res_1765_; 
v_x_88569__boxed_1763_ = lean_unbox_usize(v_x_1759_);
lean_dec(v_x_1759_);
v_x_88570__boxed_1764_ = lean_unbox_usize(v_x_1760_);
lean_dec(v_x_1760_);
v_res_1765_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1758_, v_x_88569__boxed_1763_, v_x_88570__boxed_1764_, v_x_1761_, v_x_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_){
_start:
{
uint64_t v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; lean_object* v___x_1772_; 
v___x_1769_ = l_Lean_instHashableFVarId_hash(v_x_1767_);
v___x_1770_ = lean_uint64_to_usize(v___x_1769_);
v___x_1771_ = ((size_t)1ULL);
v___x_1772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1766_, v___x_1770_, v___x_1771_, v_x_1767_, v_x_1768_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_as_1773_, size_t v_i_1774_, size_t v_stop_1775_, lean_object* v_b_1776_){
_start:
{
lean_object* v___y_1778_; uint8_t v___x_1782_; 
v___x_1782_ = lean_usize_dec_eq(v_i_1774_, v_stop_1775_);
if (v___x_1782_ == 0)
{
lean_object* v_fvarIdToDecl_1783_; lean_object* v_decls_1784_; lean_object* v_auxDeclToFullName_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_fvarIdToDecl_1783_ = lean_ctor_get(v_b_1776_, 0);
v_decls_1784_ = lean_ctor_get(v_b_1776_, 1);
v_auxDeclToFullName_1785_ = lean_ctor_get(v_b_1776_, 2);
v___x_1786_ = lean_array_uget_borrowed(v_as_1773_, v_i_1774_);
v___x_1787_ = l_Lean_Expr_fvarId_x21(v___x_1786_);
lean_inc_ref(v_b_1776_);
v___x_1788_ = lean_local_ctx_find(v_b_1776_, v___x_1787_);
if (lean_obj_tag(v___x_1788_) == 0)
{
v___y_1778_ = v_b_1776_;
goto v___jp_1777_;
}
else
{
lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1815_; 
lean_inc(v_auxDeclToFullName_1785_);
lean_inc_ref(v_decls_1784_);
lean_inc_ref(v_fvarIdToDecl_1783_);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_b_1776_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; lean_object* v_unused_1817_; lean_object* v_unused_1818_; 
v_unused_1816_ = lean_ctor_get(v_b_1776_, 2);
lean_dec(v_unused_1816_);
v_unused_1817_ = lean_ctor_get(v_b_1776_, 1);
lean_dec(v_unused_1817_);
v_unused_1818_ = lean_ctor_get(v_b_1776_, 0);
lean_dec(v_unused_1818_);
v___x_1790_ = v_b_1776_;
v_isShared_1791_ = v_isSharedCheck_1815_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v_b_1776_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1815_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_val_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1814_; 
v_val_1792_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1794_ = v___x_1788_;
v_isShared_1795_ = v_isSharedCheck_1814_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_val_1792_);
lean_dec(v___x_1788_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1814_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1810_; lean_object* v_fvarId_1813_; 
v___x_1796_ = l_Lean_LocalDecl_type(v_val_1792_);
v___x_1797_ = l_Lean_Expr_cleanupAnnotations(v___x_1796_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l_Lean_LocalDecl_setType(v_val_1792_, v___x_1797_);
v_fvarId_1813_ = lean_ctor_get(v___x_1798_, 1);
lean_inc(v_fvarId_1813_);
v___y_1810_ = v_fvarId_1813_;
goto v___jp_1809_;
v___jp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1798_);
v___x_1803_ = v___x_1794_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1798_);
v___x_1803_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = l_Lean_PersistentArray_set___redArg(v_decls_1784_, v___y_1801_, v___x_1803_);
lean_dec(v___y_1801_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v___x_1804_);
lean_ctor_set(v___x_1790_, 0, v___y_1800_);
v___x_1806_ = v___x_1790_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___y_1800_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_auxDeclToFullName_1785_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
v___y_1778_ = v___x_1806_;
goto v___jp_1777_;
}
}
}
v___jp_1809_:
{
lean_object* v___x_1811_; lean_object* v_index_1812_; 
lean_inc_ref(v___x_1798_);
v___x_1811_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1783_, v___y_1810_, v___x_1798_);
v_index_1812_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_index_1812_);
v___y_1800_ = v___x_1811_;
v___y_1801_ = v_index_1812_;
goto v___jp_1799_;
}
}
}
}
}
else
{
return v_b_1776_;
}
v___jp_1777_:
{
size_t v___x_1779_; size_t v___x_1780_; 
v___x_1779_ = ((size_t)1ULL);
v___x_1780_ = lean_usize_add(v_i_1774_, v___x_1779_);
v_i_1774_ = v___x_1780_;
v_b_1776_ = v___y_1778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_as_1819_, lean_object* v_i_1820_, lean_object* v_stop_1821_, lean_object* v_b_1822_){
_start:
{
size_t v_i_boxed_1823_; size_t v_stop_boxed_1824_; lean_object* v_res_1825_; 
v_i_boxed_1823_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_stop_boxed_1824_ = lean_unbox_usize(v_stop_1821_);
lean_dec(v_stop_1821_);
v_res_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_as_1819_, v_i_boxed_1823_, v_stop_boxed_1824_, v_b_1822_);
lean_dec_ref(v_as_1819_);
return v_res_1825_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1828_ = l_Lean_stringToMessageData(v___x_1827_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1837_, lean_object* v_value_1838_, uint8_t v___x_1839_, uint8_t v___x_1840_, lean_object* v___x_1841_, uint8_t v___y_1842_, lean_object* v_xs_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
size_t v_sz_1851_; size_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; 
v_sz_1851_ = lean_array_size(v_xs_1843_);
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_sz_1851_, v___x_1852_, v_xs_1843_);
lean_inc(v_type_1837_);
v___x_1854_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1854_, 0, v_type_1837_);
v___x_1855_ = 2;
v___x_1856_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1854_, v___x_1855_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___y_1859_; lean_object* v___y_1895_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
if (v___y_1842_ == 0)
{
lean_object* v___x_1928_; 
v___x_1928_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1895_ = v___x_1928_;
goto v___jp_1894_;
}
else
{
lean_object* v___x_1929_; 
v___x_1929_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1895_ = v___x_1929_;
goto v___jp_1894_;
}
v___jp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___f_1864_; lean_object* v___x_1865_; 
lean_inc(v_a_1857_);
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_a_1857_);
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_box(v___x_1839_);
v___x_1863_ = lean_box(v___x_1840_);
lean_inc_ref(v___x_1853_);
v___f_1864_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1864_, 0, v_value_1838_);
lean_closure_set(v___f_1864_, 1, v___x_1860_);
lean_closure_set(v___f_1864_, 2, v___x_1862_);
lean_closure_set(v___f_1864_, 3, v___x_1861_);
lean_closure_set(v___f_1864_, 4, v___x_1853_);
lean_closure_set(v___f_1864_, 5, v___x_1863_);
v___x_1865_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg(v___y_1859_, v___f_1864_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = 1;
v___x_1868_ = l_Lean_Meta_mkForallFVars(v___x_1853_, v_a_1857_, v___x_1840_, v___x_1839_, v___x_1839_, v___x_1867_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec_ref(v___x_1853_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1877_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v_a_1869_);
lean_ctor_set(v___x_1873_, 1, v_a_1866_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1866_);
v_a_1878_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1868_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1868_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1857_);
lean_dec_ref(v___x_1853_);
v_a_1886_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1865_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1865_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
v___jp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1896_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
lean_inc_ref(v___y_1895_);
v___x_1897_ = l_Lean_stringToMessageData(v___y_1895_);
lean_inc_ref(v___x_1897_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
lean_inc(v_type_1837_);
v___x_1901_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1857_, v_type_1837_, v___x_1900_, v___y_1845_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_dec_ref_known(v___x_1901_, 1);
v___x_1902_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v___x_1897_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v___x_1899_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_inc(v_a_1857_);
v___x_1906_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1857_, v_type_1837_, v___x_1905_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_lctx_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
lean_dec_ref_known(v___x_1906_, 1);
v_lctx_1907_ = lean_ctor_get(v___y_1846_, 2);
v___x_1908_ = lean_array_get_size(v___x_1853_);
v___x_1909_ = lean_nat_dec_lt(v___x_1841_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_inc_ref(v_lctx_1907_);
v___y_1859_ = v_lctx_1907_;
goto v___jp_1858_;
}
else
{
size_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_usize_of_nat(v___x_1908_);
lean_inc_ref(v_lctx_1907_);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v___x_1853_, v___x_1852_, v___x_1910_, v_lctx_1907_);
v___y_1859_ = v___x_1911_;
goto v___jp_1858_;
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_a_1857_);
lean_dec_ref(v___x_1853_);
lean_dec(v_value_1838_);
v_a_1912_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1906_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1906_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v___x_1897_);
lean_dec(v_a_1857_);
lean_dec_ref(v___x_1853_);
lean_dec(v_value_1838_);
lean_dec(v_type_1837_);
v_a_1920_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1901_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1901_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v___x_1853_);
lean_dec(v_value_1838_);
lean_dec(v_type_1837_);
v_a_1930_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1856_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1856_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1938_, lean_object* v_value_1939_, lean_object* v___x_1940_, lean_object* v___x_1941_, lean_object* v___x_1942_, lean_object* v___y_1943_, lean_object* v_xs_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
uint8_t v___x_88866__boxed_1952_; uint8_t v___x_88867__boxed_1953_; uint8_t v___y_88869__boxed_1954_; lean_object* v_res_1955_; 
v___x_88866__boxed_1952_ = lean_unbox(v___x_1940_);
v___x_88867__boxed_1953_ = lean_unbox(v___x_1941_);
v___y_88869__boxed_1954_ = lean_unbox(v___y_1943_);
v_res_1955_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1938_, v_value_1939_, v___x_88866__boxed_1952_, v___x_88867__boxed_1953_, v___x_1942_, v___y_88869__boxed_1954_, v_xs_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___x_1942_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1956_, lean_object* v_a_1957_, lean_object* v_letOrReassign_1958_, lean_object* v_a_1959_, uint8_t v_zeta_1960_, uint8_t v___y_1961_, lean_object* v_x_1962_, uint8_t v_usedOnly_1963_, uint8_t v___x_1964_, lean_object* v_snd_1965_, lean_object* v_h_x27_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
lean_inc_ref(v_h_x27_1966_);
v___x_1975_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1956_, v_h_x27_1966_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec_ref_known(v___x_1975_, 1);
v___x_1976_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_1976_, 0, v_a_1957_);
v___x_1977_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1958_, v_a_1959_, v___x_1976_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1977_) == 0)
{
if (v_zeta_1960_ == 0)
{
if (v___y_1961_ == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; 
lean_dec_ref(v_snd_1965_);
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = lean_unsigned_to_nat(2u);
v___x_1980_ = lean_mk_empty_array_with_capacity(v___x_1979_);
v___x_1981_ = lean_array_push(v___x_1980_, v_x_1962_);
v___x_1982_ = lean_array_push(v___x_1981_, v_h_x27_1966_);
v___x_1983_ = 1;
v___x_1984_ = l_Lean_Meta_mkLetFVars(v___x_1982_, v_a_1978_, v_usedOnly_1963_, v___y_1961_, v___x_1983_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec_ref(v___x_1982_);
return v___x_1984_;
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; 
v_a_1985_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1986_ = lean_unsigned_to_nat(2u);
v___x_1987_ = lean_mk_empty_array_with_capacity(v___x_1986_);
v___x_1988_ = lean_array_push(v___x_1987_, v_x_1962_);
v___x_1989_ = lean_array_push(v___x_1988_, v_h_x27_1966_);
v___x_1990_ = 1;
v___x_1991_ = l_Lean_Meta_mkLambdaFVars(v___x_1989_, v_a_1985_, v_zeta_1960_, v___x_1964_, v_zeta_1960_, v___x_1964_, v___x_1990_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec_ref(v___x_1989_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
lean_inc_ref(v_snd_1965_);
v___x_1993_ = l_Lean_Meta_mkEqRefl(v_snd_1965_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2002_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2002_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2002_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = l_Lean_mkAppB(v_a_1992_, v_snd_1965_, v_a_1994_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_1998_);
v___x_2000_ = v___x_1996_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
else
{
lean_dec(v_a_1992_);
lean_dec_ref(v_snd_1965_);
return v___x_1993_;
}
}
else
{
lean_dec_ref(v_snd_1965_);
return v___x_1991_;
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_a_2003_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_2004_ = lean_unsigned_to_nat(2u);
v___x_2005_ = lean_mk_empty_array_with_capacity(v___x_2004_);
lean_inc_ref(v___x_2005_);
v___x_2006_ = lean_array_push(v___x_2005_, v_x_1962_);
v___x_2007_ = lean_array_push(v___x_2006_, v_h_x27_1966_);
v___x_2008_ = l_Lean_Expr_abstractM(v_a_2003_, v___x_2007_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec_ref(v___x_2007_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
lean_inc_ref(v_snd_1965_);
v___x_2010_ = l_Lean_Meta_mkEqRefl(v_snd_1965_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2021_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2021_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2021_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2015_ = lean_array_push(v___x_2005_, v_snd_1965_);
v___x_2016_ = lean_array_push(v___x_2015_, v_a_2011_);
v___x_2017_ = lean_expr_instantiate_rev(v_a_2009_, v___x_2016_);
lean_dec_ref(v___x_2016_);
lean_dec(v_a_2009_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2017_);
v___x_2019_ = v___x_2013_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
else
{
lean_dec(v_a_2009_);
lean_dec_ref(v___x_2005_);
lean_dec_ref(v_snd_1965_);
return v___x_2010_;
}
}
else
{
lean_dec_ref(v___x_2005_);
lean_dec_ref(v_snd_1965_);
return v___x_2008_;
}
}
}
else
{
lean_dec_ref(v_h_x27_1966_);
lean_dec_ref(v_snd_1965_);
lean_dec_ref(v_x_1962_);
return v___x_1977_;
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v_h_x27_1966_);
lean_dec_ref(v_snd_1965_);
lean_dec_ref(v_x_1962_);
lean_dec_ref(v_a_1959_);
lean_dec(v_letOrReassign_1958_);
lean_dec_ref(v_a_1957_);
v_a_2022_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1975_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1975_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object** _args){
lean_object* v_val_2030_ = _args[0];
lean_object* v_a_2031_ = _args[1];
lean_object* v_letOrReassign_2032_ = _args[2];
lean_object* v_a_2033_ = _args[3];
lean_object* v_zeta_2034_ = _args[4];
lean_object* v___y_2035_ = _args[5];
lean_object* v_x_2036_ = _args[6];
lean_object* v_usedOnly_2037_ = _args[7];
lean_object* v___x_2038_ = _args[8];
lean_object* v_snd_2039_ = _args[9];
lean_object* v_h_x27_2040_ = _args[10];
lean_object* v___y_2041_ = _args[11];
lean_object* v___y_2042_ = _args[12];
lean_object* v___y_2043_ = _args[13];
lean_object* v___y_2044_ = _args[14];
lean_object* v___y_2045_ = _args[15];
lean_object* v___y_2046_ = _args[16];
lean_object* v___y_2047_ = _args[17];
lean_object* v___y_2048_ = _args[18];
_start:
{
uint8_t v_zeta_boxed_2049_; uint8_t v___y_89088__boxed_2050_; uint8_t v_usedOnly_boxed_2051_; uint8_t v___x_89089__boxed_2052_; lean_object* v_res_2053_; 
v_zeta_boxed_2049_ = lean_unbox(v_zeta_2034_);
v___y_89088__boxed_2050_ = lean_unbox(v___y_2035_);
v_usedOnly_boxed_2051_ = lean_unbox(v_usedOnly_2037_);
v___x_89089__boxed_2052_ = lean_unbox(v___x_2038_);
v_res_2053_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_2030_, v_a_2031_, v_letOrReassign_2032_, v_a_2033_, v_zeta_boxed_2049_, v___y_89088__boxed_2050_, v_x_2036_, v_usedOnly_boxed_2051_, v___x_89089__boxed_2052_, v_snd_2039_, v_h_x27_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_id_2054_, lean_object* v_eq_x3f_2055_, lean_object* v_a_2056_, lean_object* v_letOrReassign_2057_, lean_object* v_a_2058_, uint8_t v_zeta_2059_, uint8_t v_usedOnly_2060_, lean_object* v_snd_2061_, uint8_t v___y_2062_, uint8_t v___x_2063_, lean_object* v_x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; 
lean_inc_ref(v_x_2064_);
v___x_2073_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_2054_, v_x_2064_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_dec_ref_known(v___x_2073_, 1);
if (lean_obj_tag(v_eq_x3f_2055_) == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_2074_, 0, v_a_2056_);
v___x_2075_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_2057_, v_a_2058_, v___x_2074_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2075_) == 0)
{
if (v_zeta_2059_ == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; 
lean_dec_ref(v_snd_2061_);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2077_ = lean_unsigned_to_nat(1u);
v___x_2078_ = lean_mk_empty_array_with_capacity(v___x_2077_);
v___x_2079_ = lean_array_push(v___x_2078_, v_x_2064_);
v___x_2080_ = 1;
v___x_2081_ = l_Lean_Meta_mkLetFVars(v___x_2079_, v_a_2076_, v_usedOnly_2060_, v_zeta_2059_, v___x_2080_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec_ref(v___x_2079_);
return v___x_2081_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_a_2082_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2083_ = lean_unsigned_to_nat(1u);
v___x_2084_ = lean_mk_empty_array_with_capacity(v___x_2083_);
v___x_2085_ = lean_array_push(v___x_2084_, v_x_2064_);
v___x_2086_ = l_Lean_Expr_abstractM(v_a_2082_, v___x_2085_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec_ref(v___x_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2095_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2095_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_expr_instantiate1(v_a_2087_, v_snd_2061_);
lean_dec_ref(v_snd_2061_);
lean_dec(v_a_2087_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
else
{
lean_dec_ref(v_snd_2061_);
return v___x_2086_;
}
}
}
else
{
lean_dec_ref(v_x_2064_);
lean_dec_ref(v_snd_2061_);
return v___x_2075_;
}
}
else
{
lean_object* v_val_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___f_2101_; lean_object* v___x_2102_; 
v_val_2096_ = lean_ctor_get(v_eq_x3f_2055_, 0);
lean_inc_n(v_val_2096_, 2);
lean_dec_ref_known(v_eq_x3f_2055_, 1);
v___x_2097_ = lean_box(v_zeta_2059_);
v___x_2098_ = lean_box(v___y_2062_);
v___x_2099_ = lean_box(v_usedOnly_2060_);
v___x_2100_ = lean_box(v___x_2063_);
lean_inc_ref(v_snd_2061_);
lean_inc_ref_n(v_x_2064_, 2);
v___f_2101_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 19, 10);
lean_closure_set(v___f_2101_, 0, v_val_2096_);
lean_closure_set(v___f_2101_, 1, v_a_2056_);
lean_closure_set(v___f_2101_, 2, v_letOrReassign_2057_);
lean_closure_set(v___f_2101_, 3, v_a_2058_);
lean_closure_set(v___f_2101_, 4, v___x_2097_);
lean_closure_set(v___f_2101_, 5, v___x_2098_);
lean_closure_set(v___f_2101_, 6, v_x_2064_);
lean_closure_set(v___f_2101_, 7, v___x_2099_);
lean_closure_set(v___f_2101_, 8, v___x_2100_);
lean_closure_set(v___f_2101_, 9, v_snd_2061_);
v___x_2102_ = l_Lean_Meta_mkEq(v_x_2064_, v_snd_2061_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = l_Lean_Meta_mkEqRefl(v_x_2064_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = l_Lean_TSyntax_getId(v_val_2096_);
lean_dec(v_val_2096_);
v___x_2107_ = 0;
v___x_2108_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_2106_, v_a_2103_, v_a_2105_, v___f_2101_, v___x_2063_, v___x_2107_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v___x_2108_;
}
else
{
lean_dec(v_a_2103_);
lean_dec_ref(v___f_2101_);
lean_dec(v_val_2096_);
return v___x_2104_;
}
}
else
{
lean_dec_ref(v___f_2101_);
lean_dec(v_val_2096_);
lean_dec_ref(v_x_2064_);
return v___x_2102_;
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v_x_2064_);
lean_dec_ref(v_snd_2061_);
lean_dec_ref(v_a_2058_);
lean_dec(v_letOrReassign_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_eq_x3f_2055_);
v_a_2109_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2073_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2073_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object** _args){
lean_object* v_id_2117_ = _args[0];
lean_object* v_eq_x3f_2118_ = _args[1];
lean_object* v_a_2119_ = _args[2];
lean_object* v_letOrReassign_2120_ = _args[3];
lean_object* v_a_2121_ = _args[4];
lean_object* v_zeta_2122_ = _args[5];
lean_object* v_usedOnly_2123_ = _args[6];
lean_object* v_snd_2124_ = _args[7];
lean_object* v___y_2125_ = _args[8];
lean_object* v___x_2126_ = _args[9];
lean_object* v_x_2127_ = _args[10];
lean_object* v___y_2128_ = _args[11];
lean_object* v___y_2129_ = _args[12];
lean_object* v___y_2130_ = _args[13];
lean_object* v___y_2131_ = _args[14];
lean_object* v___y_2132_ = _args[15];
lean_object* v___y_2133_ = _args[16];
lean_object* v___y_2134_ = _args[17];
lean_object* v___y_2135_ = _args[18];
_start:
{
uint8_t v_zeta_boxed_2136_; uint8_t v_usedOnly_boxed_2137_; uint8_t v___y_89246__boxed_2138_; uint8_t v___x_89247__boxed_2139_; lean_object* v_res_2140_; 
v_zeta_boxed_2136_ = lean_unbox(v_zeta_2122_);
v_usedOnly_boxed_2137_ = lean_unbox(v_usedOnly_2123_);
v___y_89246__boxed_2138_ = lean_unbox(v___y_2125_);
v___x_89247__boxed_2139_ = lean_unbox(v___x_2126_);
v_res_2140_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_id_2117_, v_eq_x3f_2118_, v_a_2119_, v_letOrReassign_2120_, v_a_2121_, v_zeta_boxed_2136_, v_usedOnly_boxed_2137_, v_snd_2124_, v___y_89246__boxed_2138_, v___x_89247__boxed_2139_, v_x_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(uint8_t v___x_2141_, lean_object* v_____do__lift_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2142_, v___x_2141_);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object* v___x_2153_, lean_object* v_____do__lift_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v___x_89374__boxed_2163_; lean_object* v_res_2164_; 
v___x_89374__boxed_2163_ = lean_unbox(v___x_2153_);
v_res_2164_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v___x_89374__boxed_2163_, v_____do__lift_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v_____do__lift_2154_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(lean_object* v_term_2165_, lean_object* v___x_2166_, uint8_t v___x_2167_, lean_object* v___x_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_2165_, v___x_2166_, v___x_2167_, v___x_2167_, v___x_2168_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v_term_2178_, lean_object* v___x_2179_, lean_object* v___x_2180_, lean_object* v___x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v___x_89409__boxed_2190_; lean_object* v_res_2191_; 
v___x_89409__boxed_2190_ = lean_unbox(v___x_2180_);
v_res_2191_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v_term_2178_, v___x_2179_, v___x_89409__boxed_2190_, v___x_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0(lean_object* v_stx_2192_, lean_object* v_output_2193_, lean_object* v_trees_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_lctx_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v_lctx_2202_ = lean_ctor_get(v___y_2197_, 2);
lean_inc_ref(v_lctx_2202_);
v___x_2203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2203_, 0, v_lctx_2202_);
lean_ctor_set(v___x_2203_, 1, v_stx_2192_);
lean_ctor_set(v___x_2203_, 2, v_output_2193_);
v___x_2204_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v_trees_2194_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_stx_2207_, lean_object* v_output_2208_, lean_object* v_trees_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0(v_stx_2207_, v_output_2208_, v_trees_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0(lean_object* v___y_2218_, lean_object* v_mkInfoTree_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v_a_2225_, lean_object* v_a_x3f_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v_infoState_2229_; lean_object* v_trees_2230_; lean_object* v___x_2231_; 
v___x_2228_ = lean_st_ref_get(v___y_2218_);
v_infoState_2229_ = lean_ctor_get(v___x_2228_, 8);
lean_inc_ref(v_infoState_2229_);
lean_dec(v___x_2228_);
v_trees_2230_ = lean_ctor_get(v_infoState_2229_, 2);
lean_inc_ref(v_trees_2230_);
lean_dec_ref(v_infoState_2229_);
lean_inc(v___y_2218_);
lean_inc_ref(v___y_2224_);
lean_inc(v___y_2223_);
lean_inc_ref(v___y_2222_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
v___x_2231_ = lean_apply_8(v_mkInfoTree_2219_, v_trees_2230_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2218_, lean_box(0));
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2271_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2271_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2271_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v_infoState_2237_; lean_object* v_env_2238_; lean_object* v_nextMacroScope_2239_; lean_object* v_ngen_2240_; lean_object* v_auxDeclNGen_2241_; lean_object* v_traceState_2242_; lean_object* v_cache_2243_; lean_object* v_recordedDeps_2244_; lean_object* v_messages_2245_; lean_object* v_snapshotTasks_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2270_; 
v___x_2236_ = lean_st_ref_take(v___y_2218_);
v_infoState_2237_ = lean_ctor_get(v___x_2236_, 8);
v_env_2238_ = lean_ctor_get(v___x_2236_, 0);
v_nextMacroScope_2239_ = lean_ctor_get(v___x_2236_, 1);
v_ngen_2240_ = lean_ctor_get(v___x_2236_, 2);
v_auxDeclNGen_2241_ = lean_ctor_get(v___x_2236_, 3);
v_traceState_2242_ = lean_ctor_get(v___x_2236_, 4);
v_cache_2243_ = lean_ctor_get(v___x_2236_, 5);
v_recordedDeps_2244_ = lean_ctor_get(v___x_2236_, 6);
v_messages_2245_ = lean_ctor_get(v___x_2236_, 7);
v_snapshotTasks_2246_ = lean_ctor_get(v___x_2236_, 9);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2248_ = v___x_2236_;
v_isShared_2249_ = v_isSharedCheck_2270_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_snapshotTasks_2246_);
lean_inc(v_infoState_2237_);
lean_inc(v_messages_2245_);
lean_inc(v_recordedDeps_2244_);
lean_inc(v_cache_2243_);
lean_inc(v_traceState_2242_);
lean_inc(v_auxDeclNGen_2241_);
lean_inc(v_ngen_2240_);
lean_inc(v_nextMacroScope_2239_);
lean_inc(v_env_2238_);
lean_dec(v___x_2236_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2270_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
uint8_t v_enabled_2250_; lean_object* v_assignment_2251_; lean_object* v_lazyAssignment_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2268_; 
v_enabled_2250_ = lean_ctor_get_uint8(v_infoState_2237_, sizeof(void*)*3);
v_assignment_2251_ = lean_ctor_get(v_infoState_2237_, 0);
v_lazyAssignment_2252_ = lean_ctor_get(v_infoState_2237_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_infoState_2237_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; 
v_unused_2269_ = lean_ctor_get(v_infoState_2237_, 2);
lean_dec(v_unused_2269_);
v___x_2254_ = v_infoState_2237_;
v_isShared_2255_ = v_isSharedCheck_2268_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_lazyAssignment_2252_);
lean_inc(v_assignment_2251_);
lean_dec(v_infoState_2237_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2268_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2256_ = lean_box(0);
v___x_2257_ = l_Lean_PersistentArray_push___redArg(v_a_2225_, v_a_2232_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 2, v___x_2257_);
v___x_2259_ = v___x_2254_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_assignment_2251_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_lazyAssignment_2252_);
lean_ctor_set(v_reuseFailAlloc_2267_, 2, v___x_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2267_, sizeof(void*)*3, v_enabled_2250_);
v___x_2259_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2261_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 8, v___x_2259_);
v___x_2261_ = v___x_2248_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_env_2238_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_nextMacroScope_2239_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_ngen_2240_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_auxDeclNGen_2241_);
lean_ctor_set(v_reuseFailAlloc_2266_, 4, v_traceState_2242_);
lean_ctor_set(v_reuseFailAlloc_2266_, 5, v_cache_2243_);
lean_ctor_set(v_reuseFailAlloc_2266_, 6, v_recordedDeps_2244_);
lean_ctor_set(v_reuseFailAlloc_2266_, 7, v_messages_2245_);
lean_ctor_set(v_reuseFailAlloc_2266_, 8, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2266_, 9, v_snapshotTasks_2246_);
v___x_2261_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_st_ref_put(v___y_2218_, v___x_2261_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2256_);
v___x_2264_ = v___x_2234_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2256_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v_a_2225_);
v_a_2272_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2231_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2231_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_2280_, lean_object* v_mkInfoTree_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v_a_2287_, lean_object* v_a_x3f_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0(v___y_2280_, v_mkInfoTree_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v_a_2287_, v_a_x3f_2288_);
lean_dec(v_a_x3f_2288_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2280_);
return v_res_2290_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_unsigned_to_nat(32u);
v___x_2292_ = lean_mk_empty_array_with_capacity(v___x_2291_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1(void){
_start:
{
size_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2294_ = ((size_t)5ULL);
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = lean_unsigned_to_nat(32u);
v___x_2297_ = lean_mk_empty_array_with_capacity(v___x_2296_);
v___x_2298_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0);
v___x_2299_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2297_);
lean_ctor_set(v___x_2299_, 2, v___x_2295_);
lean_ctor_set(v___x_2299_, 3, v___x_2295_);
lean_ctor_set_usize(v___x_2299_, 4, v___x_2294_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg(lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; lean_object* v_infoState_2303_; lean_object* v_trees_2304_; lean_object* v___x_2305_; lean_object* v_infoState_2306_; lean_object* v_env_2307_; lean_object* v_nextMacroScope_2308_; lean_object* v_ngen_2309_; lean_object* v_auxDeclNGen_2310_; lean_object* v_traceState_2311_; lean_object* v_cache_2312_; lean_object* v_recordedDeps_2313_; lean_object* v_messages_2314_; lean_object* v_snapshotTasks_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2336_; 
v___x_2302_ = lean_st_ref_get(v___y_2300_);
v_infoState_2303_ = lean_ctor_get(v___x_2302_, 8);
lean_inc_ref(v_infoState_2303_);
lean_dec(v___x_2302_);
v_trees_2304_ = lean_ctor_get(v_infoState_2303_, 2);
lean_inc_ref(v_trees_2304_);
lean_dec_ref(v_infoState_2303_);
v___x_2305_ = lean_st_ref_take(v___y_2300_);
v_infoState_2306_ = lean_ctor_get(v___x_2305_, 8);
v_env_2307_ = lean_ctor_get(v___x_2305_, 0);
v_nextMacroScope_2308_ = lean_ctor_get(v___x_2305_, 1);
v_ngen_2309_ = lean_ctor_get(v___x_2305_, 2);
v_auxDeclNGen_2310_ = lean_ctor_get(v___x_2305_, 3);
v_traceState_2311_ = lean_ctor_get(v___x_2305_, 4);
v_cache_2312_ = lean_ctor_get(v___x_2305_, 5);
v_recordedDeps_2313_ = lean_ctor_get(v___x_2305_, 6);
v_messages_2314_ = lean_ctor_get(v___x_2305_, 7);
v_snapshotTasks_2315_ = lean_ctor_get(v___x_2305_, 9);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2317_ = v___x_2305_;
v_isShared_2318_ = v_isSharedCheck_2336_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_snapshotTasks_2315_);
lean_inc(v_infoState_2306_);
lean_inc(v_messages_2314_);
lean_inc(v_recordedDeps_2313_);
lean_inc(v_cache_2312_);
lean_inc(v_traceState_2311_);
lean_inc(v_auxDeclNGen_2310_);
lean_inc(v_ngen_2309_);
lean_inc(v_nextMacroScope_2308_);
lean_inc(v_env_2307_);
lean_dec(v___x_2305_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2336_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
uint8_t v_enabled_2319_; lean_object* v_assignment_2320_; lean_object* v_lazyAssignment_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2334_; 
v_enabled_2319_ = lean_ctor_get_uint8(v_infoState_2306_, sizeof(void*)*3);
v_assignment_2320_ = lean_ctor_get(v_infoState_2306_, 0);
v_lazyAssignment_2321_ = lean_ctor_get(v_infoState_2306_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_infoState_2306_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v_infoState_2306_, 2);
lean_dec(v_unused_2335_);
v___x_2323_ = v_infoState_2306_;
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_lazyAssignment_2321_);
lean_inc(v_assignment_2320_);
lean_dec(v_infoState_2306_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 2, v___x_2325_);
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_assignment_2320_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_lazyAssignment_2321_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v___x_2325_);
lean_ctor_set_uint8(v_reuseFailAlloc_2333_, sizeof(void*)*3, v_enabled_2319_);
v___x_2327_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 8, v___x_2327_);
v___x_2329_ = v___x_2317_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_env_2307_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_nextMacroScope_2308_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_ngen_2309_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_auxDeclNGen_2310_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v_traceState_2311_);
lean_ctor_set(v_reuseFailAlloc_2332_, 5, v_cache_2312_);
lean_ctor_set(v_reuseFailAlloc_2332_, 6, v_recordedDeps_2313_);
lean_ctor_set(v_reuseFailAlloc_2332_, 7, v_messages_2314_);
lean_ctor_set(v_reuseFailAlloc_2332_, 8, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2332_, 9, v_snapshotTasks_2315_);
v___x_2329_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_st_ref_put(v___y_2300_, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_trees_2304_);
return v___x_2331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg(v___y_2337_);
lean_dec(v___y_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg(lean_object* v_x_2340_, lean_object* v_mkInfoTree_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2349_; lean_object* v_infoState_2350_; uint8_t v_enabled_2351_; 
v___x_2349_ = lean_st_ref_get(v___y_2347_);
v_infoState_2350_ = lean_ctor_get(v___x_2349_, 8);
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
v___x_2353_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg(v___y_2347_);
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
v___x_2362_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0(v___y_2347_, v_mkInfoTree_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v_a_2354_, v___x_2361_);
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
v___x_2383_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0(v___y_2347_, v_mkInfoTree_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v_a_2354_, v___x_2382_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_x_2400_, lean_object* v_mkInfoTree_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg(v_x_2400_, v_mkInfoTree_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg(lean_object* v_stx_2410_, lean_object* v_output_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___f_2420_; lean_object* v___x_2421_; 
v___f_2420_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2420_, 0, v_stx_2410_);
lean_closure_set(v___f_2420_, 1, v_output_2411_);
v___x_2421_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg(v_x_2412_, v___f_2420_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___boxed(lean_object* v_stx_2422_, lean_object* v_output_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg(v_stx_2422_, v_output_2423_, v_x_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(lean_object* v_beforeStx_2453_, lean_object* v_afterStx_2454_, lean_object* v_x_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_declName_x3f_2463_; lean_object* v_macroStack_2464_; uint8_t v_mayPostpone_2465_; uint8_t v_errToSorry_2466_; lean_object* v_autoBoundImplicitContext_2467_; lean_object* v_autoBoundImplicitForbidden_2468_; lean_object* v_sectionVars_2469_; lean_object* v_sectionFVars_2470_; uint8_t v_implicitLambda_2471_; uint8_t v_heedElabAsElim_2472_; uint8_t v_isNoncomputableSection_2473_; uint8_t v_isMetaSection_2474_; uint8_t v_ignoreTCFailures_2475_; uint8_t v_inPattern_2476_; lean_object* v_tacSnap_x3f_2477_; uint8_t v_saveRecAppSyntax_2478_; uint8_t v_holesAsSyntheticOpaque_2479_; lean_object* v_fixedTermElabs_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_declName_x3f_2463_ = lean_ctor_get(v___y_2456_, 0);
v_macroStack_2464_ = lean_ctor_get(v___y_2456_, 1);
v_mayPostpone_2465_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8);
v_errToSorry_2466_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_2467_ = lean_ctor_get(v___y_2456_, 2);
v_autoBoundImplicitForbidden_2468_ = lean_ctor_get(v___y_2456_, 3);
v_sectionVars_2469_ = lean_ctor_get(v___y_2456_, 4);
v_sectionFVars_2470_ = lean_ctor_get(v___y_2456_, 5);
v_implicitLambda_2471_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8 + 2);
v_heedElabAsElim_2472_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_2473_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8 + 4);
v_isMetaSection_2474_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_2475_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8 + 6);
v_inPattern_2476_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_2477_ = lean_ctor_get(v___y_2456_, 6);
v_saveRecAppSyntax_2478_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_2479_ = lean_ctor_get_uint8(v___y_2456_, sizeof(void*)*8 + 9);
v_fixedTermElabs_2480_ = lean_ctor_get(v___y_2456_, 7);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_beforeStx_2453_);
lean_ctor_set(v___x_2481_, 1, v_afterStx_2454_);
lean_inc(v_macroStack_2464_);
v___x_2482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v_macroStack_2464_);
lean_inc_ref(v_fixedTermElabs_2480_);
lean_inc(v_tacSnap_x3f_2477_);
lean_inc(v_sectionFVars_2470_);
lean_inc(v_sectionVars_2469_);
lean_inc_ref(v_autoBoundImplicitForbidden_2468_);
lean_inc(v_autoBoundImplicitContext_2467_);
lean_inc(v_declName_x3f_2463_);
v___x_2483_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_2483_, 0, v_declName_x3f_2463_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
lean_ctor_set(v___x_2483_, 2, v_autoBoundImplicitContext_2467_);
lean_ctor_set(v___x_2483_, 3, v_autoBoundImplicitForbidden_2468_);
lean_ctor_set(v___x_2483_, 4, v_sectionVars_2469_);
lean_ctor_set(v___x_2483_, 5, v_sectionFVars_2470_);
lean_ctor_set(v___x_2483_, 6, v_tacSnap_x3f_2477_);
lean_ctor_set(v___x_2483_, 7, v_fixedTermElabs_2480_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8, v_mayPostpone_2465_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 1, v_errToSorry_2466_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 2, v_implicitLambda_2471_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 3, v_heedElabAsElim_2472_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 4, v_isNoncomputableSection_2473_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 5, v_isMetaSection_2474_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 6, v_ignoreTCFailures_2475_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 7, v_inPattern_2476_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_2478_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_2479_);
lean_inc(v___y_2461_);
lean_inc_ref(v___y_2460_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v___y_2457_);
v___x_2484_ = lean_apply_7(v_x_2455_, v___x_2483_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, lean_box(0));
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___boxed(lean_object* v_beforeStx_2485_, lean_object* v_afterStx_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_beforeStx_2485_, v_afterStx_2486_, v_x_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(lean_object* v_00_u03b1_2496_, lean_object* v_beforeStx_2497_, lean_object* v_afterStx_2498_, lean_object* v_x_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_beforeStx_2497_, v_afterStx_2498_, v_x_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2508_, lean_object* v_beforeStx_2509_, lean_object* v_afterStx_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(v_00_u03b1_2508_, v_beforeStx_2509_, v_afterStx_2510_, v_x_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(lean_object* v_beforeStx_2520_, lean_object* v_afterStx_2521_, lean_object* v_x_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___f_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_inc_ref(v___y_2523_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2531_, 0, v_x_2522_);
lean_closure_set(v___f_2531_, 1, v___y_2523_);
lean_inc(v_afterStx_2521_);
lean_inc(v_beforeStx_2520_);
v___x_2532_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___boxed), 11, 4);
lean_closure_set(v___x_2532_, 0, lean_box(0));
lean_closure_set(v___x_2532_, 1, v_beforeStx_2520_);
lean_closure_set(v___x_2532_, 2, v_afterStx_2521_);
lean_closure_set(v___x_2532_, 3, v___f_2531_);
v___x_2533_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg(v_beforeStx_2520_, v_afterStx_2521_, v___x_2532_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
if (lean_obj_tag(v___x_2533_) == 0)
{
return v___x_2533_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2533_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2533_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___boxed(lean_object* v_beforeStx_2542_, lean_object* v_afterStx_2543_, lean_object* v_x_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_beforeStx_2542_, v_afterStx_2543_, v_x_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
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
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__1));
v___x_2557_ = l_String_toRawSubstring_x27(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_rhs_2579_, uint8_t v___x_2580_, lean_object* v_config_2581_, lean_object* v_a_2582_, uint8_t v___x_2583_, lean_object* v___x_2584_, lean_object* v___x_2585_, lean_object* v___x_2586_, lean_object* v___f_2587_, lean_object* v___x_2588_, lean_object* v_body_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_term_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v_ref_2606_; lean_object* v___y_2607_; lean_object* v_toCold_2613_; lean_object* v_ref_2614_; lean_object* v_quotContext_2615_; lean_object* v_currMacroScope_2616_; lean_object* v_ref_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v_eq_x3f_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_toCold_2613_ = lean_ctor_get(v___y_2595_, 0);
v_ref_2614_ = lean_ctor_get(v___y_2595_, 2);
v_quotContext_2615_ = lean_ctor_get(v_toCold_2613_, 8);
v_currMacroScope_2616_ = lean_ctor_get(v_toCold_2613_, 9);
v_ref_2617_ = l_Lean_replaceRef(v_rhs_2579_, v_ref_2614_);
v___x_2618_ = l_Lean_SourceInfo_fromRef(v_ref_2617_, v___x_2580_);
lean_dec(v_ref_2617_);
v___x_2619_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__0));
lean_inc_n(v___x_2618_, 2);
v___x_2620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2);
v_eq_x3f_2622_ = lean_ctor_get(v_config_2581_, 0);
lean_inc(v_eq_x3f_2622_);
lean_dec_ref(v_config_2581_);
v___x_2623_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__3));
lean_inc(v_currMacroScope_2616_);
lean_inc(v_quotContext_2615_);
v___x_2624_ = l_Lean_addMacroScope(v_quotContext_2615_, v___x_2623_, v_currMacroScope_2616_);
v___x_2625_ = lean_box(0);
lean_inc(v___x_2624_);
v___x_2626_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2618_);
lean_ctor_set(v___x_2626_, 1, v___x_2621_);
lean_ctor_set(v___x_2626_, 2, v___x_2624_);
lean_ctor_set(v___x_2626_, 3, v___x_2625_);
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__4));
lean_inc_ref(v___x_2586_);
lean_inc_ref(v___x_2585_);
lean_inc_ref(v___x_2584_);
v___x_2628_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2627_);
v___x_2629_ = l_Lean_Syntax_node2(v___x_2618_, v___x_2628_, v___x_2620_, v___x_2626_);
if (lean_obj_tag(v_eq_x3f_2622_) == 1)
{
lean_object* v_val_2630_; lean_object* v___x_2631_; 
v_val_2630_ = lean_ctor_get(v_eq_x3f_2622_, 0);
lean_inc(v_val_2630_);
lean_dec_ref_known(v_eq_x3f_2622_, 1);
lean_inc(v___y_2596_);
lean_inc_ref(v___y_2595_);
lean_inc(v___y_2594_);
lean_inc_ref(v___y_2593_);
lean_inc(v___y_2592_);
lean_inc_ref(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v_ref_2614_);
v___x_2631_ = lean_apply_9(v___f_2587_, v_ref_2614_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, lean_box(0));
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc_n(v_a_2632_, 23);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5));
lean_inc_ref_n(v___x_2586_, 5);
lean_inc_ref_n(v___x_2585_, 5);
lean_inc_ref_n(v___x_2584_, 5);
v___x_2634_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2633_);
v___x_2635_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6));
v___x_2636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2636_, 0, v_a_2632_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2637_, 0, v_a_2632_);
lean_ctor_set(v___x_2637_, 1, v___x_2619_);
v___x_2638_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2638_, 0, v_a_2632_);
lean_ctor_set(v___x_2638_, 1, v___x_2621_);
lean_ctor_set(v___x_2638_, 2, v___x_2624_);
lean_ctor_set(v___x_2638_, 3, v___x_2625_);
v___x_2639_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2640_, 0, v_a_2632_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_2642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2642_, 0, v_a_2632_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8));
v___x_2644_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2643_);
v___x_2645_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9));
v___x_2646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2646_, 0, v_a_2632_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
v___x_2647_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_2648_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2649_, 0, v_a_2632_);
lean_ctor_set(v___x_2649_, 1, v___x_2647_);
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2651_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2652_, 0, v_a_2632_);
lean_ctor_set(v___x_2652_, 1, v___x_2650_);
lean_ctor_set(v___x_2652_, 2, v___x_2651_);
v___x_2653_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11));
v___x_2654_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2653_);
v___x_2655_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2656_, 0, v_a_2632_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = l_Lean_Syntax_node2(v_a_2632_, v___x_2650_, v_val_2630_, v___x_2656_);
v___x_2658_ = l_Lean_Syntax_node2(v_a_2632_, v___x_2654_, v___x_2657_, v___x_2629_);
v___x_2659_ = l_Lean_Syntax_node1(v_a_2632_, v___x_2650_, v___x_2658_);
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_2661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2661_, 0, v_a_2632_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13));
v___x_2663_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14));
v___x_2665_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2664_);
v___x_2666_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_2667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2667_, 0, v_a_2632_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = l_Lean_Syntax_node1(v_a_2632_, v___x_2650_, v___x_2588_);
v___x_2669_ = l_Lean_Syntax_node1(v_a_2632_, v___x_2650_, v___x_2668_);
v___x_2670_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_2671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_a_2632_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_Syntax_node4(v_a_2632_, v___x_2665_, v___x_2667_, v___x_2669_, v___x_2671_, v_body_2589_);
v___x_2673_ = l_Lean_Syntax_node1(v_a_2632_, v___x_2650_, v___x_2672_);
v___x_2674_ = l_Lean_Syntax_node1(v_a_2632_, v___x_2663_, v___x_2673_);
lean_inc_ref(v___x_2652_);
v___x_2675_ = l_Lean_Syntax_node6(v_a_2632_, v___x_2648_, v___x_2649_, v___x_2652_, v___x_2652_, v___x_2659_, v___x_2661_, v___x_2674_);
lean_inc_ref(v___x_2642_);
lean_inc_ref(v___x_2638_);
lean_inc_ref(v___x_2637_);
v___x_2676_ = l_Lean_Syntax_node5(v_a_2632_, v___x_2644_, v___x_2646_, v___x_2637_, v___x_2638_, v___x_2642_, v___x_2675_);
v___x_2677_ = l_Lean_Syntax_node7(v_a_2632_, v___x_2634_, v___x_2636_, v___x_2637_, v___x_2638_, v___x_2640_, v_rhs_2579_, v___x_2642_, v___x_2676_);
lean_inc(v_ref_2614_);
v_term_2599_ = v___x_2677_;
v___y_2600_ = v___y_2590_;
v___y_2601_ = v___y_2591_;
v___y_2602_ = v___y_2592_;
v___y_2603_ = v___y_2593_;
v___y_2604_ = v___y_2594_;
v___y_2605_ = v___y_2595_;
v_ref_2606_ = v_ref_2614_;
v___y_2607_ = v___y_2596_;
goto v___jp_2598_;
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_val_2630_);
lean_dec(v___x_2629_);
lean_dec(v___x_2624_);
lean_dec(v_body_2589_);
lean_dec(v___x_2588_);
lean_dec_ref(v___x_2586_);
lean_dec_ref(v___x_2585_);
lean_dec_ref(v___x_2584_);
lean_dec_ref(v_a_2582_);
lean_dec(v_rhs_2579_);
v_a_2678_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2631_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2631_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
else
{
lean_object* v___x_2686_; 
lean_dec(v_eq_x3f_2622_);
lean_inc_ref(v_a_2582_);
v___x_2686_ = l_Lean_Elab_Term_exprToSyntax(v_a_2582_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2688_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
lean_inc(v___y_2596_);
lean_inc_ref(v___y_2595_);
lean_inc(v___y_2594_);
lean_inc_ref(v___y_2593_);
lean_inc(v___y_2592_);
lean_inc_ref(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v_ref_2614_);
v___x_2688_ = lean_apply_9(v___f_2587_, v_ref_2614_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, lean_box(0));
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc_n(v_a_2689_, 32);
lean_dec_ref_known(v___x_2688_, 1);
v___x_2690_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5));
lean_inc_ref_n(v___x_2586_, 8);
lean_inc_ref_n(v___x_2585_, 8);
lean_inc_ref_n(v___x_2584_, 8);
v___x_2691_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2690_);
v___x_2692_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6));
v___x_2693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2693_, 0, v_a_2689_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2694_, 0, v_a_2689_);
lean_ctor_set(v___x_2694_, 1, v___x_2619_);
v___x_2695_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2695_, 0, v_a_2689_);
lean_ctor_set(v___x_2695_, 1, v___x_2621_);
lean_ctor_set(v___x_2695_, 2, v___x_2624_);
lean_ctor_set(v___x_2695_, 3, v___x_2625_);
v___x_2696_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_a_2689_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_2699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_a_2689_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8));
v___x_2701_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2700_);
v___x_2702_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9));
v___x_2703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_a_2689_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_2705_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_a_2689_);
lean_ctor_set(v___x_2706_, 1, v___x_2704_);
v___x_2707_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2708_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2709_, 0, v_a_2689_);
lean_ctor_set(v___x_2709_, 1, v___x_2707_);
lean_ctor_set(v___x_2709_, 2, v___x_2708_);
v___x_2710_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__17));
v___x_2711_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2710_);
v___x_2712_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2713_, 0, v_a_2689_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2714_, 0, v_a_2689_);
lean_ctor_set(v___x_2714_, 1, v___x_2710_);
v___x_2715_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__18));
v___x_2716_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2715_);
v___x_2717_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__19));
v___x_2718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_a_2689_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__20));
v___x_2720_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2719_);
v___x_2721_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_2722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2722_, 0, v_a_2689_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = l_Lean_Syntax_node1(v_a_2689_, v___x_2720_, v___x_2722_);
v___x_2724_ = l_Lean_Syntax_node1(v_a_2689_, v___x_2707_, v___x_2723_);
v___x_2725_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__22));
v___x_2726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2726_, 0, v_a_2689_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
lean_inc_ref_n(v___x_2709_, 2);
v___x_2727_ = l_Lean_Syntax_node5(v_a_2689_, v___x_2716_, v___x_2718_, v___x_2724_, v___x_2709_, v___x_2726_, v_a_2687_);
v___x_2728_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2729_, 0, v_a_2689_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
lean_inc_ref(v___x_2697_);
v___x_2730_ = l_Lean_Syntax_node5(v_a_2689_, v___x_2711_, v___x_2713_, v___x_2714_, v___x_2697_, v___x_2727_, v___x_2729_);
v___x_2731_ = l_Lean_Syntax_node1(v_a_2689_, v___x_2707_, v___x_2730_);
v___x_2732_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11));
v___x_2733_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2732_);
v___x_2734_ = l_Lean_Syntax_node2(v_a_2689_, v___x_2733_, v___x_2709_, v___x_2629_);
v___x_2735_ = l_Lean_Syntax_node1(v_a_2689_, v___x_2707_, v___x_2734_);
v___x_2736_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_2737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2737_, 0, v_a_2689_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13));
v___x_2739_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2738_);
v___x_2740_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14));
v___x_2741_ = l_Lean_Name_mkStr4(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2740_);
v___x_2742_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_2743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2743_, 0, v_a_2689_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = l_Lean_Syntax_node1(v_a_2689_, v___x_2707_, v___x_2588_);
v___x_2745_ = l_Lean_Syntax_node1(v_a_2689_, v___x_2707_, v___x_2744_);
v___x_2746_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_2747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2747_, 0, v_a_2689_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = l_Lean_Syntax_node4(v_a_2689_, v___x_2741_, v___x_2743_, v___x_2745_, v___x_2747_, v_body_2589_);
v___x_2749_ = l_Lean_Syntax_node1(v_a_2689_, v___x_2707_, v___x_2748_);
v___x_2750_ = l_Lean_Syntax_node1(v_a_2689_, v___x_2739_, v___x_2749_);
v___x_2751_ = l_Lean_Syntax_node6(v_a_2689_, v___x_2705_, v___x_2706_, v___x_2709_, v___x_2731_, v___x_2735_, v___x_2737_, v___x_2750_);
lean_inc_ref(v___x_2699_);
lean_inc_ref(v___x_2695_);
lean_inc_ref(v___x_2694_);
v___x_2752_ = l_Lean_Syntax_node5(v_a_2689_, v___x_2701_, v___x_2703_, v___x_2694_, v___x_2695_, v___x_2699_, v___x_2751_);
v___x_2753_ = l_Lean_Syntax_node7(v_a_2689_, v___x_2691_, v___x_2693_, v___x_2694_, v___x_2695_, v___x_2697_, v_rhs_2579_, v___x_2699_, v___x_2752_);
lean_inc(v_ref_2614_);
v_term_2599_ = v___x_2753_;
v___y_2600_ = v___y_2590_;
v___y_2601_ = v___y_2591_;
v___y_2602_ = v___y_2592_;
v___y_2603_ = v___y_2593_;
v___y_2604_ = v___y_2594_;
v___y_2605_ = v___y_2595_;
v_ref_2606_ = v_ref_2614_;
v___y_2607_ = v___y_2596_;
goto v___jp_2598_;
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_a_2687_);
lean_dec(v___x_2629_);
lean_dec(v___x_2624_);
lean_dec(v_body_2589_);
lean_dec(v___x_2588_);
lean_dec_ref(v___x_2586_);
lean_dec_ref(v___x_2585_);
lean_dec_ref(v___x_2584_);
lean_dec_ref(v_a_2582_);
lean_dec(v_rhs_2579_);
v_a_2754_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2688_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2688_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v___x_2629_);
lean_dec(v___x_2624_);
lean_dec(v_body_2589_);
lean_dec(v___x_2588_);
lean_dec_ref(v___f_2587_);
lean_dec_ref(v___x_2586_);
lean_dec_ref(v___x_2585_);
lean_dec_ref(v___x_2584_);
lean_dec_ref(v_a_2582_);
lean_dec(v_rhs_2579_);
v_a_2762_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2686_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2686_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
v___jp_2598_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___f_2611_; lean_object* v___x_2612_; 
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_a_2582_);
v___x_2609_ = lean_box(0);
v___x_2610_ = lean_box(v___x_2583_);
lean_inc(v_term_2599_);
v___f_2611_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 12, 4);
lean_closure_set(v___f_2611_, 0, v_term_2599_);
lean_closure_set(v___f_2611_, 1, v___x_2608_);
lean_closure_set(v___f_2611_, 2, v___x_2610_);
lean_closure_set(v___f_2611_, 3, v___x_2609_);
v___x_2612_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_ref_2606_, v_term_2599_, v___f_2611_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2607_);
return v___x_2612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object** _args){
lean_object* v_rhs_2770_ = _args[0];
lean_object* v___x_2771_ = _args[1];
lean_object* v_config_2772_ = _args[2];
lean_object* v_a_2773_ = _args[3];
lean_object* v___x_2774_ = _args[4];
lean_object* v___x_2775_ = _args[5];
lean_object* v___x_2776_ = _args[6];
lean_object* v___x_2777_ = _args[7];
lean_object* v___f_2778_ = _args[8];
lean_object* v___x_2779_ = _args[9];
lean_object* v_body_2780_ = _args[10];
lean_object* v___y_2781_ = _args[11];
lean_object* v___y_2782_ = _args[12];
lean_object* v___y_2783_ = _args[13];
lean_object* v___y_2784_ = _args[14];
lean_object* v___y_2785_ = _args[15];
lean_object* v___y_2786_ = _args[16];
lean_object* v___y_2787_ = _args[17];
lean_object* v___y_2788_ = _args[18];
_start:
{
uint8_t v___x_89990__boxed_2789_; uint8_t v___x_89992__boxed_2790_; lean_object* v_res_2791_; 
v___x_89990__boxed_2789_ = lean_unbox(v___x_2771_);
v___x_89992__boxed_2790_ = lean_unbox(v___x_2774_);
v_res_2791_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_rhs_2770_, v___x_89990__boxed_2789_, v_config_2772_, v_a_2773_, v___x_89992__boxed_2790_, v___x_2775_, v___x_2776_, v___x_2777_, v___f_2778_, v___x_2779_, v_body_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
return v_res_2791_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2792_; double v___x_2793_; 
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = lean_float_of_nat(v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_cls_2796_, lean_object* v_msg_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_ref_2803_; lean_object* v___x_2804_; lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2850_; 
v_ref_2803_ = lean_ctor_get(v___y_2800_, 2);
v___x_2804_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(v_msg_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2850_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2850_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v_traceState_2810_; lean_object* v_env_2811_; lean_object* v_nextMacroScope_2812_; lean_object* v_ngen_2813_; lean_object* v_auxDeclNGen_2814_; lean_object* v_cache_2815_; lean_object* v_recordedDeps_2816_; lean_object* v_messages_2817_; lean_object* v_infoState_2818_; lean_object* v_snapshotTasks_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2849_; 
v___x_2809_ = lean_st_ref_take(v___y_2801_);
v_traceState_2810_ = lean_ctor_get(v___x_2809_, 4);
v_env_2811_ = lean_ctor_get(v___x_2809_, 0);
v_nextMacroScope_2812_ = lean_ctor_get(v___x_2809_, 1);
v_ngen_2813_ = lean_ctor_get(v___x_2809_, 2);
v_auxDeclNGen_2814_ = lean_ctor_get(v___x_2809_, 3);
v_cache_2815_ = lean_ctor_get(v___x_2809_, 5);
v_recordedDeps_2816_ = lean_ctor_get(v___x_2809_, 6);
v_messages_2817_ = lean_ctor_get(v___x_2809_, 7);
v_infoState_2818_ = lean_ctor_get(v___x_2809_, 8);
v_snapshotTasks_2819_ = lean_ctor_get(v___x_2809_, 9);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2821_ = v___x_2809_;
v_isShared_2822_ = v_isSharedCheck_2849_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_snapshotTasks_2819_);
lean_inc(v_infoState_2818_);
lean_inc(v_messages_2817_);
lean_inc(v_recordedDeps_2816_);
lean_inc(v_cache_2815_);
lean_inc(v_traceState_2810_);
lean_inc(v_auxDeclNGen_2814_);
lean_inc(v_ngen_2813_);
lean_inc(v_nextMacroScope_2812_);
lean_inc(v_env_2811_);
lean_dec(v___x_2809_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2849_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
uint64_t v_tid_2823_; lean_object* v_traces_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2848_; 
v_tid_2823_ = lean_ctor_get_uint64(v_traceState_2810_, sizeof(void*)*1);
v_traces_2824_ = lean_ctor_get(v_traceState_2810_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_traceState_2810_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2826_ = v_traceState_2810_;
v_isShared_2827_ = v_isSharedCheck_2848_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_traces_2824_);
lean_dec(v_traceState_2810_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2848_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; double v___x_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0);
v___x_2831_ = 0;
v___x_2832_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2833_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2833_, 0, v_cls_2796_);
lean_ctor_set(v___x_2833_, 1, v___x_2829_);
lean_ctor_set(v___x_2833_, 2, v___x_2832_);
lean_ctor_set_float(v___x_2833_, sizeof(void*)*3, v___x_2830_);
lean_ctor_set_float(v___x_2833_, sizeof(void*)*3 + 8, v___x_2830_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*3 + 16, v___x_2831_);
v___x_2834_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1));
v___x_2835_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v_a_2805_);
lean_ctor_set(v___x_2835_, 2, v___x_2834_);
lean_inc(v_ref_2803_);
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v_ref_2803_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = l_Lean_PersistentArray_push___redArg(v_traces_2824_, v___x_2836_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2837_);
v___x_2839_ = v___x_2826_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2837_);
lean_ctor_set_uint64(v_reuseFailAlloc_2847_, sizeof(void*)*1, v_tid_2823_);
v___x_2839_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2841_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 4, v___x_2839_);
v___x_2841_ = v___x_2821_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_env_2811_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_nextMacroScope_2812_);
lean_ctor_set(v_reuseFailAlloc_2846_, 2, v_ngen_2813_);
lean_ctor_set(v_reuseFailAlloc_2846_, 3, v_auxDeclNGen_2814_);
lean_ctor_set(v_reuseFailAlloc_2846_, 4, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2846_, 5, v_cache_2815_);
lean_ctor_set(v_reuseFailAlloc_2846_, 6, v_recordedDeps_2816_);
lean_ctor_set(v_reuseFailAlloc_2846_, 7, v_messages_2817_);
lean_ctor_set(v_reuseFailAlloc_2846_, 8, v_infoState_2818_);
lean_ctor_set(v_reuseFailAlloc_2846_, 9, v_snapshotTasks_2819_);
v___x_2841_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = lean_st_ref_put(v___y_2801_, v___x_2841_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2828_);
v___x_2844_ = v___x_2807_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2828_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_cls_2851_, lean_object* v_msg_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_2851_, v_msg_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(lean_object* v_env_2859_, lean_object* v_currNamespace_2860_, lean_object* v_openDecls_2861_, lean_object* v_n_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = l_Lean_ResolveName_resolveNamespace(v_env_2859_, v_currNamespace_2860_, v_openDecls_2861_, v_n_2862_);
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___y_2864_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed(lean_object* v_env_2867_, lean_object* v_currNamespace_2868_, lean_object* v_openDecls_2869_, lean_object* v_n_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(v_env_2867_, v_currNamespace_2868_, v_openDecls_2869_, v_n_2870_, v___y_2871_, v___y_2872_);
lean_dec_ref(v___y_2871_);
return v_res_2873_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = l_Lean_maxRecDepthErrorMessage;
v___x_2880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__4(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__3);
v___x_2882_ = l_Lean_MessageData_ofFormat(v___x_2881_);
return v___x_2882_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2883_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__4);
v___x_2884_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__2));
v___x_2885_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
lean_ctor_set(v___x_2885_, 1, v___x_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg(lean_object* v_ref_2886_){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___closed__5);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_ref_2886_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg___boxed(lean_object* v_ref_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg(v_ref_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(lean_object* v_currNamespace_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v_currNamespace_2894_);
lean_ctor_set(v___x_2897_, 1, v___y_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed(lean_object* v_currNamespace_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(v_currNamespace_2898_, v___y_2899_, v___y_2900_);
lean_dec_ref(v___y_2899_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_env_2902_, lean_object* v_declName_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
uint8_t v___x_2906_; lean_object* v_env_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; uint8_t v___x_2910_; 
v___x_2906_ = 0;
v_env_2907_ = l_Lean_Environment_setExporting(v_env_2902_, v___x_2906_);
lean_inc(v_declName_2903_);
v___x_2908_ = l_Lean_mkPrivateName(v_env_2907_, v_declName_2903_);
v___x_2909_ = 1;
lean_inc_ref(v_env_2907_);
v___x_2910_ = l_Lean_Environment_contains(v_env_2907_, v___x_2908_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; uint8_t v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2911_ = l_Lean_privateToUserName(v_declName_2903_);
v___x_2912_ = l_Lean_Environment_contains(v_env_2907_, v___x_2911_, v___x_2909_);
v___x_2913_ = lean_box(v___x_2912_);
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v___y_2905_);
return v___x_2914_;
}
else
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
lean_dec_ref(v_env_2907_);
lean_dec(v_declName_2903_);
v___x_2915_ = lean_box(v___x_2910_);
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
lean_ctor_set(v___x_2916_, 1, v___y_2905_);
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_env_2917_, lean_object* v_declName_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_env_2917_, v_declName_2918_, v___y_2919_, v___y_2920_);
lean_dec_ref(v___y_2919_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(lean_object* v_as_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
if (lean_obj_tag(v_as_2925_) == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = lean_box(0);
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
return v___x_2935_;
}
else
{
lean_object* v_toCold_2936_; lean_object* v_options_2937_; uint8_t v_hasTrace_2938_; 
v_toCold_2936_ = lean_ctor_get(v___y_2931_, 0);
v_options_2937_ = lean_ctor_get(v_toCold_2936_, 2);
v_hasTrace_2938_ = lean_ctor_get_uint8(v_options_2937_, sizeof(void*)*1);
if (v_hasTrace_2938_ == 0)
{
lean_object* v_tail_2939_; 
v_tail_2939_ = lean_ctor_get(v_as_2925_, 1);
lean_inc(v_tail_2939_);
lean_dec_ref_known(v_as_2925_, 2);
v_as_2925_ = v_tail_2939_;
goto _start;
}
else
{
lean_object* v_head_2941_; lean_object* v_tail_2942_; lean_object* v_fst_2943_; lean_object* v_snd_2944_; lean_object* v_inheritedTraceOptions_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_head_2941_ = lean_ctor_get(v_as_2925_, 0);
lean_inc(v_head_2941_);
v_tail_2942_ = lean_ctor_get(v_as_2925_, 1);
lean_inc(v_tail_2942_);
lean_dec_ref_known(v_as_2925_, 2);
v_fst_2943_ = lean_ctor_get(v_head_2941_, 0);
lean_inc_n(v_fst_2943_, 2);
v_snd_2944_ = lean_ctor_get(v_head_2941_, 1);
lean_inc(v_snd_2944_);
lean_dec(v_head_2941_);
v_inheritedTraceOptions_2945_ = lean_ctor_get(v_toCold_2936_, 11);
v___x_2946_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__1));
v___x_2947_ = l_Lean_Name_append(v___x_2946_, v_fst_2943_);
v___x_2948_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2945_, v_options_2937_, v___x_2947_);
lean_dec(v___x_2947_);
if (v___x_2948_ == 0)
{
lean_dec(v_snd_2944_);
lean_dec(v_fst_2943_);
v_as_2925_ = v_tail_2942_;
goto _start;
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_snd_2944_);
v___x_2951_ = l_Lean_MessageData_ofFormat(v___x_2950_);
v___x_2952_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_fst_2943_, v___x_2951_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_dec_ref_known(v___x_2952_, 1);
v_as_2925_ = v_tail_2942_;
goto _start;
}
else
{
lean_dec(v_tail_2942_);
return v___x_2952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___boxed(lean_object* v_as_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(v_as_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec_ref(v___y_2955_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___lam__0(lean_object* v___x_2964_, lean_object* v_entry_2965_, lean_object* v_s_2966_){
_start:
{
lean_object* v_addEntryFn_2967_; lean_object* v_importedEntries_2968_; lean_object* v_state_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2977_; 
v_addEntryFn_2967_ = lean_ctor_get(v___x_2964_, 3);
lean_inc(v_addEntryFn_2967_);
lean_dec_ref(v___x_2964_);
v_importedEntries_2968_ = lean_ctor_get(v_s_2966_, 0);
v_state_2969_ = lean_ctor_get(v_s_2966_, 1);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_s_2966_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2971_ = v_s_2966_;
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_state_2969_);
lean_inc(v_importedEntries_2968_);
lean_dec(v_s_2966_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v_state_2973_; lean_object* v___x_2975_; 
v_state_2973_ = lean_apply_2(v_addEntryFn_2967_, v_state_2969_, v_entry_2965_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 1, v_state_2973_);
v___x_2975_ = v___x_2971_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_importedEntries_2968_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_state_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___redArg(lean_object* v_keys_2978_, lean_object* v_i_2979_, lean_object* v_k_2980_){
_start:
{
lean_object* v___x_2981_; uint8_t v___x_2982_; 
v___x_2981_ = lean_array_get_size(v_keys_2978_);
v___x_2982_ = lean_nat_dec_lt(v_i_2979_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_dec(v_i_2979_);
return v___x_2982_;
}
else
{
lean_object* v_k_x27_2983_; uint8_t v___x_2984_; 
v_k_x27_2983_ = lean_array_fget_borrowed(v_keys_2978_, v_i_2979_);
v___x_2984_ = l_Lean_instBEqExtraModUse_beq(v_k_2980_, v_k_x27_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_unsigned_to_nat(1u);
v___x_2986_ = lean_nat_add(v_i_2979_, v___x_2985_);
lean_dec(v_i_2979_);
v_i_2979_ = v___x_2986_;
goto _start;
}
else
{
lean_dec(v_i_2979_);
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___redArg___boxed(lean_object* v_keys_2988_, lean_object* v_i_2989_, lean_object* v_k_2990_){
_start:
{
uint8_t v_res_2991_; lean_object* v_r_2992_; 
v_res_2991_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___redArg(v_keys_2988_, v_i_2989_, v_k_2990_);
lean_dec_ref(v_k_2990_);
lean_dec_ref(v_keys_2988_);
v_r_2992_ = lean_box(v_res_2991_);
return v_r_2992_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___redArg(lean_object* v_x_2993_, size_t v_x_2994_, lean_object* v_x_2995_){
_start:
{
if (lean_obj_tag(v_x_2993_) == 0)
{
lean_object* v_es_2996_; lean_object* v___x_2997_; size_t v___x_2998_; size_t v___x_2999_; lean_object* v_j_3000_; lean_object* v___x_3001_; 
v_es_2996_ = lean_ctor_get(v_x_2993_, 0);
v___x_2997_ = lean_box(2);
v___x_2998_ = ((size_t)31ULL);
v___x_2999_ = lean_usize_land(v_x_2994_, v___x_2998_);
v_j_3000_ = lean_usize_to_nat(v___x_2999_);
v___x_3001_ = lean_array_get_borrowed(v___x_2997_, v_es_2996_, v_j_3000_);
lean_dec(v_j_3000_);
switch(lean_obj_tag(v___x_3001_))
{
case 0:
{
lean_object* v_key_3002_; uint8_t v___x_3003_; 
v_key_3002_ = lean_ctor_get(v___x_3001_, 0);
v___x_3003_ = l_Lean_instBEqExtraModUse_beq(v_x_2995_, v_key_3002_);
return v___x_3003_;
}
case 1:
{
lean_object* v_node_3004_; size_t v___x_3005_; size_t v___x_3006_; 
v_node_3004_ = lean_ctor_get(v___x_3001_, 0);
v___x_3005_ = ((size_t)5ULL);
v___x_3006_ = lean_usize_shift_right(v_x_2994_, v___x_3005_);
v_x_2993_ = v_node_3004_;
v_x_2994_ = v___x_3006_;
goto _start;
}
default: 
{
uint8_t v___x_3008_; 
v___x_3008_ = 0;
return v___x_3008_;
}
}
}
else
{
lean_object* v_ks_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v_ks_3009_ = lean_ctor_get(v_x_2993_, 0);
v___x_3010_ = lean_unsigned_to_nat(0u);
v___x_3011_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___redArg(v_ks_3009_, v___x_3010_, v_x_2995_);
return v___x_3011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___redArg___boxed(lean_object* v_x_3012_, lean_object* v_x_3013_, lean_object* v_x_3014_){
_start:
{
size_t v_x_90675__boxed_3015_; uint8_t v_res_3016_; lean_object* v_r_3017_; 
v_x_90675__boxed_3015_ = lean_unbox_usize(v_x_3013_);
lean_dec(v_x_3013_);
v_res_3016_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___redArg(v_x_3012_, v_x_90675__boxed_3015_, v_x_3014_);
lean_dec_ref(v_x_3014_);
lean_dec_ref(v_x_3012_);
v_r_3017_ = lean_box(v_res_3016_);
return v_r_3017_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___redArg(lean_object* v_x_3018_, lean_object* v_x_3019_){
_start:
{
uint64_t v___x_3020_; size_t v___x_3021_; uint8_t v___x_3022_; 
v___x_3020_ = l_Lean_instHashableExtraModUse_hash(v_x_3019_);
v___x_3021_ = lean_uint64_to_usize(v___x_3020_);
v___x_3022_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___redArg(v_x_3018_, v___x_3021_, v_x_3019_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_3023_, lean_object* v_x_3024_){
_start:
{
uint8_t v_res_3025_; lean_object* v_r_3026_; 
v_res_3025_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___redArg(v_x_3023_, v_x_3024_);
lean_dec_ref(v_x_3024_);
lean_dec_ref(v_x_3023_);
v_r_3026_ = lean_box(v_res_3025_);
return v_r_3026_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__0(void){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3027_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__1(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__0);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg(){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__1);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___boxed(lean_object* v___dummy_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg();
return v_res_3033_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg___closed__0);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
return v___x_3037_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26___redArg();
return v___x_3038_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0);
v___x_3040_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2);
v___x_3041_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set(v___x_3041_, 1, v___x_3039_);
lean_ctor_set(v___x_3041_, 2, v___x_3039_);
lean_ctor_set(v___x_3041_, 3, v___x_3039_);
lean_ctor_set(v___x_3041_, 4, v___x_3039_);
lean_ctor_set(v___x_3041_, 5, v___x_3039_);
lean_ctor_set(v___x_3041_, 6, v___x_3039_);
return v___x_3041_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_3042_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__7));
v___x_3048_ = l_Lean_stringToMessageData(v___x_3047_);
return v___x_3048_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__9));
v___x_3051_ = l_Lean_stringToMessageData(v___x_3050_);
return v___x_3051_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_3053_ = l_Lean_stringToMessageData(v___x_3052_);
return v___x_3053_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v_cls_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_cls_3054_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__6));
v___x_3055_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__1));
v___x_3056_ = l_Lean_Name_append(v___x_3055_, v_cls_3054_);
return v___x_3056_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__13));
v___x_3059_ = l_Lean_stringToMessageData(v___x_3058_);
return v___x_3059_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__15));
v___x_3062_ = l_Lean_stringToMessageData(v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17(lean_object* v_mod_3067_, uint8_t v_isMeta_3068_, lean_object* v_hint_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v_env_3112_; uint8_t v_isExporting_3113_; lean_object* v_entry_3114_; lean_object* v___x_3115_; lean_object* v_env_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3110_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4);
v___x_3111_ = lean_st_ref_get(v___y_3076_);
v_env_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc_ref(v_env_3112_);
lean_dec(v___x_3111_);
v_isExporting_3113_ = lean_ctor_get_uint8(v_env_3112_, sizeof(void*)*13);
lean_dec_ref(v_env_3112_);
lean_inc(v_mod_3067_);
v_entry_3114_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3114_, 0, v_mod_3067_);
lean_ctor_set_uint8(v_entry_3114_, sizeof(void*)*1, v_isExporting_3113_);
lean_ctor_set_uint8(v_entry_3114_, sizeof(void*)*1 + 1, v_isMeta_3068_);
v___x_3115_ = lean_st_ref_get(v___y_3076_);
v_env_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc_ref(v_env_3116_);
lean_dec(v___x_3115_);
v___x_3117_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3118_ = lean_box(1);
v___x_3119_ = lean_box(0);
v___x_3120_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3110_, v___x_3117_, v_env_3116_, v___x_3118_, v___x_3119_);
v___x_3121_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___redArg(v___x_3120_, v_entry_3114_);
lean_dec(v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v_toCold_3122_; lean_object* v_options_3123_; lean_object* v_inheritedTraceOptions_3124_; uint8_t v_hasTrace_3125_; lean_object* v___f_3126_; uint8_t v___x_3127_; lean_object* v___y_3129_; lean_object* v___y_3130_; 
v_toCold_3122_ = lean_ctor_get(v___y_3075_, 0);
v_options_3123_ = lean_ctor_get(v_toCold_3122_, 2);
v_inheritedTraceOptions_3124_ = lean_ctor_get(v_toCold_3122_, 11);
v_hasTrace_3125_ = lean_ctor_get_uint8(v_options_3123_, sizeof(void*)*1);
v___f_3126_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___lam__0), 3, 2);
lean_closure_set(v___f_3126_, 0, v___x_3117_);
lean_closure_set(v___f_3126_, 1, v_entry_3114_);
v___x_3127_ = 1;
if (v_hasTrace_3125_ == 0)
{
lean_dec(v_hint_3069_);
lean_dec(v_mod_3067_);
v___y_3129_ = v___y_3074_;
v___y_3130_ = v___y_3076_;
goto v___jp_3128_;
}
else
{
lean_object* v_cls_3157_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v_cls_3157_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__6));
v___x_3177_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12);
v___x_3178_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3124_, v_options_3123_, v___x_3177_);
if (v___x_3178_ == 0)
{
lean_dec(v_hint_3069_);
lean_dec(v_mod_3067_);
v___y_3129_ = v___y_3074_;
v___y_3130_ = v___y_3076_;
goto v___jp_3128_;
}
else
{
lean_object* v___x_3179_; lean_object* v___y_3181_; 
v___x_3179_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14);
if (v_isExporting_3113_ == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__19));
v___y_3181_ = v___x_3188_;
goto v___jp_3180_;
}
else
{
lean_object* v___x_3189_; 
v___x_3189_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__20));
v___y_3181_ = v___x_3189_;
goto v___jp_3180_;
}
v___jp_3180_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_inc_ref(v___y_3181_);
v___x_3182_ = l_Lean_stringToMessageData(v___y_3181_);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3179_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16);
v___x_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
if (v_isMeta_3068_ == 0)
{
lean_object* v___x_3186_; 
v___x_3186_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__17));
v___y_3164_ = v___x_3185_;
v___y_3165_ = v___x_3186_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3187_; 
v___x_3187_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__18));
v___y_3164_ = v___x_3185_;
v___y_3165_ = v___x_3187_;
goto v___jp_3163_;
}
}
}
v___jp_3158_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___y_3159_);
lean_ctor_set(v___x_3161_, 1, v___y_3160_);
v___x_3162_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_3157_, v___x_3161_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_dec_ref_known(v___x_3162_, 1);
v___y_3129_ = v___y_3074_;
v___y_3130_ = v___y_3076_;
goto v___jp_3128_;
}
else
{
lean_dec_ref(v___f_3126_);
return v___x_3162_;
}
}
v___jp_3163_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
lean_inc_ref(v___y_3165_);
v___x_3166_ = l_Lean_stringToMessageData(v___y_3165_);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___y_3164_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8);
v___x_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = l_Lean_MessageData_ofName(v_mod_3067_);
v___x_3171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3169_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = l_Lean_Name_isAnonymous(v_hint_3069_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10);
v___x_3174_ = l_Lean_MessageData_ofName(v_hint_3069_);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___y_3159_ = v___x_3171_;
v___y_3160_ = v___x_3175_;
goto v___jp_3158_;
}
else
{
lean_object* v___x_3176_; 
lean_dec(v_hint_3069_);
v___x_3176_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11);
v___y_3159_ = v___x_3171_;
v___y_3160_ = v___x_3176_;
goto v___jp_3158_;
}
}
}
v___jp_3128_:
{
lean_object* v___x_3131_; lean_object* v_toEnvExtension_3132_; uint8_t v_logWrites_3133_; 
v___x_3131_ = lean_st_ref_take(v___y_3130_);
v_toEnvExtension_3132_ = lean_ctor_get(v___x_3117_, 0);
v_logWrites_3133_ = lean_ctor_get_uint8(v_toEnvExtension_3132_, sizeof(void*)*6);
if (v_logWrites_3133_ == 0)
{
lean_object* v_env_3134_; lean_object* v_nextMacroScope_3135_; lean_object* v_ngen_3136_; lean_object* v_auxDeclNGen_3137_; lean_object* v_traceState_3138_; lean_object* v_recordedDeps_3139_; lean_object* v_messages_3140_; lean_object* v_infoState_3141_; lean_object* v_snapshotTasks_3142_; lean_object* v_asyncMode_3143_; lean_object* v___x_3144_; 
v_env_3134_ = lean_ctor_get(v___x_3131_, 0);
lean_inc_ref(v_env_3134_);
v_nextMacroScope_3135_ = lean_ctor_get(v___x_3131_, 1);
lean_inc(v_nextMacroScope_3135_);
v_ngen_3136_ = lean_ctor_get(v___x_3131_, 2);
lean_inc_ref(v_ngen_3136_);
v_auxDeclNGen_3137_ = lean_ctor_get(v___x_3131_, 3);
lean_inc_ref(v_auxDeclNGen_3137_);
v_traceState_3138_ = lean_ctor_get(v___x_3131_, 4);
lean_inc_ref(v_traceState_3138_);
v_recordedDeps_3139_ = lean_ctor_get(v___x_3131_, 6);
lean_inc_ref(v_recordedDeps_3139_);
v_messages_3140_ = lean_ctor_get(v___x_3131_, 7);
lean_inc_ref(v_messages_3140_);
v_infoState_3141_ = lean_ctor_get(v___x_3131_, 8);
lean_inc_ref(v_infoState_3141_);
v_snapshotTasks_3142_ = lean_ctor_get(v___x_3131_, 9);
lean_inc_ref(v_snapshotTasks_3142_);
lean_dec(v___x_3131_);
v_asyncMode_3143_ = lean_ctor_get(v_toEnvExtension_3132_, 2);
lean_inc_ref(v_toEnvExtension_3132_);
v___x_3144_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3132_, v_env_3134_, v___f_3126_, v_asyncMode_3143_, v___x_3119_, v___x_3127_);
v___y_3079_ = v_traceState_3138_;
v___y_3080_ = v_nextMacroScope_3135_;
v___y_3081_ = v___y_3129_;
v___y_3082_ = v_auxDeclNGen_3137_;
v___y_3083_ = v_snapshotTasks_3142_;
v___y_3084_ = v_messages_3140_;
v___y_3085_ = v_recordedDeps_3139_;
v___y_3086_ = v_ngen_3136_;
v___y_3087_ = v___y_3130_;
v___y_3088_ = v_infoState_3141_;
v___y_3089_ = v___x_3144_;
goto v___jp_3078_;
}
else
{
lean_object* v_env_3145_; lean_object* v_nextMacroScope_3146_; lean_object* v_ngen_3147_; lean_object* v_auxDeclNGen_3148_; lean_object* v_traceState_3149_; lean_object* v_recordedDeps_3150_; lean_object* v_messages_3151_; lean_object* v_infoState_3152_; lean_object* v_snapshotTasks_3153_; lean_object* v_asyncMode_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v_env_3145_ = lean_ctor_get(v___x_3131_, 0);
lean_inc_ref(v_env_3145_);
v_nextMacroScope_3146_ = lean_ctor_get(v___x_3131_, 1);
lean_inc(v_nextMacroScope_3146_);
v_ngen_3147_ = lean_ctor_get(v___x_3131_, 2);
lean_inc_ref(v_ngen_3147_);
v_auxDeclNGen_3148_ = lean_ctor_get(v___x_3131_, 3);
lean_inc_ref(v_auxDeclNGen_3148_);
v_traceState_3149_ = lean_ctor_get(v___x_3131_, 4);
lean_inc_ref(v_traceState_3149_);
v_recordedDeps_3150_ = lean_ctor_get(v___x_3131_, 6);
lean_inc_ref(v_recordedDeps_3150_);
v_messages_3151_ = lean_ctor_get(v___x_3131_, 7);
lean_inc_ref(v_messages_3151_);
v_infoState_3152_ = lean_ctor_get(v___x_3131_, 8);
lean_inc_ref(v_infoState_3152_);
v_snapshotTasks_3153_ = lean_ctor_get(v___x_3131_, 9);
lean_inc_ref(v_snapshotTasks_3153_);
lean_dec(v___x_3131_);
v_asyncMode_3154_ = lean_ctor_get(v_toEnvExtension_3132_, 2);
lean_inc_ref_n(v_toEnvExtension_3132_, 2);
v___x_3155_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3132_, v_env_3145_);
lean_dec_ref(v_env_3145_);
v___x_3156_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3132_, v___x_3155_, v___f_3126_, v_asyncMode_3154_, v___x_3119_, v___x_3127_);
v___y_3079_ = v_traceState_3149_;
v___y_3080_ = v_nextMacroScope_3146_;
v___y_3081_ = v___y_3129_;
v___y_3082_ = v_auxDeclNGen_3148_;
v___y_3083_ = v_snapshotTasks_3153_;
v___y_3084_ = v_messages_3151_;
v___y_3085_ = v_recordedDeps_3150_;
v___y_3086_ = v_ngen_3147_;
v___y_3087_ = v___y_3130_;
v___y_3088_ = v_infoState_3152_;
v___y_3089_ = v___x_3156_;
goto v___jp_3078_;
}
}
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_dec_ref_known(v_entry_3114_, 1);
lean_dec(v_hint_3069_);
lean_dec(v_mod_3067_);
v___x_3190_ = lean_box(0);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
v___jp_3078_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v_mctx_3094_; lean_object* v_zetaDeltaFVarIds_3095_; lean_object* v_postponed_3096_; lean_object* v_diag_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3108_; 
v___x_3090_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1);
v___x_3091_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3091_, 0, v___y_3089_);
lean_ctor_set(v___x_3091_, 1, v___y_3080_);
lean_ctor_set(v___x_3091_, 2, v___y_3086_);
lean_ctor_set(v___x_3091_, 3, v___y_3082_);
lean_ctor_set(v___x_3091_, 4, v___y_3079_);
lean_ctor_set(v___x_3091_, 5, v___x_3090_);
lean_ctor_set(v___x_3091_, 6, v___y_3085_);
lean_ctor_set(v___x_3091_, 7, v___y_3084_);
lean_ctor_set(v___x_3091_, 8, v___y_3088_);
lean_ctor_set(v___x_3091_, 9, v___y_3083_);
v___x_3092_ = lean_st_ref_put(v___y_3087_, v___x_3091_);
v___x_3093_ = lean_st_ref_take(v___y_3081_);
v_mctx_3094_ = lean_ctor_get(v___x_3093_, 0);
v_zetaDeltaFVarIds_3095_ = lean_ctor_get(v___x_3093_, 2);
v_postponed_3096_ = lean_ctor_get(v___x_3093_, 3);
v_diag_3097_ = lean_ctor_get(v___x_3093_, 4);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; 
v_unused_3109_ = lean_ctor_get(v___x_3093_, 1);
lean_dec(v_unused_3109_);
v___x_3099_ = v___x_3093_;
v_isShared_3100_ = v_isSharedCheck_3108_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_diag_3097_);
lean_inc(v_postponed_3096_);
lean_inc(v_zetaDeltaFVarIds_3095_);
lean_inc(v_mctx_3094_);
lean_dec(v___x_3093_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3108_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3101_ = lean_box(0);
v___x_3102_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 1, v___x_3102_);
v___x_3104_ = v___x_3099_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_mctx_3094_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3107_, 2, v_zetaDeltaFVarIds_3095_);
lean_ctor_set(v_reuseFailAlloc_3107_, 3, v_postponed_3096_);
lean_ctor_set(v_reuseFailAlloc_3107_, 4, v_diag_3097_);
v___x_3104_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = lean_st_ref_put(v___y_3081_, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3101_);
return v___x_3106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___boxed(lean_object* v_mod_3192_, lean_object* v_isMeta_3193_, lean_object* v_hint_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
uint8_t v_isMeta_boxed_3203_; lean_object* v_res_3204_; 
v_isMeta_boxed_3203_ = lean_unbox(v_isMeta_3193_);
v_res_3204_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17(v_mod_3192_, v_isMeta_boxed_3203_, v_hint_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec_ref(v___y_3195_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18(lean_object* v___x_3205_, lean_object* v_declName_3206_, lean_object* v_as_3207_, size_t v_sz_3208_, size_t v_i_3209_, lean_object* v_b_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
uint8_t v___x_3219_; 
v___x_3219_ = lean_usize_dec_lt(v_i_3209_, v_sz_3208_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
lean_dec(v_declName_3206_);
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v_b_3210_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v_modules_3222_; lean_object* v___x_3223_; lean_object* v_a_3224_; lean_object* v___x_3225_; lean_object* v_toImport_3226_; lean_object* v_module_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; lean_object* v___x_3230_; 
v___x_3221_ = l_Lean_Environment_header(v___x_3205_);
v_modules_3222_ = lean_ctor_get(v___x_3221_, 3);
lean_inc_ref(v_modules_3222_);
lean_dec_ref(v___x_3221_);
v___x_3223_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3224_ = lean_array_uget_borrowed(v_as_3207_, v_i_3209_);
v___x_3225_ = lean_array_get(v___x_3223_, v_modules_3222_, v_a_3224_);
lean_dec_ref(v_modules_3222_);
v_toImport_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc_ref(v_toImport_3226_);
lean_dec(v___x_3225_);
v_module_3227_ = lean_ctor_get(v_toImport_3226_, 0);
lean_inc(v_module_3227_);
lean_dec_ref(v_toImport_3226_);
v___x_3228_ = lean_box(0);
v___x_3229_ = 0;
lean_inc(v_declName_3206_);
v___x_3230_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17(v_module_3227_, v___x_3229_, v_declName_3206_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
if (lean_obj_tag(v___x_3230_) == 0)
{
size_t v___x_3231_; size_t v___x_3232_; 
lean_dec_ref_known(v___x_3230_, 1);
v___x_3231_ = ((size_t)1ULL);
v___x_3232_ = lean_usize_add(v_i_3209_, v___x_3231_);
v_i_3209_ = v___x_3232_;
v_b_3210_ = v___x_3228_;
goto _start;
}
else
{
lean_dec(v_declName_3206_);
return v___x_3230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18___boxed(lean_object* v___x_3234_, lean_object* v_declName_3235_, lean_object* v_as_3236_, lean_object* v_sz_3237_, lean_object* v_i_3238_, lean_object* v_b_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
size_t v_sz_boxed_3248_; size_t v_i_boxed_3249_; lean_object* v_res_3250_; 
v_sz_boxed_3248_ = lean_unbox_usize(v_sz_3237_);
lean_dec(v_sz_3237_);
v_i_boxed_3249_ = lean_unbox_usize(v_i_3238_);
lean_dec(v_i_3238_);
v_res_3250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18(v___x_3234_, v_declName_3235_, v_as_3236_, v_sz_boxed_3248_, v_i_boxed_3249_, v_b_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec_ref(v_as_3236_);
lean_dec_ref(v___x_3234_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25___redArg(lean_object* v_a_3251_, lean_object* v_x_3252_){
_start:
{
if (lean_obj_tag(v_x_3252_) == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_box(0);
return v___x_3253_;
}
else
{
lean_object* v_key_3254_; lean_object* v_value_3255_; lean_object* v_tail_3256_; uint8_t v___x_3257_; 
v_key_3254_ = lean_ctor_get(v_x_3252_, 0);
v_value_3255_ = lean_ctor_get(v_x_3252_, 1);
v_tail_3256_ = lean_ctor_get(v_x_3252_, 2);
v___x_3257_ = lean_name_eq(v_key_3254_, v_a_3251_);
if (v___x_3257_ == 0)
{
v_x_3252_ = v_tail_3256_;
goto _start;
}
else
{
lean_object* v___x_3259_; 
lean_inc(v_value_3255_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_value_3255_);
return v___x_3259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25___redArg___boxed(lean_object* v_a_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25___redArg(v_a_3260_, v_x_3261_);
lean_dec(v_x_3261_);
lean_dec(v_a_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg(lean_object* v_m_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v_buckets_3265_; lean_object* v___x_3266_; uint64_t v___y_3268_; 
v_buckets_3265_ = lean_ctor_get(v_m_3263_, 1);
v___x_3266_ = lean_array_get_size(v_buckets_3265_);
if (lean_obj_tag(v_a_3264_) == 0)
{
uint64_t v___x_3282_; 
v___x_3282_ = 1723ULL;
v___y_3268_ = v___x_3282_;
goto v___jp_3267_;
}
else
{
uint64_t v_hash_3283_; 
v_hash_3283_ = lean_ctor_get_uint64(v_a_3264_, sizeof(void*)*2);
v___y_3268_ = v_hash_3283_;
goto v___jp_3267_;
}
v___jp_3267_:
{
uint64_t v___x_3269_; uint64_t v___x_3270_; uint64_t v_fold_3271_; uint64_t v___x_3272_; uint64_t v___x_3273_; uint64_t v___x_3274_; size_t v___x_3275_; size_t v___x_3276_; size_t v___x_3277_; size_t v___x_3278_; size_t v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3269_ = 32ULL;
v___x_3270_ = lean_uint64_shift_right(v___y_3268_, v___x_3269_);
v_fold_3271_ = lean_uint64_xor(v___y_3268_, v___x_3270_);
v___x_3272_ = 16ULL;
v___x_3273_ = lean_uint64_shift_right(v_fold_3271_, v___x_3272_);
v___x_3274_ = lean_uint64_xor(v_fold_3271_, v___x_3273_);
v___x_3275_ = lean_uint64_to_usize(v___x_3274_);
v___x_3276_ = lean_usize_of_nat(v___x_3266_);
v___x_3277_ = ((size_t)1ULL);
v___x_3278_ = lean_usize_sub(v___x_3276_, v___x_3277_);
v___x_3279_ = lean_usize_land(v___x_3275_, v___x_3278_);
v___x_3280_ = lean_array_uget_borrowed(v_buckets_3265_, v___x_3279_);
v___x_3281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25___redArg(v_a_3264_, v___x_3280_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg___boxed(lean_object* v_m_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg(v_m_3284_, v_a_3285_);
lean_dec(v_a_3285_);
lean_dec_ref(v_m_3284_);
return v_res_3286_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0(void){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Std_HashMap_instInhabited___redArg();
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(lean_object* v_declName_3290_, uint8_t v_isMeta_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v_env_3305_; lean_object* v___y_3307_; lean_object* v___x_3320_; 
v___x_3300_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0);
v___x_3301_ = lean_st_ref_get(v___y_3298_);
v_env_3305_ = lean_ctor_get(v___x_3301_, 0);
lean_inc_ref(v_env_3305_);
lean_dec(v___x_3301_);
v___x_3320_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3305_, v_declName_3290_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_dec_ref(v_env_3305_);
lean_dec(v_declName_3290_);
goto v___jp_3302_;
}
else
{
lean_object* v_val_3321_; lean_object* v___x_3322_; lean_object* v_modules_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; 
v_val_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_val_3321_);
lean_dec_ref_known(v___x_3320_, 1);
v___x_3322_ = l_Lean_Environment_header(v_env_3305_);
v_modules_3323_ = lean_ctor_get(v___x_3322_, 3);
lean_inc_ref(v_modules_3323_);
lean_dec_ref(v___x_3322_);
v___x_3324_ = lean_array_get_size(v_modules_3323_);
v___x_3325_ = lean_nat_dec_lt(v_val_3321_, v___x_3324_);
if (v___x_3325_ == 0)
{
lean_dec_ref(v_modules_3323_);
lean_dec(v_val_3321_);
lean_dec_ref(v_env_3305_);
lean_dec(v_declName_3290_);
goto v___jp_3302_;
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___y_3329_; 
v___x_3326_ = lean_array_fget(v_modules_3323_, v_val_3321_);
lean_dec(v_val_3321_);
lean_dec_ref(v_modules_3323_);
v___x_3327_ = lean_st_ref_get(v___y_3298_);
if (v_isMeta_3291_ == 0)
{
lean_dec(v___x_3327_);
v___y_3329_ = v_isMeta_3291_;
goto v___jp_3328_;
}
else
{
lean_object* v_env_3340_; uint8_t v___x_3341_; 
v_env_3340_ = lean_ctor_get(v___x_3327_, 0);
lean_inc_ref(v_env_3340_);
lean_dec(v___x_3327_);
lean_inc(v_declName_3290_);
v___x_3341_ = l_Lean_isMarkedMeta(v_env_3340_, v_declName_3290_);
if (v___x_3341_ == 0)
{
v___y_3329_ = v_isMeta_3291_;
goto v___jp_3328_;
}
else
{
uint8_t v___x_3342_; 
v___x_3342_ = 0;
v___y_3329_ = v___x_3342_;
goto v___jp_3328_;
}
}
v___jp_3328_:
{
lean_object* v_toImport_3330_; lean_object* v_module_3331_; lean_object* v___x_3332_; 
v_toImport_3330_ = lean_ctor_get(v___x_3326_, 0);
lean_inc_ref(v_toImport_3330_);
lean_dec(v___x_3326_);
v_module_3331_ = lean_ctor_get(v_toImport_3330_, 0);
lean_inc(v_module_3331_);
lean_dec_ref(v_toImport_3330_);
lean_inc(v_declName_3290_);
v___x_3332_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17(v_module_3331_, v___y_3329_, v_declName_3290_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
lean_dec_ref_known(v___x_3332_, 1);
v___x_3333_ = l_Lean_indirectModUseExt;
v___x_3334_ = lean_box(1);
v___x_3335_ = lean_box(0);
lean_inc_ref(v_env_3305_);
v___x_3336_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3300_, v___x_3333_, v_env_3305_, v___x_3334_, v___x_3335_);
v___x_3337_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg(v___x_3336_, v_declName_3290_);
lean_dec(v___x_3336_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v___x_3338_; 
v___x_3338_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__1));
v___y_3307_ = v___x_3338_;
goto v___jp_3306_;
}
else
{
lean_object* v_val_3339_; 
v_val_3339_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_val_3339_);
lean_dec_ref_known(v___x_3337_, 1);
v___y_3307_ = v_val_3339_;
goto v___jp_3306_;
}
}
else
{
lean_dec_ref(v_env_3305_);
lean_dec(v_declName_3290_);
return v___x_3332_;
}
}
}
}
v___jp_3302_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
return v___x_3304_;
}
v___jp_3306_:
{
lean_object* v___x_3308_; size_t v_sz_3309_; size_t v___x_3310_; lean_object* v___x_3311_; 
v___x_3308_ = lean_box(0);
v_sz_3309_ = lean_array_size(v___y_3307_);
v___x_3310_ = ((size_t)0ULL);
v___x_3311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18(v_env_3305_, v_declName_3290_, v___y_3307_, v_sz_3309_, v___x_3310_, v___x_3308_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec_ref(v___y_3307_);
lean_dec_ref(v_env_3305_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3318_ == 0)
{
lean_object* v_unused_3319_; 
v_unused_3319_ = lean_ctor_get(v___x_3311_, 0);
lean_dec(v_unused_3319_);
v___x_3313_ = v___x_3311_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_dec(v___x_3311_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v___x_3308_);
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3308_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
return v___x_3311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___boxed(lean_object* v_declName_3343_, lean_object* v_isMeta_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v_isMeta_boxed_3353_; lean_object* v_res_3354_; 
v_isMeta_boxed_3353_ = lean_unbox(v_isMeta_3344_);
v_res_3354_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(v_declName_3343_, v_isMeta_boxed_3353_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg(lean_object* v_as_x27_3355_, lean_object* v_b_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
if (lean_obj_tag(v_as_x27_3355_) == 0)
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_b_3356_);
return v___x_3365_;
}
else
{
lean_object* v_head_3366_; lean_object* v_tail_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; 
v_head_3366_ = lean_ctor_get(v_as_x27_3355_, 0);
v_tail_3367_ = lean_ctor_get(v_as_x27_3355_, 1);
v___x_3368_ = lean_box(0);
v___x_3369_ = 1;
lean_inc(v_head_3366_);
v___x_3370_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(v_head_3366_, v___x_3369_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_dec_ref_known(v___x_3370_, 1);
v_as_x27_3355_ = v_tail_3367_;
v_b_3356_ = v___x_3368_;
goto _start;
}
else
{
return v___x_3370_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg___boxed(lean_object* v_as_x27_3372_, lean_object* v_b_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg(v_as_x27_3372_, v_b_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v_as_x27_3372_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(lean_object* v_env_3383_, lean_object* v___x_3384_, lean_object* v_currNamespace_3385_, lean_object* v_openDecls_3386_, lean_object* v_n_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = l_Lean_ResolveName_resolveGlobalName(v_env_3383_, v___x_3384_, v_currNamespace_3385_, v_openDecls_3386_, v_n_3387_);
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v___y_3389_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed(lean_object* v_env_3392_, lean_object* v___x_3393_, lean_object* v_currNamespace_3394_, lean_object* v_openDecls_3395_, lean_object* v_n_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(v_env_3392_, v___x_3393_, v_currNamespace_3394_, v_openDecls_3395_, v_n_3396_, v___y_3397_, v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec_ref(v___x_3393_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(lean_object* v_x_3400_, lean_object* v___y_3401_){
_start:
{
if (lean_obj_tag(v_x_3400_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3403_; 
v_a_3402_ = lean_ctor_get(v_x_3400_, 0);
lean_inc(v_a_3402_);
v___x_3403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3403_, 0, v_a_3402_);
lean_ctor_set(v___x_3403_, 1, v___y_3401_);
return v___x_3403_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3405_; 
v_a_3404_ = lean_ctor_get(v_x_3400_, 0);
lean_inc(v_a_3404_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v_a_3404_);
lean_ctor_set(v___x_3405_, 1, v___y_3401_);
return v___x_3405_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg___boxed(lean_object* v_x_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(v_x_3406_, v___y_3407_);
lean_dec_ref(v_x_3406_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(lean_object* v_env_3409_, lean_object* v_stx_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_3409_, v_stx_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
if (lean_obj_tag(v_a_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3423_; 
v_a_3415_ = lean_ctor_get(v___x_3413_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; 
v_unused_3424_ = lean_ctor_get(v___x_3413_, 0);
lean_dec(v_unused_3424_);
v___x_3417_ = v___x_3413_;
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3413_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3419_ = lean_box(0);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3419_);
v___x_3421_ = v___x_3417_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_a_3415_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
else
{
lean_object* v_val_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3453_; 
v_val_3425_ = lean_ctor_get(v_a_3414_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_a_3414_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3427_ = v_a_3414_;
v_isShared_3428_ = v_isSharedCheck_3453_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_val_3425_);
lean_dec(v_a_3414_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3453_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v_snd_3429_; 
v_snd_3429_ = lean_ctor_get(v_val_3425_, 1);
lean_inc(v_snd_3429_);
lean_dec(v_val_3425_);
if (lean_obj_tag(v_snd_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3439_; 
lean_del_object(v___x_3427_);
v_a_3430_ = lean_ctor_get(v___x_3413_, 1);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3413_, 2);
v_a_3431_ = lean_ctor_get(v_snd_3429_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_snd_3429_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3433_ = v_snd_3429_;
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v_snd_3429_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(v___x_3436_, v_a_3430_);
lean_dec_ref(v___x_3436_);
return v___x_3437_;
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3452_; 
v_a_3440_ = lean_ctor_get(v___x_3413_, 1);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3413_, 2);
v_a_3441_ = lean_ctor_get(v_snd_3429_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_snd_3429_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3443_ = v_snd_3429_;
v_isShared_3444_ = v_isSharedCheck_3452_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v_snd_3429_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3452_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 0, v_a_3441_);
v___x_3446_ = v___x_3427_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3448_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3446_);
v___x_3448_ = v___x_3443_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(v___x_3448_, v_a_3440_);
lean_dec_ref(v___x_3448_);
return v___x_3449_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
v_a_3454_ = lean_ctor_get(v___x_3413_, 0);
v_a_3455_ = lean_ctor_get(v___x_3413_, 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3413_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_inc(v_a_3454_);
lean_dec(v___x_3413_);
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
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3454_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_a_3455_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed(lean_object* v_env_3463_, lean_object* v_stx_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(v_env_3463_, v_stx_3464_, v___y_3465_, v___y_3466_);
lean_dec_ref(v___y_3465_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_x_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; lean_object* v_toCold_3479_; lean_object* v_env_3480_; lean_object* v_currRecDepth_3481_; lean_object* v_ref_3482_; lean_object* v_maxRecDepth_3483_; lean_object* v_currNamespace_3484_; lean_object* v_openDecls_3485_; lean_object* v_quotContext_3486_; lean_object* v_currMacroScope_3487_; lean_object* v___f_3488_; lean_object* v___f_3489_; lean_object* v___x_3490_; lean_object* v___f_3491_; lean_object* v___f_3492_; lean_object* v___f_3493_; lean_object* v_methods_3494_; lean_object* v___x_3495_; lean_object* v_nextMacroScope_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3478_ = lean_st_ref_get(v___y_3476_);
v_toCold_3479_ = lean_ctor_get(v___y_3475_, 0);
v_env_3480_ = lean_ctor_get(v___x_3478_, 0);
lean_inc_ref_n(v_env_3480_, 4);
lean_dec(v___x_3478_);
v_currRecDepth_3481_ = lean_ctor_get(v___y_3475_, 1);
v_ref_3482_ = lean_ctor_get(v___y_3475_, 2);
v_maxRecDepth_3483_ = lean_ctor_get(v_toCold_3479_, 3);
v_currNamespace_3484_ = lean_ctor_get(v_toCold_3479_, 4);
v_openDecls_3485_ = lean_ctor_get(v_toCold_3479_, 5);
v_quotContext_3486_ = lean_ctor_get(v_toCold_3479_, 8);
v_currMacroScope_3487_ = lean_ctor_get(v_toCold_3479_, 9);
v___f_3488_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3488_, 0, v_env_3480_);
v___f_3489_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3489_, 0, v_env_3480_);
v___x_3490_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3475_);
lean_inc_n(v_currNamespace_3484_, 3);
v___f_3491_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3491_, 0, v_currNamespace_3484_);
lean_inc_n(v_openDecls_3485_, 2);
v___f_3492_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_3492_, 0, v_env_3480_);
lean_closure_set(v___f_3492_, 1, v___x_3490_);
lean_closure_set(v___f_3492_, 2, v_currNamespace_3484_);
lean_closure_set(v___f_3492_, 3, v_openDecls_3485_);
v___f_3493_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_3493_, 0, v_env_3480_);
lean_closure_set(v___f_3493_, 1, v_currNamespace_3484_);
lean_closure_set(v___f_3493_, 2, v_openDecls_3485_);
v_methods_3494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3494_, 0, v___f_3489_);
lean_ctor_set(v_methods_3494_, 1, v___f_3491_);
lean_ctor_set(v_methods_3494_, 2, v___f_3488_);
lean_ctor_set(v_methods_3494_, 3, v___f_3493_);
lean_ctor_set(v_methods_3494_, 4, v___f_3492_);
v___x_3495_ = lean_st_ref_get(v___y_3476_);
v_nextMacroScope_3496_ = lean_ctor_get(v___x_3495_, 1);
lean_inc(v_nextMacroScope_3496_);
lean_dec(v___x_3495_);
lean_inc(v_ref_3482_);
lean_inc(v_maxRecDepth_3483_);
lean_inc(v_currRecDepth_3481_);
lean_inc(v_currMacroScope_3487_);
lean_inc(v_quotContext_3486_);
v___x_3497_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3497_, 0, v_methods_3494_);
lean_ctor_set(v___x_3497_, 1, v_quotContext_3486_);
lean_ctor_set(v___x_3497_, 2, v_currMacroScope_3487_);
lean_ctor_set(v___x_3497_, 3, v_currRecDepth_3481_);
lean_ctor_set(v___x_3497_, 4, v_maxRecDepth_3483_);
lean_ctor_set(v___x_3497_, 5, v_ref_3482_);
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3499_, 0, v_nextMacroScope_3496_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
lean_ctor_set(v___x_3499_, 2, v___x_3498_);
v___x_3500_ = lean_apply_2(v_x_3469_, v___x_3497_, v___x_3499_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v_a_3502_; lean_object* v_macroScope_3503_; lean_object* v_traceMsgs_3504_; lean_object* v_expandedMacroDecls_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 1);
lean_inc(v_a_3501_);
v_a_3502_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3500_, 2);
v_macroScope_3503_ = lean_ctor_get(v_a_3501_, 0);
lean_inc(v_macroScope_3503_);
v_traceMsgs_3504_ = lean_ctor_get(v_a_3501_, 1);
lean_inc(v_traceMsgs_3504_);
v_expandedMacroDecls_3505_ = lean_ctor_get(v_a_3501_, 2);
lean_inc(v_expandedMacroDecls_3505_);
lean_dec(v_a_3501_);
v___x_3506_ = lean_box(0);
v___x_3507_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg(v_expandedMacroDecls_3505_, v___x_3506_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v_expandedMacroDecls_3505_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v___x_3508_; lean_object* v_env_3509_; lean_object* v_ngen_3510_; lean_object* v_auxDeclNGen_3511_; lean_object* v_traceState_3512_; lean_object* v_cache_3513_; lean_object* v_recordedDeps_3514_; lean_object* v_messages_3515_; lean_object* v_infoState_3516_; lean_object* v_snapshotTasks_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3543_; 
lean_dec_ref_known(v___x_3507_, 1);
v___x_3508_ = lean_st_ref_take(v___y_3476_);
v_env_3509_ = lean_ctor_get(v___x_3508_, 0);
v_ngen_3510_ = lean_ctor_get(v___x_3508_, 2);
v_auxDeclNGen_3511_ = lean_ctor_get(v___x_3508_, 3);
v_traceState_3512_ = lean_ctor_get(v___x_3508_, 4);
v_cache_3513_ = lean_ctor_get(v___x_3508_, 5);
v_recordedDeps_3514_ = lean_ctor_get(v___x_3508_, 6);
v_messages_3515_ = lean_ctor_get(v___x_3508_, 7);
v_infoState_3516_ = lean_ctor_get(v___x_3508_, 8);
v_snapshotTasks_3517_ = lean_ctor_get(v___x_3508_, 9);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3543_ == 0)
{
lean_object* v_unused_3544_; 
v_unused_3544_ = lean_ctor_get(v___x_3508_, 1);
lean_dec(v_unused_3544_);
v___x_3519_ = v___x_3508_;
v_isShared_3520_ = v_isSharedCheck_3543_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snapshotTasks_3517_);
lean_inc(v_infoState_3516_);
lean_inc(v_messages_3515_);
lean_inc(v_recordedDeps_3514_);
lean_inc(v_cache_3513_);
lean_inc(v_traceState_3512_);
lean_inc(v_auxDeclNGen_3511_);
lean_inc(v_ngen_3510_);
lean_inc(v_env_3509_);
lean_dec(v___x_3508_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3543_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v_macroScope_3503_);
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_env_3509_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_macroScope_3503_);
lean_ctor_set(v_reuseFailAlloc_3542_, 2, v_ngen_3510_);
lean_ctor_set(v_reuseFailAlloc_3542_, 3, v_auxDeclNGen_3511_);
lean_ctor_set(v_reuseFailAlloc_3542_, 4, v_traceState_3512_);
lean_ctor_set(v_reuseFailAlloc_3542_, 5, v_cache_3513_);
lean_ctor_set(v_reuseFailAlloc_3542_, 6, v_recordedDeps_3514_);
lean_ctor_set(v_reuseFailAlloc_3542_, 7, v_messages_3515_);
lean_ctor_set(v_reuseFailAlloc_3542_, 8, v_infoState_3516_);
lean_ctor_set(v_reuseFailAlloc_3542_, 9, v_snapshotTasks_3517_);
v___x_3522_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3523_ = lean_st_ref_put(v___y_3476_, v___x_3522_);
v___x_3524_ = l_List_reverse___redArg(v_traceMsgs_3504_);
v___x_3525_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(v___x_3524_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v___x_3525_, 0);
lean_dec(v_unused_3533_);
v___x_3527_ = v___x_3525_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_dec(v___x_3525_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v_a_3502_);
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3502_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec(v_a_3502_);
v_a_3534_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3525_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3525_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_traceMsgs_3504_);
lean_dec(v_macroScope_3503_);
lean_dec(v_a_3502_);
v_a_3545_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3507_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3507_);
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
lean_object* v_a_3553_; 
v_a_3553_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3500_, 2);
if (lean_obj_tag(v_a_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v_a_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v_a_3554_ = lean_ctor_get(v_a_3553_, 0);
lean_inc(v_a_3554_);
v_a_3555_ = lean_ctor_get(v_a_3553_, 1);
lean_inc_ref(v_a_3555_);
lean_dec_ref_known(v_a_3553_, 2);
v___x_3556_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___closed__0));
v___x_3557_ = lean_string_dec_eq(v_a_3555_, v___x_3556_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_a_3555_);
v___x_3559_ = l_Lean_MessageData_ofFormat(v___x_3558_);
v___x_3560_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_a_3554_, v___x_3559_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v_a_3554_);
return v___x_3560_;
}
else
{
lean_object* v___x_3561_; 
lean_dec_ref(v_a_3555_);
v___x_3561_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg(v_a_3554_);
return v___x_3561_;
}
}
else
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_x_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v___y_3564_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(lean_object* v___x_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_toCold_3577_; lean_object* v_quotContext_3578_; lean_object* v_currMacroScope_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_toCold_3577_ = lean_ctor_get(v___y_3574_, 0);
lean_inc_ref(v_toCold_3577_);
lean_dec_ref(v___y_3574_);
v_quotContext_3578_ = lean_ctor_get(v_toCold_3577_, 8);
lean_inc(v_quotContext_3578_);
v_currMacroScope_3579_ = lean_ctor_get(v_toCold_3577_, 9);
lean_inc(v_currMacroScope_3579_);
lean_dec_ref(v_toCold_3577_);
v___x_3580_ = l_Lean_addMacroScope(v_quotContext_3578_, v___x_3573_, v_currMacroScope_3579_);
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v___x_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(v___x_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___f_3595_; lean_object* v___x_3596_; 
v___f_3595_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__2));
v___x_3596_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3595_, v___y_3592_, v___y_3593_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___boxed(lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_ref_3601_, uint8_t v_canonical_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3620_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3614_ = v___x_3611_;
v_isShared_3615_ = v_isSharedCheck_3620_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3611_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3620_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3616_ = l_Lean_mkIdentFrom(v_ref_3601_, v_a_3612_, v_canonical_3602_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v___x_3616_);
v___x_3618_ = v___x_3614_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3616_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
v_a_3621_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3611_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3611_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_ref_3629_, lean_object* v_canonical_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
uint8_t v_canonical_boxed_3639_; lean_object* v_res_3640_; 
v_canonical_boxed_3639_ = lean_unbox(v_canonical_3630_);
v_res_3640_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_ref_3629_, v_canonical_boxed_3639_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v_ref_3629_);
return v_res_3640_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1(void){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__0));
v___x_3643_ = l_Lean_stringToMessageData(v___x_3642_);
return v___x_3643_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3649_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3650_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__1));
v___x_3651_ = l_Lean_Name_append(v___x_3650_, v___x_3649_);
return v___x_3651_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3654_ = l_Lean_stringToMessageData(v___x_3653_);
return v___x_3654_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3657_ = l_Lean_stringToMessageData(v___x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3664_, lean_object* v_letOrReassign_3665_, lean_object* v_decl_3666_, lean_object* v_tk_3667_, lean_object* v_dec_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3664_, v_letOrReassign_3665_, v_decl_3666_, v_tk_3667_, v_dec_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
lean_dec(v_a_3675_);
lean_dec_ref(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec_ref(v_a_3672_);
lean_dec(v_a_3671_);
lean_dec_ref(v_a_3670_);
lean_dec_ref(v_a_3669_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3678_, lean_object* v_letOrReassign_3679_, lean_object* v_decl_3680_, lean_object* v_tk_3681_, lean_object* v_dec_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_config_3678_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v___x_3692_; 
lean_dec_ref_known(v___x_3691_, 1);
lean_inc(v_decl_3680_);
v___x_3692_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3680_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3694_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
v___x_3694_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3679_, v_a_3693_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v___x_3695_; 
lean_dec_ref_known(v___x_3694_, 1);
v___x_3695_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3682_, v_tk_3681_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___y_3698_; uint8_t v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; uint8_t v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v_rhs_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3726_; lean_object* v___y_3727_; uint8_t v___y_3728_; lean_object* v___y_3729_; uint8_t v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; uint8_t v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v_xType_x3f_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; uint8_t v___y_3795_; uint8_t v___y_3796_; uint8_t v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; uint8_t v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; uint8_t v___y_3813_; uint8_t v___y_3872_; uint8_t v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; uint8_t v___y_3878_; uint8_t v___y_3879_; lean_object* v_id_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v_decl_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___x_3984_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3984_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_3679_, v_a_3693_, v_a_3683_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3986_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3986_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3679_, v_decl_3680_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_);
if (lean_obj_tag(v___x_3986_) == 0)
{
uint8_t v___x_3987_; 
v___x_3987_ = lean_unbox(v_a_3985_);
lean_dec(v_a_3985_);
if (v___x_3987_ == 0)
{
lean_object* v_a_3988_; 
v_a_3988_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v___x_3986_, 1);
v_decl_3899_ = v_a_3988_;
v___y_3900_ = v_a_3683_;
v___y_3901_ = v_a_3684_;
v___y_3902_ = v_a_3685_;
v___y_3903_ = v_a_3686_;
v___y_3904_ = v_a_3687_;
v___y_3905_ = v_a_3688_;
v___y_3906_ = v_a_3689_;
goto v___jp_3898_;
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3990_; 
v_a_3989_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3986_, 1);
v___x_3990_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(v_a_3989_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref_known(v___x_3990_, 1);
v_decl_3899_ = v_a_3991_;
v___y_3900_ = v_a_3683_;
v___y_3901_ = v_a_3684_;
v___y_3902_ = v_a_3685_;
v___y_3903_ = v_a_3686_;
v___y_3904_ = v_a_3687_;
v___y_3905_ = v_a_3688_;
v___y_3906_ = v_a_3689_;
goto v___jp_3898_;
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_tk_3681_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v_a_3992_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3990_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3990_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v_a_3985_);
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_tk_3681_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v_a_4000_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3986_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3986_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_tk_3681_);
lean_dec(v_decl_3680_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v_a_4008_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3984_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3984_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
v___jp_3697_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___f_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3715_ = lean_box(v___y_3703_);
v___x_3716_ = lean_box(v___y_3699_);
lean_inc_ref(v___y_3698_);
lean_inc_ref(v___y_3704_);
lean_inc_ref(v___y_3701_);
v___f_3717_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 19, 10);
lean_closure_set(v___f_3717_, 0, v_rhs_3707_);
lean_closure_set(v___f_3717_, 1, v___x_3715_);
lean_closure_set(v___f_3717_, 2, v_config_3678_);
lean_closure_set(v___f_3717_, 3, v___y_3700_);
lean_closure_set(v___f_3717_, 4, v___x_3716_);
lean_closure_set(v___f_3717_, 5, v___y_3701_);
lean_closure_set(v___f_3717_, 6, v___y_3704_);
lean_closure_set(v___f_3717_, 7, v___y_3698_);
lean_closure_set(v___f_3717_, 8, v___y_3702_);
lean_closure_set(v___f_3717_, 9, v___y_3705_);
v___x_3718_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3718_, 0, v_a_3696_);
v___x_3719_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3719_, 0, v_letOrReassign_3679_);
lean_closure_set(v___x_3719_, 1, v_a_3693_);
lean_closure_set(v___x_3719_, 2, v___x_3718_);
v___x_3720_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1);
v___x_3721_ = l_Lean_MessageData_ofSyntax(v___y_3706_);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3720_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = lean_box(0);
v___x_3724_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3722_, v___x_3719_, v___f_3717_, v___x_3723_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
return v___x_3724_;
}
v___jp_3725_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = lean_unsigned_to_nat(4u);
v___x_3748_ = l_Lean_Syntax_getArg(v___y_3737_, v___x_3747_);
lean_dec(v___y_3737_);
if (lean_obj_tag(v_xType_x3f_3739_) == 0)
{
lean_inc(v___y_3733_);
v___y_3698_ = v___y_3726_;
v___y_3699_ = v___y_3728_;
v___y_3700_ = v___y_3727_;
v___y_3701_ = v___y_3729_;
v___y_3702_ = v___y_3731_;
v___y_3703_ = v___y_3730_;
v___y_3704_ = v___y_3732_;
v___y_3705_ = v___y_3733_;
v___y_3706_ = v___y_3733_;
v_rhs_3707_ = v___x_3748_;
v___y_3708_ = v___y_3740_;
v___y_3709_ = v___y_3741_;
v___y_3710_ = v___y_3742_;
v___y_3711_ = v___y_3743_;
v___y_3712_ = v___y_3744_;
v___y_3713_ = v___y_3745_;
v___y_3714_ = v___y_3746_;
goto v___jp_3697_;
}
else
{
lean_object* v_toCold_3749_; lean_object* v_val_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3793_; 
v_toCold_3749_ = lean_ctor_get(v___y_3745_, 0);
v_val_3750_ = lean_ctor_get(v_xType_x3f_3739_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v_xType_x3f_3739_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3752_ = v_xType_x3f_3739_;
v_isShared_3753_ = v_isSharedCheck_3793_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_val_3750_);
lean_dec(v_xType_x3f_3739_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3793_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v_ref_3754_; lean_object* v_quotContext_3755_; lean_object* v_currMacroScope_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
v_ref_3754_ = lean_ctor_get(v___y_3745_, 2);
v_quotContext_3755_ = lean_ctor_get(v_toCold_3749_, 8);
v_currMacroScope_3756_ = lean_ctor_get(v_toCold_3749_, 9);
v___x_3757_ = l_Lean_SourceInfo_fromRef(v_ref_3754_, v___y_3736_);
v___x_3758_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__15));
lean_inc_ref_n(v___y_3734_, 2);
lean_inc_ref_n(v___y_3738_, 2);
lean_inc_ref_n(v___y_3735_, 3);
v___x_3759_ = l_Lean_Name_mkStr4(v___y_3735_, v___y_3738_, v___y_3734_, v___x_3758_);
v___x_3760_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__17));
v___x_3761_ = l_Lean_Name_mkStr4(v___y_3735_, v___y_3738_, v___y_3734_, v___x_3760_);
v___x_3762_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_3757_);
v___x_3763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3757_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3765_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3766_ = lean_box(0);
lean_inc(v_currMacroScope_3756_);
lean_inc(v_quotContext_3755_);
v___x_3767_ = l_Lean_addMacroScope(v_quotContext_3755_, v___x_3766_, v_currMacroScope_3756_);
v___x_3768_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24));
v___x_3769_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25));
v___x_3770_ = l_Lean_Name_mkStr3(v___y_3735_, v___x_3768_, v___x_3769_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set_tag(v___x_3752_, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3770_);
v___x_3772_ = v___x_3752_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3773_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__28));
lean_inc_ref_n(v___y_3735_, 2);
v___x_3774_ = l_Lean_Name_mkStr2(v___y_3735_, v___x_3773_);
v___x_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3774_);
lean_inc_ref(v___y_3734_);
lean_inc_ref(v___y_3738_);
v___x_3776_ = l_Lean_Name_mkStr3(v___y_3735_, v___y_3738_, v___y_3734_);
v___x_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
v___x_3778_ = lean_box(0);
v___x_3779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3775_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3772_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
lean_inc_n(v___x_3757_, 6);
v___x_3782_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3757_);
lean_ctor_set(v___x_3782_, 1, v___x_3765_);
lean_ctor_set(v___x_3782_, 2, v___x_3767_);
lean_ctor_set(v___x_3782_, 3, v___x_3781_);
v___x_3783_ = l_Lean_Syntax_node1(v___x_3757_, v___x_3764_, v___x_3782_);
v___x_3784_ = l_Lean_Syntax_node2(v___x_3757_, v___x_3761_, v___x_3763_, v___x_3783_);
v___x_3785_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3757_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3788_ = l_Lean_Syntax_node1(v___x_3757_, v___x_3787_, v_val_3750_);
v___x_3789_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3757_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = l_Lean_Syntax_node5(v___x_3757_, v___x_3759_, v___x_3784_, v___x_3748_, v___x_3786_, v___x_3788_, v___x_3790_);
lean_inc(v___y_3733_);
v___y_3698_ = v___y_3726_;
v___y_3699_ = v___y_3728_;
v___y_3700_ = v___y_3727_;
v___y_3701_ = v___y_3729_;
v___y_3702_ = v___y_3731_;
v___y_3703_ = v___y_3730_;
v___y_3704_ = v___y_3732_;
v___y_3705_ = v___y_3733_;
v___y_3706_ = v___y_3733_;
v_rhs_3707_ = v___x_3791_;
v___y_3708_ = v___y_3740_;
v___y_3709_ = v___y_3741_;
v___y_3710_ = v___y_3742_;
v___y_3711_ = v___y_3743_;
v___y_3712_ = v___y_3744_;
v___y_3713_ = v___y_3745_;
v___y_3714_ = v___y_3746_;
goto v___jp_3697_;
}
}
}
}
v___jp_3794_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___f_3817_; lean_object* v___x_3818_; 
v___x_3814_ = lean_box(v___y_3796_);
v___x_3815_ = lean_box(v___y_3797_);
v___x_3816_ = lean_box(v___y_3813_);
v___f_3817_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3817_, 0, v___y_3803_);
lean_closure_set(v___f_3817_, 1, v___y_3798_);
lean_closure_set(v___f_3817_, 2, v___x_3814_);
lean_closure_set(v___f_3817_, 3, v___x_3815_);
lean_closure_set(v___f_3817_, 4, v___y_3801_);
lean_closure_set(v___f_3817_, 5, v___x_3816_);
v___x_3818_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___y_3810_, v___f_3817_, v___y_3808_, v___y_3812_, v___y_3811_, v___y_3807_, v___y_3805_, v___y_3804_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v_toCold_3820_; lean_object* v_options_3821_; lean_object* v_fst_3822_; lean_object* v_snd_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3862_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v___x_3818_, 1);
v_toCold_3820_ = lean_ctor_get(v___y_3805_, 0);
v_options_3821_ = lean_ctor_get(v_toCold_3820_, 2);
v_fst_3822_ = lean_ctor_get(v_a_3819_, 0);
v_snd_3823_ = lean_ctor_get(v_a_3819_, 1);
v_isSharedCheck_3862_ = !lean_is_exclusive(v_a_3819_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3825_ = v_a_3819_;
v_isShared_3826_ = v_isSharedCheck_3862_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_snd_3823_);
lean_inc(v_fst_3822_);
lean_dec(v_a_3819_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3862_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v_inheritedTraceOptions_3827_; uint8_t v_hasTrace_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___f_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_inheritedTraceOptions_3827_ = lean_ctor_get(v_toCold_3820_, 11);
v_hasTrace_3828_ = lean_ctor_get_uint8(v_options_3821_, sizeof(void*)*1);
v___x_3829_ = lean_box(v___y_3802_);
v___x_3830_ = lean_box(v___y_3795_);
v___x_3831_ = lean_box(v___y_3813_);
v___x_3832_ = lean_box(v___y_3796_);
lean_inc(v_snd_3823_);
v___f_3833_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 19, 10);
lean_closure_set(v___f_3833_, 0, v___y_3800_);
lean_closure_set(v___f_3833_, 1, v___y_3799_);
lean_closure_set(v___f_3833_, 2, v_a_3696_);
lean_closure_set(v___f_3833_, 3, v_letOrReassign_3679_);
lean_closure_set(v___f_3833_, 4, v_a_3693_);
lean_closure_set(v___f_3833_, 5, v___x_3829_);
lean_closure_set(v___f_3833_, 6, v___x_3830_);
lean_closure_set(v___f_3833_, 7, v_snd_3823_);
lean_closure_set(v___f_3833_, 8, v___x_3831_);
lean_closure_set(v___f_3833_, 9, v___x_3832_);
v___x_3834_ = l_Lean_Syntax_getId(v___y_3809_);
lean_dec(v___y_3809_);
v___x_3835_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3834_);
if (v_hasTrace_3828_ == 0)
{
lean_object* v___x_3836_; 
lean_del_object(v___x_3825_);
v___x_3836_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3834_, v_fst_3822_, v_snd_3823_, v___f_3833_, v___y_3813_, v___x_3835_, v___y_3806_, v___y_3808_, v___y_3812_, v___y_3811_, v___y_3807_, v___y_3805_, v___y_3804_);
return v___x_3836_;
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v___x_3837_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3838_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3827_, v_options_3821_, v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; 
lean_del_object(v___x_3825_);
v___x_3840_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3834_, v_fst_3822_, v_snd_3823_, v___f_3833_, v___y_3813_, v___x_3835_, v___y_3806_, v___y_3808_, v___y_3812_, v___y_3811_, v___y_3807_, v___y_3805_, v___y_3804_);
return v___x_3840_;
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
lean_inc(v___x_3834_);
v___x_3841_ = l_Lean_MessageData_ofName(v___x_3834_);
v___x_3842_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3826_ == 0)
{
lean_ctor_set_tag(v___x_3825_, 7);
lean_ctor_set(v___x_3825_, 1, v___x_3842_);
lean_ctor_set(v___x_3825_, 0, v___x_3841_);
v___x_3844_ = v___x_3825_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_inc(v_fst_3822_);
v___x_3845_ = l_Lean_MessageData_ofExpr(v_fst_3822_);
v___x_3846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3844_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
v___x_3847_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
lean_inc(v_snd_3823_);
v___x_3849_ = l_Lean_MessageData_ofExpr(v_snd_3823_);
v___x_3850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3837_, v___x_3850_, v___y_3811_, v___y_3807_, v___y_3805_, v___y_3804_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v___x_3852_; 
lean_dec_ref_known(v___x_3851_, 1);
v___x_3852_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3834_, v_fst_3822_, v_snd_3823_, v___f_3833_, v___y_3813_, v___x_3835_, v___y_3806_, v___y_3808_, v___y_3812_, v___y_3811_, v___y_3807_, v___y_3805_, v___y_3804_);
return v___x_3852_;
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v___x_3834_);
lean_dec_ref(v___f_3833_);
lean_dec(v_snd_3823_);
lean_dec(v_fst_3822_);
v_a_3853_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3851_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3851_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
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
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec(v___y_3809_);
lean_dec(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_letOrReassign_3679_);
v_a_3863_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3818_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3818_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
v___jp_3871_:
{
uint8_t v_nondep_3888_; 
v_nondep_3888_ = lean_ctor_get_uint8(v_config_3678_, sizeof(void*)*1);
if (v_nondep_3888_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3679_) == 1)
{
uint8_t v_usedOnly_3889_; uint8_t v_zeta_3890_; lean_object* v_eq_x3f_3891_; 
v_usedOnly_3889_ = lean_ctor_get_uint8(v_config_3678_, sizeof(void*)*1 + 1);
v_zeta_3890_ = lean_ctor_get_uint8(v_config_3678_, sizeof(void*)*1 + 2);
v_eq_x3f_3891_ = lean_ctor_get(v_config_3678_, 0);
lean_inc(v_eq_x3f_3891_);
lean_dec_ref(v_config_3678_);
lean_inc(v_id_3880_);
v___y_3795_ = v_usedOnly_3889_;
v___y_3796_ = v___y_3872_;
v___y_3797_ = v___y_3873_;
v___y_3798_ = v___y_3874_;
v___y_3799_ = v_eq_x3f_3891_;
v___y_3800_ = v_id_3880_;
v___y_3801_ = v___y_3876_;
v___y_3802_ = v_zeta_3890_;
v___y_3803_ = v___y_3877_;
v___y_3804_ = v___y_3887_;
v___y_3805_ = v___y_3886_;
v___y_3806_ = v___y_3881_;
v___y_3807_ = v___y_3885_;
v___y_3808_ = v___y_3882_;
v___y_3809_ = v_id_3880_;
v___y_3810_ = v___y_3875_;
v___y_3811_ = v___y_3884_;
v___y_3812_ = v___y_3883_;
v___y_3813_ = v___y_3878_;
goto v___jp_3794_;
}
else
{
uint8_t v_usedOnly_3892_; uint8_t v_zeta_3893_; lean_object* v_eq_x3f_3894_; 
v_usedOnly_3892_ = lean_ctor_get_uint8(v_config_3678_, sizeof(void*)*1 + 1);
v_zeta_3893_ = lean_ctor_get_uint8(v_config_3678_, sizeof(void*)*1 + 2);
v_eq_x3f_3894_ = lean_ctor_get(v_config_3678_, 0);
lean_inc(v_eq_x3f_3894_);
lean_dec_ref(v_config_3678_);
lean_inc(v_id_3880_);
v___y_3795_ = v_usedOnly_3892_;
v___y_3796_ = v___y_3872_;
v___y_3797_ = v___y_3873_;
v___y_3798_ = v___y_3874_;
v___y_3799_ = v_eq_x3f_3894_;
v___y_3800_ = v_id_3880_;
v___y_3801_ = v___y_3876_;
v___y_3802_ = v_zeta_3893_;
v___y_3803_ = v___y_3877_;
v___y_3804_ = v___y_3887_;
v___y_3805_ = v___y_3886_;
v___y_3806_ = v___y_3881_;
v___y_3807_ = v___y_3885_;
v___y_3808_ = v___y_3882_;
v___y_3809_ = v_id_3880_;
v___y_3810_ = v___y_3875_;
v___y_3811_ = v___y_3884_;
v___y_3812_ = v___y_3883_;
v___y_3813_ = v___y_3879_;
goto v___jp_3794_;
}
}
else
{
uint8_t v_usedOnly_3895_; uint8_t v_zeta_3896_; lean_object* v_eq_x3f_3897_; 
v_usedOnly_3895_ = lean_ctor_get_uint8(v_config_3678_, sizeof(void*)*1 + 1);
v_zeta_3896_ = lean_ctor_get_uint8(v_config_3678_, sizeof(void*)*1 + 2);
v_eq_x3f_3897_ = lean_ctor_get(v_config_3678_, 0);
lean_inc(v_eq_x3f_3897_);
lean_dec_ref(v_config_3678_);
lean_inc(v_id_3880_);
v___y_3795_ = v_usedOnly_3895_;
v___y_3796_ = v___y_3872_;
v___y_3797_ = v___y_3873_;
v___y_3798_ = v___y_3874_;
v___y_3799_ = v_eq_x3f_3897_;
v___y_3800_ = v_id_3880_;
v___y_3801_ = v___y_3876_;
v___y_3802_ = v_zeta_3896_;
v___y_3803_ = v___y_3877_;
v___y_3804_ = v___y_3887_;
v___y_3805_ = v___y_3886_;
v___y_3806_ = v___y_3881_;
v___y_3807_ = v___y_3885_;
v___y_3808_ = v___y_3882_;
v___y_3809_ = v_id_3880_;
v___y_3810_ = v___y_3875_;
v___y_3811_ = v___y_3884_;
v___y_3812_ = v___y_3883_;
v___y_3813_ = v___y_3878_;
goto v___jp_3794_;
}
}
v___jp_3898_:
{
lean_object* v_doBlockResultType_3907_; lean_object* v___x_3908_; 
v_doBlockResultType_3907_ = lean_ctor_get(v___y_3900_, 3);
lean_inc_ref(v_doBlockResultType_3907_);
v___x_3908_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3907_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3983_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3911_ = v___x_3908_;
v_isShared_3912_ = v_isSharedCheck_3983_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3908_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3983_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; 
v___x_3913_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3914_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3915_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3916_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_3899_);
v___x_3917_ = l_Lean_Syntax_isOfKind(v_decl_3899_, v___x_3916_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; 
lean_del_object(v___x_3911_);
lean_dec(v_a_3909_);
lean_dec(v_decl_3899_);
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_tk_3681_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v___x_3918_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3918_;
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; uint8_t v___x_3922_; 
v___x_3919_ = lean_unsigned_to_nat(0u);
v___x_3920_ = l_Lean_Syntax_getArg(v_decl_3899_, v___x_3919_);
lean_dec(v_decl_3899_);
v___x_3921_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__10));
lean_inc(v___x_3920_);
v___x_3922_ = l_Lean_Syntax_isOfKind(v___x_3920_, v___x_3921_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; uint8_t v___x_3924_; 
lean_dec(v_tk_3681_);
v___x_3923_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3920_);
v___x_3924_ = l_Lean_Syntax_isOfKind(v___x_3920_, v___x_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; uint8_t v___x_3926_; 
lean_del_object(v___x_3911_);
lean_dec(v_a_3909_);
v___x_3925_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3920_);
v___x_3926_ = l_Lean_Syntax_isOfKind(v___x_3920_, v___x_3925_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; 
lean_dec(v___x_3920_);
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v___x_3927_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3927_;
}
else
{
lean_object* v___x_3928_; lean_object* v_id_3929_; lean_object* v_binders_3930_; lean_object* v_type_3931_; lean_object* v_value_3932_; uint8_t v___x_3933_; 
v___x_3928_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3920_);
lean_dec(v___x_3920_);
v_id_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_id_3929_);
v_binders_3930_ = lean_ctor_get(v___x_3928_, 1);
lean_inc_ref(v_binders_3930_);
v_type_3931_ = lean_ctor_get(v___x_3928_, 2);
lean_inc(v_type_3931_);
v_value_3932_ = lean_ctor_get(v___x_3928_, 3);
lean_inc(v_value_3932_);
lean_dec_ref(v___x_3928_);
v___x_3933_ = l_Lean_Syntax_isIdent(v_id_3929_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_id_3929_, v___x_3917_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec(v_id_3929_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3934_, 1);
v___y_3872_ = v___x_3917_;
v___y_3873_ = v___x_3924_;
v___y_3874_ = v_value_3932_;
v___y_3875_ = v_binders_3930_;
v___y_3876_ = v___x_3919_;
v___y_3877_ = v_type_3931_;
v___y_3878_ = v___x_3917_;
v___y_3879_ = v___x_3924_;
v_id_3880_ = v_a_3935_;
v___y_3881_ = v___y_3900_;
v___y_3882_ = v___y_3901_;
v___y_3883_ = v___y_3902_;
v___y_3884_ = v___y_3903_;
v___y_3885_ = v___y_3904_;
v___y_3886_ = v___y_3905_;
v___y_3887_ = v___y_3906_;
goto v___jp_3871_;
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec(v_value_3932_);
lean_dec(v_type_3931_);
lean_dec_ref(v_binders_3930_);
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v_a_3936_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3934_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3934_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
else
{
v___y_3872_ = v___x_3917_;
v___y_3873_ = v___x_3924_;
v___y_3874_ = v_value_3932_;
v___y_3875_ = v_binders_3930_;
v___y_3876_ = v___x_3919_;
v___y_3877_ = v_type_3931_;
v___y_3878_ = v___x_3917_;
v___y_3879_ = v___x_3924_;
v_id_3880_ = v_id_3929_;
v___y_3881_ = v___y_3900_;
v___y_3882_ = v___y_3901_;
v___y_3883_ = v___y_3902_;
v___y_3884_ = v___y_3903_;
v___y_3885_ = v___y_3904_;
v___y_3886_ = v___y_3905_;
v___y_3887_ = v___y_3906_;
goto v___jp_3871_;
}
}
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3944_ = lean_unsigned_to_nat(1u);
v___x_3945_ = l_Lean_Syntax_getArg(v___x_3920_, v___x_3944_);
v___x_3946_ = l_Lean_Syntax_matchesNull(v___x_3945_, v___x_3919_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
lean_dec(v___x_3920_);
lean_del_object(v___x_3911_);
lean_dec(v_a_3909_);
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v___x_3947_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3947_;
}
else
{
lean_object* v___x_3948_; lean_object* v___f_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3948_ = lean_box(v___x_3922_);
v___f_3949_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 10, 1);
lean_closure_set(v___f_3949_, 0, v___x_3948_);
v___x_3950_ = l_Lean_Syntax_getArg(v___x_3920_, v___x_3919_);
v___x_3951_ = lean_unsigned_to_nat(2u);
v___x_3952_ = l_Lean_Syntax_getArg(v___x_3920_, v___x_3951_);
v___x_3953_ = l_Lean_Syntax_isNone(v___x_3952_);
if (v___x_3953_ == 0)
{
uint8_t v___x_3954_; 
lean_inc(v___x_3952_);
v___x_3954_ = l_Lean_Syntax_matchesNull(v___x_3952_, v___x_3944_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; 
lean_dec(v___x_3952_);
lean_dec(v___x_3950_);
lean_dec_ref(v___f_3949_);
lean_dec(v___x_3920_);
lean_del_object(v___x_3911_);
lean_dec(v_a_3909_);
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v___x_3955_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v___x_3956_ = l_Lean_Syntax_getArg(v___x_3952_, v___x_3919_);
lean_dec(v___x_3952_);
v___x_3957_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3956_);
v___x_3958_ = l_Lean_Syntax_isOfKind(v___x_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; 
lean_dec(v___x_3956_);
lean_dec(v___x_3950_);
lean_dec_ref(v___f_3949_);
lean_dec(v___x_3920_);
lean_del_object(v___x_3911_);
lean_dec(v_a_3909_);
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v___x_3959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3959_;
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3960_ = l_Lean_Syntax_getArg(v___x_3956_, v___x_3944_);
lean_dec(v___x_3956_);
if (v_isShared_3912_ == 0)
{
lean_ctor_set_tag(v___x_3911_, 1);
lean_ctor_set(v___x_3911_, 0, v___x_3960_);
v___x_3962_ = v___x_3911_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
v___y_3726_ = v___x_3915_;
v___y_3727_ = v_a_3909_;
v___y_3728_ = v___x_3917_;
v___y_3729_ = v___x_3913_;
v___y_3730_ = v___x_3922_;
v___y_3731_ = v___f_3949_;
v___y_3732_ = v___x_3914_;
v___y_3733_ = v___x_3950_;
v___y_3734_ = v___x_3915_;
v___y_3735_ = v___x_3913_;
v___y_3736_ = v___x_3922_;
v___y_3737_ = v___x_3920_;
v___y_3738_ = v___x_3914_;
v_xType_x3f_3739_ = v___x_3962_;
v___y_3740_ = v___y_3900_;
v___y_3741_ = v___y_3901_;
v___y_3742_ = v___y_3902_;
v___y_3743_ = v___y_3903_;
v___y_3744_ = v___y_3904_;
v___y_3745_ = v___y_3905_;
v___y_3746_ = v___y_3906_;
goto v___jp_3725_;
}
}
}
}
else
{
lean_object* v___x_3964_; 
lean_dec(v___x_3952_);
lean_del_object(v___x_3911_);
v___x_3964_ = lean_box(0);
v___y_3726_ = v___x_3915_;
v___y_3727_ = v_a_3909_;
v___y_3728_ = v___x_3917_;
v___y_3729_ = v___x_3913_;
v___y_3730_ = v___x_3922_;
v___y_3731_ = v___f_3949_;
v___y_3732_ = v___x_3914_;
v___y_3733_ = v___x_3950_;
v___y_3734_ = v___x_3915_;
v___y_3735_ = v___x_3913_;
v___y_3736_ = v___x_3922_;
v___y_3737_ = v___x_3920_;
v___y_3738_ = v___x_3914_;
v_xType_x3f_3739_ = v___x_3964_;
v___y_3740_ = v___y_3900_;
v___y_3741_ = v___y_3901_;
v___y_3742_ = v___y_3902_;
v___y_3743_ = v___y_3903_;
v___y_3744_ = v___y_3904_;
v___y_3745_ = v___y_3905_;
v___y_3746_ = v___y_3906_;
goto v___jp_3725_;
}
}
}
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_del_object(v___x_3911_);
lean_dec(v_a_3909_);
lean_dec(v_a_3693_);
v___x_3965_ = lean_box(v___x_3917_);
lean_inc(v___x_3920_);
v___x_3966_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3966_, 0, v___x_3920_);
lean_closure_set(v___x_3966_, 1, v___x_3965_);
v___x_3967_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3966_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v_ref_3969_; uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v___x_3967_, 1);
v_ref_3969_ = lean_ctor_get(v___y_3905_, 2);
v___x_3970_ = 0;
v___x_3971_ = l_Lean_SourceInfo_fromRef(v_ref_3969_, v___x_3970_);
v___x_3972_ = l_Lean_Syntax_node1(v___x_3971_, v___x_3916_, v_a_3968_);
lean_inc(v___x_3972_);
v___x_3973_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3973_, 0, v_config_3678_);
lean_closure_set(v___x_3973_, 1, v_letOrReassign_3679_);
lean_closure_set(v___x_3973_, 2, v___x_3972_);
lean_closure_set(v___x_3973_, 3, v_tk_3681_);
lean_closure_set(v___x_3973_, 4, v_a_3696_);
v___x_3974_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v___x_3920_, v___x_3972_, v___x_3973_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
return v___x_3974_;
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v___x_3920_);
lean_dec(v_a_3696_);
lean_dec(v_tk_3681_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v_a_3975_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3967_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3967_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
}
}
else
{
lean_dec(v_decl_3899_);
lean_dec(v_a_3696_);
lean_dec(v_a_3693_);
lean_dec(v_tk_3681_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
return v___x_3908_;
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v_a_3693_);
lean_dec(v_tk_3681_);
lean_dec(v_decl_3680_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v_a_4016_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3695_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3695_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec(v_a_3693_);
lean_dec_ref(v_dec_3682_);
lean_dec(v_tk_3681_);
lean_dec(v_decl_3680_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v_a_4024_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_3694_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_3694_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec_ref(v_dec_3682_);
lean_dec(v_tk_3681_);
lean_dec(v_decl_3680_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v_a_4032_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_3692_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_3692_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
lean_dec_ref(v_dec_3682_);
lean_dec(v_tk_3681_);
lean_dec(v_decl_3680_);
lean_dec(v_letOrReassign_3679_);
lean_dec_ref(v_config_3678_);
v_a_4040_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_3691_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_3691_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_4048_, lean_object* v_x_4049_, lean_object* v_x_4050_, lean_object* v_x_4051_){
_start:
{
lean_object* v___x_4052_; 
v___x_4052_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_4049_, v_x_4050_, v_x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_cls_4053_, lean_object* v_msg_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_4053_, v_msg_4054_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_cls_4064_, lean_object* v_msg_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_cls_4064_, v_msg_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_4080_, v___y_4081_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___boxed(lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec_ref(v___y_4084_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_00_u03b1_4093_, lean_object* v_beforeStx_4094_, lean_object* v_afterStx_4095_, lean_object* v_x_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_beforeStx_4094_, v_afterStx_4095_, v_x_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_00_u03b1_4106_, lean_object* v_beforeStx_4107_, lean_object* v_afterStx_4108_, lean_object* v_x_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_00_u03b1_4106_, v_beforeStx_4107_, v_afterStx_4108_, v_x_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec_ref(v___y_4110_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(lean_object* v_00_u03b1_4119_, lean_object* v_x_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(v_x_4120_, v___y_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___boxed(lean_object* v_00_u03b1_4124_, lean_object* v_x_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(v_00_u03b1_4124_, v_x_4125_, v___y_4126_, v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec_ref(v_x_4125_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16(lean_object* v_00_u03b1_4129_, lean_object* v_ref_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg(v_ref_4130_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___boxed(lean_object* v_00_u03b1_4140_, lean_object* v_ref_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16(v_00_u03b1_4140_, v_ref_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec_ref(v___y_4142_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_4151_, lean_object* v_x_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_4162_, lean_object* v_x_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_4162_, v_x_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec_ref(v___y_4164_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_4173_, lean_object* v_x_4174_, size_t v_x_4175_, size_t v_x_4176_, lean_object* v_x_4177_, lean_object* v_x_4178_){
_start:
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_4174_, v_x_4175_, v_x_4176_, v_x_4177_, v_x_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4180_, lean_object* v_x_4181_, lean_object* v_x_4182_, lean_object* v_x_4183_, lean_object* v_x_4184_, lean_object* v_x_4185_){
_start:
{
size_t v_x_92656__boxed_4186_; size_t v_x_92657__boxed_4187_; lean_object* v_res_4188_; 
v_x_92656__boxed_4186_ = lean_unbox_usize(v_x_4182_);
lean_dec(v_x_4182_);
v_x_92657__boxed_4187_ = lean_unbox_usize(v_x_4183_);
lean_dec(v_x_4183_);
v_res_4188_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_4180_, v_x_4181_, v_x_92656__boxed_4186_, v_x_92657__boxed_4187_, v_x_4184_, v_x_4185_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10(lean_object* v_00_u03b1_4189_, lean_object* v_stx_4190_, lean_object* v_output_4191_, lean_object* v_x_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg(v_stx_4190_, v_output_4191_, v_x_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___boxed(lean_object* v_00_u03b1_4201_, lean_object* v_stx_4202_, lean_object* v_output_4203_, lean_object* v_x_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10(v_00_u03b1_4201_, v_stx_4202_, v_output_4203_, v_x_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(lean_object* v_as_4213_, lean_object* v_as_x27_4214_, lean_object* v_b_4215_, lean_object* v_a_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg(v_as_x27_4214_, v_b_4215_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___boxed(lean_object* v_as_4226_, lean_object* v_as_x27_4227_, lean_object* v_b_4228_, lean_object* v_a_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(v_as_4226_, v_as_x27_4227_, v_b_4228_, v_a_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v_as_x27_4227_);
lean_dec(v_as_4226_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4239_, lean_object* v_n_4240_, lean_object* v_k_4241_, lean_object* v_v_4242_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(v_n_4240_, v_k_4241_, v_v_4242_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_4244_, size_t v_depth_4245_, lean_object* v_keys_4246_, lean_object* v_vals_4247_, lean_object* v_heq_4248_, lean_object* v_i_4249_, lean_object* v_entries_4250_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_depth_4245_, v_keys_4246_, v_vals_4247_, v_i_4249_, v_entries_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_4252_, lean_object* v_depth_4253_, lean_object* v_keys_4254_, lean_object* v_vals_4255_, lean_object* v_heq_4256_, lean_object* v_i_4257_, lean_object* v_entries_4258_){
_start:
{
size_t v_depth_boxed_4259_; lean_object* v_res_4260_; 
v_depth_boxed_4259_ = lean_unbox_usize(v_depth_4253_);
lean_dec(v_depth_4253_);
v_res_4260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(v_00_u03b2_4252_, v_depth_boxed_4259_, v_keys_4254_, v_vals_4255_, v_heq_4256_, v_i_4257_, v_entries_4258_);
lean_dec_ref(v_vals_4255_);
lean_dec_ref(v_keys_4254_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18(lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg(v___y_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___boxed(lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18(v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_4277_, lean_object* v_x_4278_, lean_object* v_mkInfoTree_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg(v_x_4278_, v_mkInfoTree_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b1_4288_, lean_object* v_x_4289_, lean_object* v_mkInfoTree_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13(v_00_u03b1_4288_, v_x_4289_, v_mkInfoTree_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19(lean_object* v_00_u03b2_4299_, lean_object* v_m_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg(v_m_4300_, v_a_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___boxed(lean_object* v_00_u03b2_4303_, lean_object* v_m_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19(v_00_u03b2_4303_, v_m_4304_, v_a_4305_);
lean_dec(v_a_4305_);
lean_dec_ref(v_m_4304_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14(lean_object* v_00_u03b2_4307_, lean_object* v_x_4308_, lean_object* v_x_4309_, lean_object* v_x_4310_, lean_object* v_x_4311_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14___redArg(v_x_4308_, v_x_4309_, v_x_4310_, v_x_4311_);
return v___x_4312_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_4313_, lean_object* v_x_4314_, lean_object* v_x_4315_){
_start:
{
uint8_t v___x_4316_; 
v___x_4316_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___redArg(v_x_4314_, v_x_4315_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_4317_, lean_object* v_x_4318_, lean_object* v_x_4319_){
_start:
{
uint8_t v_res_4320_; lean_object* v_r_4321_; 
v_res_4320_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21(v_00_u03b2_4317_, v_x_4318_, v_x_4319_);
lean_dec_ref(v_x_4319_);
lean_dec_ref(v_x_4318_);
v_r_4321_ = lean_box(v_res_4320_);
return v_r_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22_spec__26(lean_object* v_00_u03b2_4322_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22___redArg(){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22___redArg___boxed(lean_object* v___dummy_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22___redArg();
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__22(lean_object* v_00_u03b2_4328_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25(lean_object* v_00_u03b2_4330_, lean_object* v_a_4331_, lean_object* v_x_4332_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25___redArg(v_a_4331_, v_x_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25___boxed(lean_object* v_00_u03b2_4334_, lean_object* v_a_4335_, lean_object* v_x_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__25(v_00_u03b2_4334_, v_a_4335_, v_x_4336_);
lean_dec(v_x_4336_);
lean_dec(v_a_4335_);
return v_res_4337_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24(lean_object* v_00_u03b2_4338_, lean_object* v_x_4339_, size_t v_x_4340_, lean_object* v_x_4341_){
_start:
{
uint8_t v___x_4342_; 
v___x_4342_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___redArg(v_x_4339_, v_x_4340_, v_x_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___boxed(lean_object* v_00_u03b2_4343_, lean_object* v_x_4344_, lean_object* v_x_4345_, lean_object* v_x_4346_){
_start:
{
size_t v_x_92809__boxed_4347_; uint8_t v_res_4348_; lean_object* v_r_4349_; 
v_x_92809__boxed_4347_ = lean_unbox_usize(v_x_4345_);
lean_dec(v_x_4345_);
v_res_4348_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24(v_00_u03b2_4343_, v_x_4344_, v_x_92809__boxed_4347_, v_x_4346_);
lean_dec_ref(v_x_4346_);
lean_dec_ref(v_x_4344_);
v_r_4349_ = lean_box(v_res_4348_);
return v_r_4349_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27(lean_object* v_00_u03b2_4350_, lean_object* v_keys_4351_, lean_object* v_vals_4352_, lean_object* v_heq_4353_, lean_object* v_i_4354_, lean_object* v_k_4355_){
_start:
{
uint8_t v___x_4356_; 
v___x_4356_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___redArg(v_keys_4351_, v_i_4354_, v_k_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___boxed(lean_object* v_00_u03b2_4357_, lean_object* v_keys_4358_, lean_object* v_vals_4359_, lean_object* v_heq_4360_, lean_object* v_i_4361_, lean_object* v_k_4362_){
_start:
{
uint8_t v_res_4363_; lean_object* v_r_4364_; 
v_res_4363_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27(v_00_u03b2_4357_, v_keys_4358_, v_vals_4359_, v_heq_4360_, v_i_4361_, v_k_4362_);
lean_dec_ref(v_k_4362_);
lean_dec_ref(v_vals_4359_);
lean_dec_ref(v_keys_4358_);
v_r_4364_ = lean_box(v_res_4363_);
return v_r_4364_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1(void){
_start:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4366_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__0));
v___x_4367_ = l_Lean_stringToMessageData(v___x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4368_, lean_object* v_mutTk_x3f_4369_, lean_object* v_initConfig_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4369_) == 0)
{
lean_object* v___x_4379_; 
v___x_4379_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4368_, v_initConfig_4370_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
return v___x_4379_;
}
else
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4380_ = lean_unsigned_to_nat(0u);
v___x_4381_ = l_Lean_Syntax_getArg(v_letConfigStx_4368_, v___x_4380_);
v___x_4382_ = l_Lean_Syntax_getArgs(v___x_4381_);
lean_dec(v___x_4381_);
v___x_4383_ = lean_array_get_size(v___x_4382_);
lean_dec_ref(v___x_4382_);
v___x_4384_ = lean_nat_dec_eq(v___x_4383_, v___x_4380_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
lean_dec_ref(v_initConfig_4370_);
v___x_4385_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1);
v___x_4386_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_letConfigStx_4368_, v___x_4385_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
lean_dec(v_letConfigStx_4368_);
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4386_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4386_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
else
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4368_, v_initConfig_4370_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
return v___x_4395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4396_, lean_object* v_mutTk_x3f_4397_, lean_object* v_initConfig_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4396_, v_mutTk_x3f_4397_, v_initConfig_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
lean_dec(v_a_4405_);
lean_dec_ref(v_a_4404_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec(v_mutTk_x3f_4397_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4423_, lean_object* v_dec_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4433_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_stx_4423_);
v___x_4434_ = l_Lean_Syntax_isOfKind(v_stx_4423_, v___x_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; 
lean_dec_ref(v_dec_4424_);
lean_dec(v_stx_4423_);
v___x_4435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4435_;
}
else
{
lean_object* v___x_4436_; lean_object* v_tk_4437_; lean_object* v_mutTk_x3f_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___x_4471_; lean_object* v___x_4472_; uint8_t v___x_4473_; 
v___x_4436_ = lean_unsigned_to_nat(0u);
v_tk_4437_ = l_Lean_Syntax_getArg(v_stx_4423_, v___x_4436_);
v___x_4471_ = lean_unsigned_to_nat(1u);
v___x_4472_ = l_Lean_Syntax_getArg(v_stx_4423_, v___x_4471_);
v___x_4473_ = l_Lean_Syntax_isNone(v___x_4472_);
if (v___x_4473_ == 0)
{
uint8_t v___x_4474_; 
lean_inc(v___x_4472_);
v___x_4474_ = l_Lean_Syntax_matchesNull(v___x_4472_, v___x_4471_);
if (v___x_4474_ == 0)
{
lean_object* v___x_4475_; 
lean_dec(v___x_4472_);
lean_dec(v_tk_4437_);
lean_dec_ref(v_dec_4424_);
lean_dec(v_stx_4423_);
v___x_4475_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4475_;
}
else
{
lean_object* v_mutTk_x3f_4476_; lean_object* v___x_4477_; 
v_mutTk_x3f_4476_ = l_Lean_Syntax_getArg(v___x_4472_, v___x_4436_);
lean_dec(v___x_4472_);
v___x_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4477_, 0, v_mutTk_x3f_4476_);
v_mutTk_x3f_4439_ = v___x_4477_;
v___y_4440_ = v_a_4425_;
v___y_4441_ = v_a_4426_;
v___y_4442_ = v_a_4427_;
v___y_4443_ = v_a_4428_;
v___y_4444_ = v_a_4429_;
v___y_4445_ = v_a_4430_;
v___y_4446_ = v_a_4431_;
goto v___jp_4438_;
}
}
else
{
lean_object* v___x_4478_; 
lean_dec(v___x_4472_);
v___x_4478_ = lean_box(0);
v_mutTk_x3f_4439_ = v___x_4478_;
v___y_4440_ = v_a_4425_;
v___y_4441_ = v_a_4426_;
v___y_4442_ = v_a_4427_;
v___y_4443_ = v_a_4428_;
v___y_4444_ = v_a_4429_;
v___y_4445_ = v_a_4430_;
v___y_4446_ = v_a_4431_;
goto v___jp_4438_;
}
v___jp_4438_:
{
lean_object* v___x_4447_; lean_object* v_config_4448_; lean_object* v___x_4449_; uint8_t v___x_4450_; 
v___x_4447_ = lean_unsigned_to_nat(2u);
v_config_4448_ = l_Lean_Syntax_getArg(v_stx_4423_, v___x_4447_);
v___x_4449_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_config_4448_);
v___x_4450_ = l_Lean_Syntax_isOfKind(v_config_4448_, v___x_4449_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4451_; 
lean_dec(v_config_4448_);
lean_dec(v_mutTk_x3f_4439_);
lean_dec(v_tk_4437_);
lean_dec_ref(v_dec_4424_);
lean_dec(v_stx_4423_);
v___x_4451_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4451_;
}
else
{
lean_object* v___x_4452_; lean_object* v_decl_4453_; lean_object* v___x_4454_; uint8_t v___x_4455_; 
v___x_4452_ = lean_unsigned_to_nat(3u);
v_decl_4453_ = l_Lean_Syntax_getArg(v_stx_4423_, v___x_4452_);
lean_dec(v_stx_4423_);
v___x_4454_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4453_);
v___x_4455_ = l_Lean_Syntax_isOfKind(v_decl_4453_, v___x_4454_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; 
lean_dec(v_decl_4453_);
lean_dec(v_config_4448_);
lean_dec(v_mutTk_x3f_4439_);
lean_dec(v_tk_4437_);
lean_dec_ref(v_dec_4424_);
v___x_4456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4456_;
}
else
{
uint8_t v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4457_ = 0;
v___x_4458_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_4459_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_config_4448_, v_mutTk_x3f_4439_, v___x_4458_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v___x_4461_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4461_, 0, v_mutTk_x3f_4439_);
lean_ctor_set_uint8(v___x_4461_, sizeof(void*)*1, v___x_4457_);
v___x_4462_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4460_, v___x_4461_, v_decl_4453_, v_tk_4437_, v_dec_4424_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
return v___x_4462_;
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec(v_decl_4453_);
lean_dec(v_mutTk_x3f_4439_);
lean_dec(v_tk_4437_);
lean_dec_ref(v_dec_4424_);
v_a_4463_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4459_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4459_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4479_, lean_object* v_dec_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_Elab_Do_elabDoLet(v_stx_4479_, v_dec_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
lean_dec(v_a_4487_);
lean_dec_ref(v_a_4486_);
lean_dec(v_a_4485_);
lean_dec_ref(v_a_4484_);
lean_dec(v_a_4483_);
lean_dec_ref(v_a_4482_);
lean_dec_ref(v_a_4481_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4497_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4498_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_4499_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4500_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4501_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4497_, v___x_4498_, v___x_4499_, v___x_4500_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased(lean_object* v_stx_4518_, lean_object* v_dec_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4528_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
lean_inc(v_stx_4518_);
v___x_4529_ = l_Lean_Syntax_isOfKind(v_stx_4518_, v___x_4528_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; 
lean_dec_ref(v_dec_4519_);
lean_dec(v_stx_4518_);
v___x_4530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4530_;
}
else
{
lean_object* v___x_4531_; lean_object* v_tk_4532_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; uint8_t v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v_t_x3f_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___x_4593_; lean_object* v_mutTk_x3f_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v___y_4602_; lean_object* v___x_4630_; uint8_t v___x_4631_; 
v___x_4531_ = lean_unsigned_to_nat(0u);
v_tk_4532_ = l_Lean_Syntax_getArg(v_stx_4518_, v___x_4531_);
v___x_4593_ = lean_unsigned_to_nat(1u);
v___x_4630_ = l_Lean_Syntax_getArg(v_stx_4518_, v___x_4593_);
v___x_4631_ = l_Lean_Syntax_isNone(v___x_4630_);
if (v___x_4631_ == 0)
{
uint8_t v___x_4632_; 
lean_inc(v___x_4630_);
v___x_4632_ = l_Lean_Syntax_matchesNull(v___x_4630_, v___x_4593_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; 
lean_dec(v___x_4630_);
lean_dec(v_tk_4532_);
lean_dec_ref(v_dec_4519_);
lean_dec(v_stx_4518_);
v___x_4633_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4633_;
}
else
{
lean_object* v_mutTk_x3f_4634_; lean_object* v___x_4635_; 
v_mutTk_x3f_4634_ = l_Lean_Syntax_getArg(v___x_4630_, v___x_4531_);
lean_dec(v___x_4630_);
v___x_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4635_, 0, v_mutTk_x3f_4634_);
v_mutTk_x3f_4595_ = v___x_4635_;
v___y_4596_ = v_a_4520_;
v___y_4597_ = v_a_4521_;
v___y_4598_ = v_a_4522_;
v___y_4599_ = v_a_4523_;
v___y_4600_ = v_a_4524_;
v___y_4601_ = v_a_4525_;
v___y_4602_ = v_a_4526_;
goto v___jp_4594_;
}
}
else
{
lean_object* v___x_4636_; 
lean_dec(v___x_4630_);
v___x_4636_ = lean_box(0);
v_mutTk_x3f_4595_ = v___x_4636_;
v___y_4596_ = v_a_4520_;
v___y_4597_ = v_a_4521_;
v___y_4598_ = v_a_4522_;
v___y_4599_ = v_a_4523_;
v___y_4600_ = v_a_4524_;
v___y_4601_ = v_a_4525_;
v___y_4602_ = v_a_4526_;
goto v___jp_4594_;
}
v___jp_4533_:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
lean_inc_ref(v___y_4542_);
v___x_4552_ = l_Array_append___redArg(v___y_4542_, v___y_4551_);
lean_dec_ref(v___y_4551_);
lean_inc(v___y_4547_);
lean_inc_n(v___y_4548_, 3);
v___x_4553_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4553_, 0, v___y_4548_);
lean_ctor_set(v___x_4553_, 1, v___y_4547_);
lean_ctor_set(v___x_4553_, 2, v___x_4552_);
v___x_4554_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___y_4548_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
lean_inc(v___y_4536_);
v___x_4556_ = l_Lean_Syntax_node5(v___y_4548_, v___y_4536_, v___y_4544_, v___y_4535_, v___x_4553_, v___x_4555_, v___y_4539_);
lean_inc(v___y_4550_);
v___x_4557_ = l_Lean_Syntax_node1(v___y_4548_, v___y_4550_, v___x_4556_);
v___x_4558_ = lean_box(0);
v___x_4559_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
lean_ctor_set_uint8(v___x_4559_, sizeof(void*)*1, v___y_4545_);
lean_ctor_set_uint8(v___x_4559_, sizeof(void*)*1 + 1, v___y_4545_);
lean_ctor_set_uint8(v___x_4559_, sizeof(void*)*1 + 2, v___y_4545_);
lean_ctor_set_uint8(v___x_4559_, sizeof(void*)*1 + 3, v___y_4545_);
lean_ctor_set_uint8(v___x_4559_, sizeof(void*)*1 + 4, v___y_4545_);
v___x_4560_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4560_, 0, v___y_4537_);
lean_ctor_set_uint8(v___x_4560_, sizeof(void*)*1, v___x_4529_);
v___x_4561_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4559_, v___x_4560_, v___x_4557_, v_tk_4532_, v_dec_4519_, v___y_4540_, v___y_4538_, v___y_4541_, v___y_4549_, v___y_4543_, v___y_4534_, v___y_4546_);
return v___x_4561_;
}
v___jp_4562_:
{
lean_object* v_ref_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v_ref_4575_ = lean_ctor_get(v___y_4573_, 2);
v___x_4576_ = lean_unsigned_to_nat(4u);
v___x_4577_ = l_Lean_Syntax_getArg(v___y_4564_, v___x_4576_);
lean_dec(v___y_4564_);
v___x_4578_ = 0;
v___x_4579_ = l_Lean_SourceInfo_fromRef(v_ref_4575_, v___x_4578_);
v___x_4580_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4581_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___y_4566_);
lean_inc_n(v___x_4579_, 2);
v___x_4582_ = l_Lean_Syntax_node1(v___x_4579_, v___y_4566_, v___y_4565_);
v___x_4583_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4584_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4579_);
lean_ctor_set(v___x_4585_, 1, v___x_4583_);
lean_ctor_set(v___x_4585_, 2, v___x_4584_);
if (lean_obj_tag(v_t_x3f_4567_) == 1)
{
lean_object* v_val_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v_val_4586_ = lean_ctor_get(v_t_x3f_4567_, 0);
lean_inc(v_val_4586_);
lean_dec_ref_known(v_t_x3f_4567_, 1);
v___x_4587_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4588_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_4579_, 2);
v___x_4589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4579_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = l_Lean_Syntax_node2(v___x_4579_, v___x_4587_, v___x_4589_, v_val_4586_);
v___x_4591_ = l_Array_mkArray1___redArg(v___x_4590_);
v___y_4534_ = v___y_4573_;
v___y_4535_ = v___x_4585_;
v___y_4536_ = v___x_4581_;
v___y_4537_ = v___y_4563_;
v___y_4538_ = v___y_4569_;
v___y_4539_ = v___x_4577_;
v___y_4540_ = v___y_4568_;
v___y_4541_ = v___y_4570_;
v___y_4542_ = v___x_4584_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___x_4582_;
v___y_4545_ = v___x_4578_;
v___y_4546_ = v___y_4574_;
v___y_4547_ = v___x_4583_;
v___y_4548_ = v___x_4579_;
v___y_4549_ = v___y_4571_;
v___y_4550_ = v___x_4580_;
v___y_4551_ = v___x_4591_;
goto v___jp_4533_;
}
else
{
lean_object* v___x_4592_; 
lean_dec(v_t_x3f_4567_);
v___x_4592_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4534_ = v___y_4573_;
v___y_4535_ = v___x_4585_;
v___y_4536_ = v___x_4581_;
v___y_4537_ = v___y_4563_;
v___y_4538_ = v___y_4569_;
v___y_4539_ = v___x_4577_;
v___y_4540_ = v___y_4568_;
v___y_4541_ = v___y_4570_;
v___y_4542_ = v___x_4584_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___x_4582_;
v___y_4545_ = v___x_4578_;
v___y_4546_ = v___y_4574_;
v___y_4547_ = v___x_4583_;
v___y_4548_ = v___x_4579_;
v___y_4549_ = v___y_4571_;
v___y_4550_ = v___x_4580_;
v___y_4551_ = v___x_4592_;
goto v___jp_4533_;
}
}
v___jp_4594_:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; 
v___x_4603_ = lean_unsigned_to_nat(2u);
v___x_4604_ = l_Lean_Syntax_getArg(v_stx_4518_, v___x_4603_);
lean_dec(v_stx_4518_);
v___x_4605_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_4604_);
v___x_4606_ = l_Lean_Syntax_isOfKind(v___x_4604_, v___x_4605_);
if (v___x_4606_ == 0)
{
lean_object* v___x_4607_; 
lean_dec(v___x_4604_);
lean_dec(v_mutTk_x3f_4595_);
lean_dec(v_tk_4532_);
lean_dec_ref(v_dec_4519_);
v___x_4607_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4607_;
}
else
{
lean_object* v___x_4608_; lean_object* v___x_4609_; uint8_t v___x_4610_; 
v___x_4608_ = l_Lean_Syntax_getArg(v___x_4604_, v___x_4531_);
v___x_4609_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_4608_);
v___x_4610_ = l_Lean_Syntax_isOfKind(v___x_4608_, v___x_4609_);
if (v___x_4610_ == 0)
{
lean_object* v___x_4611_; 
lean_dec(v___x_4608_);
lean_dec(v___x_4604_);
lean_dec(v_mutTk_x3f_4595_);
lean_dec(v_tk_4532_);
lean_dec_ref(v_dec_4519_);
v___x_4611_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4611_;
}
else
{
lean_object* v___x_4612_; lean_object* v___x_4613_; uint8_t v___x_4614_; 
v___x_4612_ = l_Lean_Syntax_getArg(v___x_4608_, v___x_4531_);
lean_dec(v___x_4608_);
v___x_4613_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4612_);
v___x_4614_ = l_Lean_Syntax_isOfKind(v___x_4612_, v___x_4613_);
if (v___x_4614_ == 0)
{
lean_object* v___x_4615_; 
lean_dec(v___x_4612_);
lean_dec(v___x_4604_);
lean_dec(v_mutTk_x3f_4595_);
lean_dec(v_tk_4532_);
lean_dec_ref(v_dec_4519_);
v___x_4615_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4615_;
}
else
{
lean_object* v___x_4616_; uint8_t v___x_4617_; 
v___x_4616_ = l_Lean_Syntax_getArg(v___x_4604_, v___x_4593_);
v___x_4617_ = l_Lean_Syntax_matchesNull(v___x_4616_, v___x_4531_);
if (v___x_4617_ == 0)
{
lean_object* v___x_4618_; 
lean_dec(v___x_4612_);
lean_dec(v___x_4604_);
lean_dec(v_mutTk_x3f_4595_);
lean_dec(v_tk_4532_);
lean_dec_ref(v_dec_4519_);
v___x_4618_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4618_;
}
else
{
lean_object* v___x_4619_; uint8_t v___x_4620_; 
v___x_4619_ = l_Lean_Syntax_getArg(v___x_4604_, v___x_4603_);
v___x_4620_ = l_Lean_Syntax_isNone(v___x_4619_);
if (v___x_4620_ == 0)
{
uint8_t v___x_4621_; 
lean_inc(v___x_4619_);
v___x_4621_ = l_Lean_Syntax_matchesNull(v___x_4619_, v___x_4593_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; 
lean_dec(v___x_4619_);
lean_dec(v___x_4612_);
lean_dec(v___x_4604_);
lean_dec(v_mutTk_x3f_4595_);
lean_dec(v_tk_4532_);
lean_dec_ref(v_dec_4519_);
v___x_4622_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4622_;
}
else
{
lean_object* v___x_4623_; lean_object* v___x_4624_; uint8_t v___x_4625_; 
v___x_4623_ = l_Lean_Syntax_getArg(v___x_4619_, v___x_4531_);
lean_dec(v___x_4619_);
v___x_4624_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4623_);
v___x_4625_ = l_Lean_Syntax_isOfKind(v___x_4623_, v___x_4624_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; 
lean_dec(v___x_4623_);
lean_dec(v___x_4612_);
lean_dec(v___x_4604_);
lean_dec(v_mutTk_x3f_4595_);
lean_dec(v_tk_4532_);
lean_dec_ref(v_dec_4519_);
v___x_4626_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4626_;
}
else
{
lean_object* v_t_x3f_4627_; lean_object* v___x_4628_; 
v_t_x3f_4627_ = l_Lean_Syntax_getArg(v___x_4623_, v___x_4593_);
lean_dec(v___x_4623_);
v___x_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4628_, 0, v_t_x3f_4627_);
v___y_4563_ = v_mutTk_x3f_4595_;
v___y_4564_ = v___x_4604_;
v___y_4565_ = v___x_4612_;
v___y_4566_ = v___x_4609_;
v_t_x3f_4567_ = v___x_4628_;
v___y_4568_ = v___y_4596_;
v___y_4569_ = v___y_4597_;
v___y_4570_ = v___y_4598_;
v___y_4571_ = v___y_4599_;
v___y_4572_ = v___y_4600_;
v___y_4573_ = v___y_4601_;
v___y_4574_ = v___y_4602_;
goto v___jp_4562_;
}
}
}
else
{
lean_object* v___x_4629_; 
lean_dec(v___x_4619_);
v___x_4629_ = lean_box(0);
v___y_4563_ = v_mutTk_x3f_4595_;
v___y_4564_ = v___x_4604_;
v___y_4565_ = v___x_4612_;
v___y_4566_ = v___x_4609_;
v_t_x3f_4567_ = v___x_4629_;
v___y_4568_ = v___y_4596_;
v___y_4569_ = v___y_4597_;
v___y_4570_ = v___y_4598_;
v___y_4571_ = v___y_4599_;
v___y_4572_ = v___y_4600_;
v___y_4573_ = v___y_4601_;
v___y_4574_ = v___y_4602_;
goto v___jp_4562_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased___boxed(lean_object* v_stx_4637_, lean_object* v_dec_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Elab_Do_elabDoErased(v_stx_4637_, v_dec_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
lean_dec_ref(v_a_4639_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1(){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4655_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4656_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4657_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1));
v___x_4658_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoErased___boxed), 10, 0);
v___x_4659_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4655_, v___x_4656_, v___x_4657_, v___x_4658_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___boxed(lean_object* v_a_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1();
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0(lean_object* v_____do__lift_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
uint8_t v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = 0;
v___x_4666_ = l_Lean_SourceInfo_fromRef(v_____do__lift_4662_, v___x_4665_);
v___x_4667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
lean_ctor_set(v___x_4667_, 1, v___y_4664_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0___boxed(lean_object* v_____do__lift_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_____do__lift_4668_, v___y_4669_, v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v_____do__lift_4668_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow(lean_object* v_stx_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v___y_4719_; lean_object* v___y_4720_; uint8_t v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___y_4729_; lean_object* v___y_4730_; lean_object* v___x_4757_; uint8_t v___x_4758_; 
v___x_4757_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
lean_inc(v_stx_4715_);
v___x_4758_ = l_Lean_Syntax_isOfKind(v_stx_4715_, v___x_4757_);
if (v___x_4758_ == 0)
{
lean_object* v___x_4759_; 
lean_dec(v_stx_4715_);
v___x_4759_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4717_);
return v___x_4759_;
}
else
{
lean_object* v___x_4760_; lean_object* v_tk_4761_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___y_4765_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4768_; lean_object* v___y_4769_; lean_object* v___y_4770_; lean_object* v___y_4771_; uint8_t v___y_4772_; lean_object* v___y_4773_; lean_object* v___y_4774_; lean_object* v___y_4775_; lean_object* v___y_4776_; lean_object* v___y_4777_; lean_object* v___y_4778_; lean_object* v___y_4779_; lean_object* v___y_4806_; lean_object* v___y_4807_; lean_object* v___y_4808_; lean_object* v___y_4809_; lean_object* v_t_x3f_4810_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___x_4846_; lean_object* v_mutTk_x3f_4848_; lean_object* v___y_4849_; lean_object* v___y_4850_; lean_object* v___x_4871_; uint8_t v___x_4872_; 
v___x_4760_ = lean_unsigned_to_nat(0u);
v_tk_4761_ = l_Lean_Syntax_getArg(v_stx_4715_, v___x_4760_);
v___x_4846_ = lean_unsigned_to_nat(1u);
v___x_4871_ = l_Lean_Syntax_getArg(v_stx_4715_, v___x_4846_);
v___x_4872_ = l_Lean_Syntax_isNone(v___x_4871_);
if (v___x_4872_ == 0)
{
uint8_t v___x_4873_; 
lean_inc(v___x_4871_);
v___x_4873_ = l_Lean_Syntax_matchesNull(v___x_4871_, v___x_4846_);
if (v___x_4873_ == 0)
{
lean_object* v___x_4874_; 
lean_dec(v___x_4871_);
lean_dec(v_tk_4761_);
lean_dec(v_stx_4715_);
v___x_4874_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4717_);
return v___x_4874_;
}
else
{
lean_object* v_mutTk_x3f_4875_; lean_object* v___x_4876_; 
v_mutTk_x3f_4875_ = l_Lean_Syntax_getArg(v___x_4871_, v___x_4760_);
lean_dec(v___x_4871_);
v___x_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4876_, 0, v_mutTk_x3f_4875_);
v_mutTk_x3f_4848_ = v___x_4876_;
v___y_4849_ = v_a_4716_;
v___y_4850_ = v_a_4717_;
goto v___jp_4847_;
}
}
else
{
lean_object* v___x_4877_; 
lean_dec(v___x_4871_);
v___x_4877_ = lean_box(0);
v_mutTk_x3f_4848_ = v___x_4877_;
v___y_4849_ = v_a_4716_;
v___y_4850_ = v_a_4717_;
goto v___jp_4847_;
}
v___jp_4762_:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v_a_4783_; lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4804_; 
lean_inc_ref(v___y_4768_);
v___x_4780_ = l_Array_append___redArg(v___y_4768_, v___y_4779_);
lean_dec_ref(v___y_4779_);
lean_inc(v___y_4767_);
lean_inc(v___y_4765_);
v___x_4781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4781_, 0, v___y_4765_);
lean_ctor_set(v___x_4781_, 1, v___y_4767_);
lean_ctor_set(v___x_4781_, 2, v___x_4780_);
v___x_4782_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v___y_4774_, v___y_4778_, v___y_4769_);
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
v_a_4784_ = lean_ctor_get(v___x_4782_, 1);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4786_ = v___x_4782_;
v_isShared_4787_ = v_isSharedCheck_4804_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_inc(v_a_4783_);
lean_dec(v___x_4782_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4804_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4788_; lean_object* v___x_4790_; 
v___x_4788_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__9));
lean_inc(v___y_4765_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set_tag(v___x_4786_, 2);
lean_ctor_set(v___x_4786_, 1, v___x_4788_);
lean_ctor_set(v___x_4786_, 0, v___y_4765_);
v___x_4790_ = v___x_4786_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___y_4765_);
lean_ctor_set(v_reuseFailAlloc_4803_, 1, v___x_4788_);
v___x_4790_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_inc(v___y_4770_);
lean_inc(v___y_4773_);
lean_inc(v___y_4765_);
v___x_4791_ = l_Lean_Syntax_node4(v___y_4765_, v___y_4773_, v___y_4770_, v___x_4781_, v___x_4790_, v___y_4771_);
lean_inc(v___y_4775_);
v___x_4792_ = l_Lean_Syntax_node4(v___y_4765_, v___y_4775_, v___y_4776_, v___y_4763_, v___y_4764_, v___x_4791_);
v___x_4793_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4794_ = l_Lean_SourceInfo_fromRef(v_tk_4761_, v___x_4758_);
lean_dec(v_tk_4761_);
v___x_4795_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__10));
v___x_4796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4794_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
if (lean_obj_tag(v___y_4777_) == 1)
{
lean_object* v_val_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v_val_4797_ = lean_ctor_get(v___y_4777_, 0);
lean_inc(v_val_4797_);
lean_dec_ref_known(v___y_4777_, 1);
v___x_4798_ = l_Lean_SourceInfo_fromRef(v_val_4797_, v___x_4758_);
lean_dec(v_val_4797_);
v___x_4799_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_4800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4798_);
lean_ctor_set(v___x_4800_, 1, v___x_4799_);
v___x_4801_ = l_Array_mkArray1___redArg(v___x_4800_);
v___y_4719_ = v_a_4784_;
v___y_4720_ = v___y_4770_;
v___y_4721_ = v___y_4772_;
v___y_4722_ = v___y_4774_;
v___y_4723_ = v_a_4783_;
v___y_4724_ = v___x_4796_;
v___y_4725_ = v___y_4766_;
v___y_4726_ = v___y_4767_;
v___y_4727_ = v___x_4793_;
v___y_4728_ = v___y_4768_;
v___y_4729_ = v___x_4792_;
v___y_4730_ = v___x_4801_;
goto v___jp_4718_;
}
else
{
lean_object* v___x_4802_; 
lean_dec(v___y_4777_);
v___x_4802_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4719_ = v_a_4784_;
v___y_4720_ = v___y_4770_;
v___y_4721_ = v___y_4772_;
v___y_4722_ = v___y_4774_;
v___y_4723_ = v_a_4783_;
v___y_4724_ = v___x_4796_;
v___y_4725_ = v___y_4766_;
v___y_4726_ = v___y_4767_;
v___y_4727_ = v___x_4793_;
v___y_4728_ = v___y_4768_;
v___y_4729_ = v___x_4792_;
v___y_4730_ = v___x_4802_;
goto v___jp_4718_;
}
}
}
}
v___jp_4805_:
{
lean_object* v_quotContext_4813_; lean_object* v_currMacroScope_4814_; lean_object* v_ref_4815_; lean_object* v___x_4816_; lean_object* v_a_4817_; lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4845_; 
v_quotContext_4813_ = lean_ctor_get(v___y_4811_, 1);
v_currMacroScope_4814_ = lean_ctor_get(v___y_4811_, 2);
v_ref_4815_ = lean_ctor_get(v___y_4811_, 5);
v___x_4816_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_ref_4815_, v___y_4811_, v___y_4812_);
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
v_a_4818_ = lean_ctor_get(v___x_4816_, 1);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4820_ = v___x_4816_;
v_isShared_4821_ = v_isSharedCheck_4845_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_inc(v_a_4817_);
lean_dec(v___x_4816_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4845_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4831_; 
v___x_4822_ = lean_unsigned_to_nat(3u);
v___x_4823_ = l_Lean_Syntax_getArg(v___y_4806_, v___x_4822_);
lean_dec(v___y_4806_);
v___x_4824_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
lean_inc(v_currMacroScope_4814_);
lean_inc(v_quotContext_4813_);
v___x_4825_ = l_Lean_addMacroScope(v_quotContext_4813_, v___x_4824_, v_currMacroScope_4814_);
v___x_4826_ = 0;
v___x_4827_ = l_Lean_mkIdentFrom(v___y_4808_, v___x_4825_, v___x_4826_);
v___x_4828_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_4829_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v_a_4817_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set_tag(v___x_4820_, 2);
lean_ctor_set(v___x_4820_, 1, v___x_4829_);
v___x_4831_ = v___x_4820_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_a_4817_);
lean_ctor_set(v_reuseFailAlloc_4844_, 1, v___x_4829_);
v___x_4831_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4832_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4833_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v_a_4817_, 2);
v___x_4834_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4834_, 0, v_a_4817_);
lean_ctor_set(v___x_4834_, 1, v___x_4832_);
lean_ctor_set(v___x_4834_, 2, v___x_4833_);
v___x_4835_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc_ref(v___x_4834_);
v___x_4836_ = l_Lean_Syntax_node1(v_a_4817_, v___x_4835_, v___x_4834_);
if (lean_obj_tag(v_t_x3f_4810_) == 1)
{
lean_object* v_val_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v_val_4837_ = lean_ctor_get(v_t_x3f_4810_, 0);
lean_inc(v_val_4837_);
lean_dec_ref_known(v_t_x3f_4810_, 1);
v___x_4838_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4839_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v_a_4817_, 2);
v___x_4840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4840_, 0, v_a_4817_);
lean_ctor_set(v___x_4840_, 1, v___x_4839_);
v___x_4841_ = l_Lean_Syntax_node2(v_a_4817_, v___x_4838_, v___x_4840_, v_val_4837_);
v___x_4842_ = l_Array_mkArray1___redArg(v___x_4841_);
v___y_4763_ = v___x_4834_;
v___y_4764_ = v___x_4836_;
v___y_4765_ = v_a_4817_;
v___y_4766_ = v___y_4808_;
v___y_4767_ = v___x_4832_;
v___y_4768_ = v___x_4833_;
v___y_4769_ = v_a_4818_;
v___y_4770_ = v___x_4827_;
v___y_4771_ = v___x_4823_;
v___y_4772_ = v___x_4826_;
v___y_4773_ = v___y_4807_;
v___y_4774_ = v_ref_4815_;
v___y_4775_ = v___x_4828_;
v___y_4776_ = v___x_4831_;
v___y_4777_ = v___y_4809_;
v___y_4778_ = v___y_4811_;
v___y_4779_ = v___x_4842_;
goto v___jp_4762_;
}
else
{
lean_object* v___x_4843_; 
lean_dec(v_t_x3f_4810_);
v___x_4843_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4763_ = v___x_4834_;
v___y_4764_ = v___x_4836_;
v___y_4765_ = v_a_4817_;
v___y_4766_ = v___y_4808_;
v___y_4767_ = v___x_4832_;
v___y_4768_ = v___x_4833_;
v___y_4769_ = v_a_4818_;
v___y_4770_ = v___x_4827_;
v___y_4771_ = v___x_4823_;
v___y_4772_ = v___x_4826_;
v___y_4773_ = v___y_4807_;
v___y_4774_ = v_ref_4815_;
v___y_4775_ = v___x_4828_;
v___y_4776_ = v___x_4831_;
v___y_4777_ = v___y_4809_;
v___y_4778_ = v___y_4811_;
v___y_4779_ = v___x_4843_;
goto v___jp_4762_;
}
}
}
}
v___jp_4847_:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; uint8_t v___x_4854_; 
v___x_4851_ = lean_unsigned_to_nat(2u);
v___x_4852_ = l_Lean_Syntax_getArg(v_stx_4715_, v___x_4851_);
lean_dec(v_stx_4715_);
v___x_4853_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_4852_);
v___x_4854_ = l_Lean_Syntax_isOfKind(v___x_4852_, v___x_4853_);
if (v___x_4854_ == 0)
{
lean_object* v___x_4855_; 
lean_dec(v___x_4852_);
lean_dec(v_mutTk_x3f_4848_);
lean_dec(v_tk_4761_);
v___x_4855_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4850_);
return v___x_4855_;
}
else
{
lean_object* v___x_4856_; lean_object* v___x_4857_; uint8_t v___x_4858_; 
v___x_4856_ = l_Lean_Syntax_getArg(v___x_4852_, v___x_4760_);
v___x_4857_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4856_);
v___x_4858_ = l_Lean_Syntax_isOfKind(v___x_4856_, v___x_4857_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; 
lean_dec(v___x_4856_);
lean_dec(v___x_4852_);
lean_dec(v_mutTk_x3f_4848_);
lean_dec(v_tk_4761_);
v___x_4859_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4850_);
return v___x_4859_;
}
else
{
lean_object* v___x_4860_; uint8_t v___x_4861_; 
v___x_4860_ = l_Lean_Syntax_getArg(v___x_4852_, v___x_4846_);
v___x_4861_ = l_Lean_Syntax_isNone(v___x_4860_);
if (v___x_4861_ == 0)
{
uint8_t v___x_4862_; 
lean_inc(v___x_4860_);
v___x_4862_ = l_Lean_Syntax_matchesNull(v___x_4860_, v___x_4846_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; 
lean_dec(v___x_4860_);
lean_dec(v___x_4856_);
lean_dec(v___x_4852_);
lean_dec(v_mutTk_x3f_4848_);
lean_dec(v_tk_4761_);
v___x_4863_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4850_);
return v___x_4863_;
}
else
{
lean_object* v___x_4864_; lean_object* v___x_4865_; uint8_t v___x_4866_; 
v___x_4864_ = l_Lean_Syntax_getArg(v___x_4860_, v___x_4760_);
lean_dec(v___x_4860_);
v___x_4865_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4864_);
v___x_4866_ = l_Lean_Syntax_isOfKind(v___x_4864_, v___x_4865_);
if (v___x_4866_ == 0)
{
lean_object* v___x_4867_; 
lean_dec(v___x_4864_);
lean_dec(v___x_4856_);
lean_dec(v___x_4852_);
lean_dec(v_mutTk_x3f_4848_);
lean_dec(v_tk_4761_);
v___x_4867_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4850_);
return v___x_4867_;
}
else
{
lean_object* v_t_x3f_4868_; lean_object* v___x_4869_; 
v_t_x3f_4868_ = l_Lean_Syntax_getArg(v___x_4864_, v___x_4846_);
lean_dec(v___x_4864_);
v___x_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4869_, 0, v_t_x3f_4868_);
v___y_4806_ = v___x_4852_;
v___y_4807_ = v___x_4853_;
v___y_4808_ = v___x_4856_;
v___y_4809_ = v_mutTk_x3f_4848_;
v_t_x3f_4810_ = v___x_4869_;
v___y_4811_ = v___y_4849_;
v___y_4812_ = v___y_4850_;
goto v___jp_4805_;
}
}
}
else
{
lean_object* v___x_4870_; 
lean_dec(v___x_4860_);
v___x_4870_ = lean_box(0);
v___y_4806_ = v___x_4852_;
v___y_4807_ = v___x_4853_;
v___y_4808_ = v___x_4856_;
v___y_4809_ = v_mutTk_x3f_4848_;
v_t_x3f_4810_ = v___x_4870_;
v___y_4811_ = v___y_4849_;
v___y_4812_ = v___y_4850_;
goto v___jp_4805_;
}
}
}
}
}
v___jp_4718_:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
lean_inc_ref_n(v___y_4728_, 3);
v___x_4731_ = l_Array_append___redArg(v___y_4728_, v___y_4730_);
lean_dec_ref(v___y_4730_);
lean_inc_n(v___y_4726_, 5);
lean_inc_n(v___y_4723_, 5);
v___x_4732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4732_, 0, v___y_4723_);
lean_ctor_set(v___x_4732_, 1, v___y_4726_);
lean_ctor_set(v___x_4732_, 2, v___x_4731_);
v___x_4733_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_4734_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
v___x_4735_ = l_Lean_Syntax_node1(v___y_4723_, v___x_4734_, v___y_4725_);
v___x_4736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4736_, 0, v___y_4723_);
lean_ctor_set(v___x_4736_, 1, v___y_4726_);
lean_ctor_set(v___x_4736_, 2, v___y_4728_);
v___x_4737_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4738_, 0, v___y_4723_);
lean_ctor_set(v___x_4738_, 1, v___x_4737_);
lean_inc_ref(v___x_4736_);
v___x_4739_ = l_Lean_Syntax_node5(v___y_4723_, v___x_4733_, v___x_4735_, v___x_4736_, v___x_4736_, v___x_4738_, v___y_4720_);
lean_inc(v___y_4727_);
v___x_4740_ = l_Lean_Syntax_node3(v___y_4723_, v___y_4727_, v___y_4724_, v___x_4732_, v___x_4739_);
v___x_4741_ = l_Lean_SourceInfo_fromRef(v___y_4722_, v___y_4721_);
v___x_4742_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_4743_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
lean_inc_n(v___x_4741_, 8);
v___x_4744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4741_);
lean_ctor_set(v___x_4744_, 1, v___x_4743_);
v___x_4745_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_4746_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_4747_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4741_);
lean_ctor_set(v___x_4748_, 1, v___x_4747_);
v___x_4749_ = l_Lean_Syntax_node1(v___x_4741_, v___y_4726_, v___x_4748_);
v___x_4750_ = l_Lean_Syntax_node2(v___x_4741_, v___x_4746_, v___y_4729_, v___x_4749_);
v___x_4751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4741_);
lean_ctor_set(v___x_4751_, 1, v___y_4726_);
lean_ctor_set(v___x_4751_, 2, v___y_4728_);
v___x_4752_ = l_Lean_Syntax_node2(v___x_4741_, v___x_4746_, v___x_4740_, v___x_4751_);
v___x_4753_ = l_Lean_Syntax_node2(v___x_4741_, v___y_4726_, v___x_4750_, v___x_4752_);
v___x_4754_ = l_Lean_Syntax_node1(v___x_4741_, v___x_4745_, v___x_4753_);
v___x_4755_ = l_Lean_Syntax_node2(v___x_4741_, v___x_4742_, v___x_4744_, v___x_4754_);
v___x_4756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
lean_ctor_set(v___x_4756_, 1, v___y_4719_);
return v___x_4756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___boxed(lean_object* v_stx_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_){
_start:
{
lean_object* v_res_4881_; 
v_res_4881_ = l_Lean_Elab_Do_expandDoErasedArrow(v_stx_4878_, v_a_4879_, v_a_4880_);
lean_dec_ref(v_a_4879_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1(){
_start:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4889_ = l_Lean_Elab_macroAttribute;
v___x_4890_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
v___x_4891_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1));
v___x_4892_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoErasedArrow___boxed), 3, 0);
v___x_4893_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4889_, v___x_4890_, v___x_4891_, v___x_4892_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___boxed(lean_object* v_a_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1();
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4902_, lean_object* v_dec_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
lean_object* v___x_4912_; uint8_t v___x_4913_; 
v___x_4912_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
lean_inc(v_stx_4902_);
v___x_4913_ = l_Lean_Syntax_isOfKind(v_stx_4902_, v___x_4912_);
if (v___x_4913_ == 0)
{
lean_object* v___x_4914_; 
lean_dec_ref(v_dec_4903_);
lean_dec(v_stx_4902_);
v___x_4914_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4914_;
}
else
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; uint8_t v___x_4918_; 
v___x_4915_ = lean_unsigned_to_nat(1u);
v___x_4916_ = l_Lean_Syntax_getArg(v_stx_4902_, v___x_4915_);
v___x_4917_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v___x_4916_);
v___x_4918_ = l_Lean_Syntax_isOfKind(v___x_4916_, v___x_4917_);
if (v___x_4918_ == 0)
{
lean_object* v___x_4919_; 
lean_dec(v___x_4916_);
lean_dec_ref(v_dec_4903_);
lean_dec(v_stx_4902_);
v___x_4919_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4919_;
}
else
{
lean_object* v___x_4920_; lean_object* v_decl_4921_; lean_object* v___x_4922_; uint8_t v___x_4923_; 
v___x_4920_ = lean_unsigned_to_nat(2u);
v_decl_4921_ = l_Lean_Syntax_getArg(v_stx_4902_, v___x_4920_);
v___x_4922_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4921_);
v___x_4923_ = l_Lean_Syntax_isOfKind(v_decl_4921_, v___x_4922_);
if (v___x_4923_ == 0)
{
lean_object* v___x_4924_; 
lean_dec(v_decl_4921_);
lean_dec(v___x_4916_);
lean_dec_ref(v_dec_4903_);
lean_dec(v_stx_4902_);
v___x_4924_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4924_;
}
else
{
lean_object* v___x_4925_; lean_object* v_tk_4926_; uint8_t v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4925_ = lean_unsigned_to_nat(0u);
v_tk_4926_ = l_Lean_Syntax_getArg(v_stx_4902_, v___x_4925_);
lean_dec(v_stx_4902_);
v___x_4927_ = 0;
v___x_4928_ = lean_box(0);
v___x_4929_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
lean_ctor_set_uint8(v___x_4929_, sizeof(void*)*1, v___x_4923_);
lean_ctor_set_uint8(v___x_4929_, sizeof(void*)*1 + 1, v___x_4927_);
lean_ctor_set_uint8(v___x_4929_, sizeof(void*)*1 + 2, v___x_4927_);
lean_ctor_set_uint8(v___x_4929_, sizeof(void*)*1 + 3, v___x_4927_);
lean_ctor_set_uint8(v___x_4929_, sizeof(void*)*1 + 4, v___x_4927_);
v___x_4930_ = l_Lean_Elab_Term_mkLetConfig(v___x_4916_, v___x_4929_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4932_ = lean_box(1);
v___x_4933_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4931_, v___x_4932_, v_decl_4921_, v_tk_4926_, v_dec_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_);
return v___x_4933_;
}
else
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4941_; 
lean_dec(v_tk_4926_);
lean_dec(v_decl_4921_);
lean_dec_ref(v_dec_4903_);
v_a_4934_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4941_ == 0)
{
v___x_4936_ = v___x_4930_;
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4930_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4939_; 
if (v_isShared_4937_ == 0)
{
v___x_4939_ = v___x_4936_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4934_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4942_, lean_object* v_dec_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l_Lean_Elab_Do_elabDoHave(v_stx_4942_, v_dec_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec_ref(v_a_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec_ref(v_a_4944_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4960_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4961_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
v___x_4962_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4963_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4964_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4960_, v___x_4961_, v___x_4962_, v___x_4963_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4969_, lean_object* v___x_4970_, lean_object* v___x_4971_, lean_object* v___x_4972_, lean_object* v_decls_4973_, lean_object* v_a_4974_, uint8_t v___x_4975_, lean_object* v_body_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
lean_object* v_ref_4985_; uint8_t v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v_ref_4985_ = lean_ctor_get(v___y_4982_, 2);
v___x_4986_ = 0;
v___x_4987_ = l_Lean_SourceInfo_fromRef(v_ref_4985_, v___x_4986_);
v___x_4988_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4989_ = l_Lean_Name_mkStr4(v___x_4969_, v___x_4970_, v___x_4971_, v___x_4988_);
v___x_4990_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4987_, 4);
v___x_4991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4987_);
lean_ctor_set(v___x_4991_, 1, v___x_4990_);
v___x_4992_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4987_);
lean_ctor_set(v___x_4993_, 1, v___x_4992_);
v___x_4994_ = l_Lean_Syntax_node2(v___x_4987_, v___x_4972_, v___x_4991_, v___x_4993_);
v___x_4995_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4987_);
lean_ctor_set(v___x_4996_, 1, v___x_4995_);
v___x_4997_ = l_Lean_Syntax_node4(v___x_4987_, v___x_4989_, v___x_4994_, v_decls_4973_, v___x_4996_, v_body_4976_);
v___x_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4998_, 0, v_a_4974_);
v___x_4999_ = l_Lean_Elab_Term_elabTerm(v___x_4997_, v___x_4998_, v___x_4975_, v___x_4975_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_5000_, lean_object* v___x_5001_, lean_object* v___x_5002_, lean_object* v___x_5003_, lean_object* v_decls_5004_, lean_object* v_a_5005_, lean_object* v___x_5006_, lean_object* v_body_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
uint8_t v___x_4419__boxed_5016_; lean_object* v_res_5017_; 
v___x_4419__boxed_5016_ = lean_unbox(v___x_5006_);
v_res_5017_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_5000_, v___x_5001_, v___x_5002_, v___x_5003_, v_decls_5004_, v_a_5005_, v___x_4419__boxed_5016_, v_body_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
lean_dec(v___y_5012_);
lean_dec_ref(v___y_5011_);
lean_dec(v___y_5010_);
lean_dec_ref(v___y_5009_);
lean_dec_ref(v___y_5008_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_5018_, lean_object* v_a_5019_){
_start:
{
if (lean_obj_tag(v_a_5018_) == 0)
{
lean_object* v___x_5020_; 
v___x_5020_ = l_List_reverse___redArg(v_a_5019_);
return v___x_5020_;
}
else
{
lean_object* v_head_5021_; lean_object* v_tail_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5031_; 
v_head_5021_ = lean_ctor_get(v_a_5018_, 0);
v_tail_5022_ = lean_ctor_get(v_a_5018_, 1);
v_isSharedCheck_5031_ = !lean_is_exclusive(v_a_5018_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5024_ = v_a_5018_;
v_isShared_5025_ = v_isSharedCheck_5031_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_tail_5022_);
lean_inc(v_head_5021_);
lean_dec(v_a_5018_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5031_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5026_; lean_object* v___x_5028_; 
v___x_5026_ = l_Lean_MessageData_ofSyntax(v_head_5021_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 1, v_a_5019_);
lean_ctor_set(v___x_5024_, 0, v___x_5026_);
v___x_5028_ = v___x_5024_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v___x_5026_);
lean_ctor_set(v_reuseFailAlloc_5030_, 1, v_a_5019_);
v___x_5028_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
v_a_5018_ = v_tail_5022_;
v_a_5019_ = v___x_5028_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5048_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_5049_ = l_Lean_stringToMessageData(v___x_5048_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_5050_, lean_object* v_dec_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_){
_start:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; uint8_t v___x_5064_; 
v___x_5060_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_5061_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_5062_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_5063_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_5050_);
v___x_5064_ = l_Lean_Syntax_isOfKind(v_stx_5050_, v___x_5063_);
if (v___x_5064_ == 0)
{
lean_object* v___x_5065_; 
lean_dec_ref(v_dec_5051_);
lean_dec(v_stx_5050_);
v___x_5065_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5065_;
}
else
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; uint8_t v___x_5069_; 
v___x_5066_ = lean_unsigned_to_nat(0u);
v___x_5067_ = l_Lean_Syntax_getArg(v_stx_5050_, v___x_5066_);
v___x_5068_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_5067_);
v___x_5069_ = l_Lean_Syntax_isOfKind(v___x_5067_, v___x_5068_);
if (v___x_5069_ == 0)
{
lean_object* v___x_5070_; 
lean_dec(v___x_5067_);
lean_dec_ref(v_dec_5051_);
lean_dec(v_stx_5050_);
v___x_5070_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5070_;
}
else
{
lean_object* v___x_5071_; lean_object* v_decls_5072_; lean_object* v___x_5073_; uint8_t v___x_5074_; 
v___x_5071_ = lean_unsigned_to_nat(1u);
v_decls_5072_ = l_Lean_Syntax_getArg(v_stx_5050_, v___x_5071_);
lean_dec(v_stx_5050_);
v___x_5073_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_5072_);
v___x_5074_ = l_Lean_Syntax_isOfKind(v_decls_5072_, v___x_5073_);
if (v___x_5074_ == 0)
{
lean_object* v___x_5075_; 
lean_dec(v_decls_5072_);
lean_dec(v___x_5067_);
lean_dec_ref(v_dec_5051_);
v___x_5075_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5075_;
}
else
{
lean_object* v_tk_5076_; lean_object* v___x_5077_; 
v_tk_5076_ = l_Lean_Syntax_getArg(v___x_5067_, v___x_5066_);
lean_dec(v___x_5067_);
v___x_5077_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_5051_, v_tk_5076_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_);
lean_dec(v_tk_5076_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5079_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref_known(v___x_5077_, 1);
lean_inc(v_decls_5072_);
v___x_5079_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_5072_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v_doBlockResultType_5081_; lean_object* v___x_5082_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref_known(v___x_5079_, 1);
v_doBlockResultType_5081_ = lean_ctor_get(v_a_5052_, 3);
lean_inc_ref(v_doBlockResultType_5081_);
v___x_5082_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_5081_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; lean_object* v___x_5084_; lean_object* v___f_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5083_);
lean_dec_ref_known(v___x_5082_, 1);
v___x_5084_ = lean_box(v___x_5074_);
v___f_5085_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_5085_, 0, v___x_5060_);
lean_closure_set(v___f_5085_, 1, v___x_5061_);
lean_closure_set(v___f_5085_, 2, v___x_5062_);
lean_closure_set(v___f_5085_, 3, v___x_5068_);
lean_closure_set(v___f_5085_, 4, v_decls_5072_);
lean_closure_set(v___f_5085_, 5, v_a_5083_);
lean_closure_set(v___f_5085_, 6, v___x_5084_);
v___x_5086_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_5087_ = lean_array_to_list(v_a_5080_);
v___x_5088_ = lean_box(0);
v___x_5089_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_5087_, v___x_5088_);
v___x_5090_ = l_Lean_MessageData_ofList(v___x_5089_);
v___x_5091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5086_);
lean_ctor_set(v___x_5091_, 1, v___x_5090_);
v___x_5092_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_5092_, 0, v_a_5078_);
v___x_5093_ = lean_box(0);
v___x_5094_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_5091_, v___x_5092_, v___f_5085_, v___x_5093_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_);
return v___x_5094_;
}
else
{
lean_dec(v_a_5080_);
lean_dec(v_a_5078_);
lean_dec(v_decls_5072_);
return v___x_5082_;
}
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
lean_dec(v_a_5078_);
lean_dec(v_decls_5072_);
v_a_5095_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_5079_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5079_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec(v_decls_5072_);
v_a_5103_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_5077_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5077_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_5111_, lean_object* v_dec_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_5111_, v_dec_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_, v_a_5119_);
lean_dec(v_a_5119_);
lean_dec_ref(v_a_5118_);
lean_dec(v_a_5117_);
lean_dec_ref(v_a_5116_);
lean_dec(v_a_5115_);
lean_dec_ref(v_a_5114_);
lean_dec_ref(v_a_5113_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5129_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5130_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_5131_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_5132_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_5133_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5129_, v___x_5130_, v___x_5131_, v___x_5132_);
return v___x_5133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_5134_){
_start:
{
lean_object* v_res_5135_; 
v_res_5135_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_5135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_5142_, lean_object* v_dec_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_){
_start:
{
lean_object* v___y_5153_; lean_object* v___y_5154_; lean_object* v___y_5155_; lean_object* v___y_5156_; lean_object* v___y_5157_; lean_object* v___y_5158_; lean_object* v___y_5159_; lean_object* v___y_5160_; lean_object* v___y_5161_; lean_object* v___y_5162_; lean_object* v___y_5163_; lean_object* v___y_5164_; uint8_t v___y_5165_; lean_object* v___y_5166_; lean_object* v___y_5167_; lean_object* v___y_5168_; lean_object* v___y_5169_; lean_object* v___x_5185_; uint8_t v___x_5186_; 
v___x_5185_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
lean_inc(v_stx_5142_);
v___x_5186_ = l_Lean_Syntax_isOfKind(v_stx_5142_, v___x_5185_);
if (v___x_5186_ == 0)
{
lean_object* v___x_5187_; 
lean_dec_ref(v_dec_5143_);
lean_dec(v_stx_5142_);
v___x_5187_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5187_;
}
else
{
lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; uint8_t v___x_5191_; 
v___x_5188_ = lean_unsigned_to_nat(0u);
v___x_5189_ = l_Lean_Syntax_getArg(v_stx_5142_, v___x_5188_);
lean_dec(v_stx_5142_);
v___x_5190_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_5189_);
v___x_5191_ = l_Lean_Syntax_isOfKind(v___x_5189_, v___x_5190_);
if (v___x_5191_ == 0)
{
lean_object* v___x_5192_; uint8_t v___x_5193_; 
v___x_5192_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5189_);
v___x_5193_ = l_Lean_Syntax_isOfKind(v___x_5189_, v___x_5192_);
if (v___x_5193_ == 0)
{
lean_object* v___x_5194_; 
lean_dec(v___x_5189_);
lean_dec_ref(v_dec_5143_);
v___x_5194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5194_;
}
else
{
lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v_decl_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; 
v___x_5195_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5196_ = lean_unsigned_to_nat(1u);
v___x_5197_ = lean_mk_empty_array_with_capacity(v___x_5196_);
v___x_5198_ = lean_array_push(v___x_5197_, v___x_5189_);
v___x_5199_ = lean_box(2);
v_decl_5200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5200_, 0, v___x_5199_);
lean_ctor_set(v_decl_5200_, 1, v___x_5195_);
lean_ctor_set(v_decl_5200_, 2, v___x_5198_);
v___x_5201_ = lean_box(0);
v___x_5202_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5202_, 0, v___x_5201_);
lean_ctor_set_uint8(v___x_5202_, sizeof(void*)*1, v___x_5191_);
lean_ctor_set_uint8(v___x_5202_, sizeof(void*)*1 + 1, v___x_5191_);
lean_ctor_set_uint8(v___x_5202_, sizeof(void*)*1 + 2, v___x_5191_);
lean_ctor_set_uint8(v___x_5202_, sizeof(void*)*1 + 3, v___x_5191_);
lean_ctor_set_uint8(v___x_5202_, sizeof(void*)*1 + 4, v___x_5191_);
v___x_5203_ = lean_box(2);
lean_inc_ref(v_decl_5200_);
v___x_5204_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5202_, v___x_5203_, v_decl_5200_, v_decl_5200_, v_dec_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_);
return v___x_5204_;
}
}
else
{
lean_object* v___x_5205_; lean_object* v___x_5206_; uint8_t v___x_5207_; 
v___x_5205_ = l_Lean_Syntax_getArg(v___x_5189_, v___x_5188_);
v___x_5206_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5205_);
v___x_5207_ = l_Lean_Syntax_isOfKind(v___x_5205_, v___x_5206_);
if (v___x_5207_ == 0)
{
lean_object* v___x_5208_; 
lean_dec(v___x_5205_);
lean_dec(v___x_5189_);
lean_dec_ref(v_dec_5143_);
v___x_5208_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5208_;
}
else
{
lean_object* v___x_5209_; lean_object* v_xType_x3f_5211_; lean_object* v___y_5212_; lean_object* v___y_5213_; lean_object* v___y_5214_; lean_object* v___y_5215_; lean_object* v___y_5216_; lean_object* v___y_5217_; lean_object* v___y_5218_; lean_object* v___x_5238_; uint8_t v___x_5239_; 
v___x_5209_ = l_Lean_Syntax_getArg(v___x_5205_, v___x_5188_);
lean_dec(v___x_5205_);
v___x_5238_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5209_);
v___x_5239_ = l_Lean_Syntax_isOfKind(v___x_5209_, v___x_5238_);
if (v___x_5239_ == 0)
{
lean_object* v___x_5240_; 
lean_dec(v___x_5209_);
lean_dec(v___x_5189_);
lean_dec_ref(v_dec_5143_);
v___x_5240_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5240_;
}
else
{
lean_object* v___x_5241_; lean_object* v___x_5242_; uint8_t v___x_5243_; 
v___x_5241_ = lean_unsigned_to_nat(1u);
v___x_5242_ = l_Lean_Syntax_getArg(v___x_5189_, v___x_5241_);
v___x_5243_ = l_Lean_Syntax_matchesNull(v___x_5242_, v___x_5188_);
if (v___x_5243_ == 0)
{
lean_object* v___x_5244_; 
lean_dec(v___x_5209_);
lean_dec(v___x_5189_);
lean_dec_ref(v_dec_5143_);
v___x_5244_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5244_;
}
else
{
lean_object* v___x_5245_; lean_object* v___x_5246_; uint8_t v___x_5247_; 
v___x_5245_ = lean_unsigned_to_nat(2u);
v___x_5246_ = l_Lean_Syntax_getArg(v___x_5189_, v___x_5245_);
v___x_5247_ = l_Lean_Syntax_isNone(v___x_5246_);
if (v___x_5247_ == 0)
{
uint8_t v___x_5248_; 
lean_inc(v___x_5246_);
v___x_5248_ = l_Lean_Syntax_matchesNull(v___x_5246_, v___x_5241_);
if (v___x_5248_ == 0)
{
lean_object* v___x_5249_; 
lean_dec(v___x_5246_);
lean_dec(v___x_5209_);
lean_dec(v___x_5189_);
lean_dec_ref(v_dec_5143_);
v___x_5249_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5249_;
}
else
{
lean_object* v___x_5250_; lean_object* v___x_5251_; uint8_t v___x_5252_; 
v___x_5250_ = l_Lean_Syntax_getArg(v___x_5246_, v___x_5188_);
lean_dec(v___x_5246_);
v___x_5251_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5250_);
v___x_5252_ = l_Lean_Syntax_isOfKind(v___x_5250_, v___x_5251_);
if (v___x_5252_ == 0)
{
lean_object* v___x_5253_; 
lean_dec(v___x_5250_);
lean_dec(v___x_5209_);
lean_dec(v___x_5189_);
lean_dec_ref(v_dec_5143_);
v___x_5253_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5253_;
}
else
{
lean_object* v_xType_x3f_5254_; lean_object* v___x_5255_; 
v_xType_x3f_5254_ = l_Lean_Syntax_getArg(v___x_5250_, v___x_5241_);
lean_dec(v___x_5250_);
v___x_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5255_, 0, v_xType_x3f_5254_);
v_xType_x3f_5211_ = v___x_5255_;
v___y_5212_ = v_a_5144_;
v___y_5213_ = v_a_5145_;
v___y_5214_ = v_a_5146_;
v___y_5215_ = v_a_5147_;
v___y_5216_ = v_a_5148_;
v___y_5217_ = v_a_5149_;
v___y_5218_ = v_a_5150_;
goto v___jp_5210_;
}
}
}
else
{
lean_object* v___x_5256_; 
lean_dec(v___x_5246_);
v___x_5256_ = lean_box(0);
v_xType_x3f_5211_ = v___x_5256_;
v___y_5212_ = v_a_5144_;
v___y_5213_ = v_a_5145_;
v___y_5214_ = v_a_5146_;
v___y_5215_ = v_a_5147_;
v___y_5216_ = v_a_5148_;
v___y_5217_ = v_a_5149_;
v___y_5218_ = v_a_5150_;
goto v___jp_5210_;
}
}
}
v___jp_5210_:
{
lean_object* v_ref_5219_; lean_object* v___x_5220_; lean_object* v_tk_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; uint8_t v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; 
v_ref_5219_ = lean_ctor_get(v___y_5217_, 2);
v___x_5220_ = lean_unsigned_to_nat(3u);
v_tk_5221_ = l_Lean_Syntax_getArg(v___x_5189_, v___x_5220_);
v___x_5222_ = lean_unsigned_to_nat(4u);
v___x_5223_ = l_Lean_Syntax_getArg(v___x_5189_, v___x_5222_);
lean_dec(v___x_5189_);
v___x_5224_ = 0;
v___x_5225_ = l_Lean_SourceInfo_fromRef(v_ref_5219_, v___x_5224_);
v___x_5226_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5225_, 2);
v___x_5227_ = l_Lean_Syntax_node1(v___x_5225_, v___x_5206_, v___x_5209_);
v___x_5228_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5229_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5225_);
lean_ctor_set(v___x_5230_, 1, v___x_5228_);
lean_ctor_set(v___x_5230_, 2, v___x_5229_);
if (lean_obj_tag(v_xType_x3f_5211_) == 1)
{
lean_object* v_val_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v_val_5231_ = lean_ctor_get(v_xType_x3f_5211_, 0);
lean_inc(v_val_5231_);
lean_dec_ref_known(v_xType_x3f_5211_, 1);
v___x_5232_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5233_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5225_, 2);
v___x_5234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5225_);
lean_ctor_set(v___x_5234_, 1, v___x_5233_);
v___x_5235_ = l_Lean_Syntax_node2(v___x_5225_, v___x_5232_, v___x_5234_, v_val_5231_);
v___x_5236_ = l_Array_mkArray1___redArg(v___x_5235_);
v___y_5153_ = v___x_5227_;
v___y_5154_ = v___x_5229_;
v___y_5155_ = v___x_5225_;
v___y_5156_ = v___y_5212_;
v___y_5157_ = v___y_5213_;
v___y_5158_ = v___x_5226_;
v___y_5159_ = v___y_5216_;
v___y_5160_ = v___x_5230_;
v___y_5161_ = v___y_5217_;
v___y_5162_ = v___x_5228_;
v___y_5163_ = v___y_5218_;
v___y_5164_ = v___x_5223_;
v___y_5165_ = v___x_5224_;
v___y_5166_ = v___y_5215_;
v___y_5167_ = v___y_5214_;
v___y_5168_ = v_tk_5221_;
v___y_5169_ = v___x_5236_;
goto v___jp_5152_;
}
else
{
lean_object* v___x_5237_; 
lean_dec(v_xType_x3f_5211_);
v___x_5237_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_5153_ = v___x_5227_;
v___y_5154_ = v___x_5229_;
v___y_5155_ = v___x_5225_;
v___y_5156_ = v___y_5212_;
v___y_5157_ = v___y_5213_;
v___y_5158_ = v___x_5226_;
v___y_5159_ = v___y_5216_;
v___y_5160_ = v___x_5230_;
v___y_5161_ = v___y_5217_;
v___y_5162_ = v___x_5228_;
v___y_5163_ = v___y_5218_;
v___y_5164_ = v___x_5223_;
v___y_5165_ = v___x_5224_;
v___y_5166_ = v___y_5215_;
v___y_5167_ = v___y_5214_;
v___y_5168_ = v_tk_5221_;
v___y_5169_ = v___x_5237_;
goto v___jp_5152_;
}
}
}
}
}
v___jp_5152_:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; 
lean_inc_ref(v___y_5154_);
v___x_5170_ = l_Array_append___redArg(v___y_5154_, v___y_5169_);
lean_dec_ref(v___y_5169_);
lean_inc(v___y_5162_);
lean_inc_n(v___y_5155_, 2);
v___x_5171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5171_, 0, v___y_5155_);
lean_ctor_set(v___x_5171_, 1, v___y_5162_);
lean_ctor_set(v___x_5171_, 2, v___x_5170_);
v___x_5172_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5173_, 0, v___y_5155_);
lean_ctor_set(v___x_5173_, 1, v___x_5172_);
lean_inc(v___y_5158_);
v___x_5174_ = l_Lean_Syntax_node5(v___y_5155_, v___y_5158_, v___y_5153_, v___y_5160_, v___x_5171_, v___x_5173_, v___y_5164_);
v___x_5175_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5176_ = lean_unsigned_to_nat(1u);
v___x_5177_ = lean_mk_empty_array_with_capacity(v___x_5176_);
v___x_5178_ = lean_array_push(v___x_5177_, v___x_5174_);
v___x_5179_ = lean_box(2);
v___x_5180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5179_);
lean_ctor_set(v___x_5180_, 1, v___x_5175_);
lean_ctor_set(v___x_5180_, 2, v___x_5178_);
v___x_5181_ = lean_box(0);
v___x_5182_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5182_, 0, v___x_5181_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*1, v___y_5165_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*1 + 1, v___y_5165_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*1 + 2, v___y_5165_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*1 + 3, v___y_5165_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*1 + 4, v___y_5165_);
v___x_5183_ = lean_box(2);
v___x_5184_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5182_, v___x_5183_, v___x_5180_, v___y_5168_, v_dec_5143_, v___y_5156_, v___y_5157_, v___y_5167_, v___y_5166_, v___y_5159_, v___y_5161_, v___y_5163_);
return v___x_5184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5257_, lean_object* v_dec_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5257_, v_dec_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_);
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec_ref(v_a_5259_);
return v_res_5267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v___x_5275_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5276_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_5277_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5278_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5279_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5275_, v___x_5276_, v___x_5277_, v___x_5278_);
return v___x_5279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
uint8_t v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5291_ = 0;
v___x_5292_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5282_, v___x_5291_);
v___x_5293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
return v___x_5293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec(v___y_5297_);
lean_dec_ref(v___y_5296_);
lean_dec_ref(v___y_5295_);
lean_dec(v_____do__lift_5294_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5304_, size_t v_sz_5305_, size_t v_i_5306_, lean_object* v_b_5307_, lean_object* v___y_5308_){
_start:
{
uint8_t v___x_5310_; 
v___x_5310_ = lean_usize_dec_lt(v_i_5306_, v_sz_5305_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5311_; 
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v_b_5307_);
return v___x_5311_;
}
else
{
lean_object* v_ref_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v_a_5315_; uint8_t v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; size_t v___x_5349_; size_t v___x_5350_; 
v_ref_5312_ = lean_ctor_get(v___y_5308_, 2);
v___x_5313_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5314_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5315_ = lean_array_uget_borrowed(v_as_5304_, v_i_5306_);
v___x_5316_ = 0;
v___x_5317_ = l_Lean_SourceInfo_fromRef(v_ref_5312_, v___x_5316_);
v___x_5318_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5319_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5320_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5321_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5317_, 17);
v___x_5322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5322_, 0, v___x_5317_);
lean_ctor_set(v___x_5322_, 1, v___x_5321_);
v___x_5323_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5317_);
lean_ctor_set(v___x_5324_, 1, v___x_5323_);
v___x_5325_ = l_Lean_Syntax_node1(v___x_5317_, v___x_5318_, v___x_5324_);
v___x_5326_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5317_);
lean_ctor_set(v___x_5327_, 1, v___x_5318_);
lean_ctor_set(v___x_5327_, 2, v___x_5326_);
lean_inc_ref_n(v___x_5327_, 3);
v___x_5328_ = l_Lean_Syntax_node1(v___x_5317_, v___x_5313_, v___x_5327_);
v___x_5329_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5330_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5331_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5315_, 2);
v___x_5332_ = l_Lean_Syntax_node1(v___x_5317_, v___x_5331_, v_a_5315_);
v___x_5333_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5334_, 0, v___x_5317_);
lean_ctor_set(v___x_5334_, 1, v___x_5333_);
v___x_5335_ = l_Lean_Syntax_node5(v___x_5317_, v___x_5330_, v___x_5332_, v___x_5327_, v___x_5327_, v___x_5334_, v_a_5315_);
v___x_5336_ = l_Lean_Syntax_node1(v___x_5317_, v___x_5329_, v___x_5335_);
v___x_5337_ = l_Lean_Syntax_node4(v___x_5317_, v___x_5320_, v___x_5322_, v___x_5325_, v___x_5328_, v___x_5336_);
v___x_5338_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5339_, 0, v___x_5317_);
lean_ctor_set(v___x_5339_, 1, v___x_5338_);
v___x_5340_ = l_Lean_Syntax_node1(v___x_5317_, v___x_5318_, v___x_5339_);
v___x_5341_ = l_Lean_Syntax_node2(v___x_5317_, v___x_5319_, v___x_5337_, v___x_5340_);
v___x_5342_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5343_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5344_, 0, v___x_5317_);
lean_ctor_set(v___x_5344_, 1, v___x_5343_);
v___x_5345_ = l_Lean_Syntax_node2(v___x_5317_, v___x_5342_, v___x_5344_, v_b_5307_);
v___x_5346_ = l_Lean_Syntax_node2(v___x_5317_, v___x_5319_, v___x_5345_, v___x_5327_);
v___x_5347_ = l_Lean_Syntax_node2(v___x_5317_, v___x_5318_, v___x_5341_, v___x_5346_);
v___x_5348_ = l_Lean_Syntax_node1(v___x_5317_, v___x_5314_, v___x_5347_);
v___x_5349_ = ((size_t)1ULL);
v___x_5350_ = lean_usize_add(v_i_5306_, v___x_5349_);
v_i_5306_ = v___x_5350_;
v_b_5307_ = v___x_5348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5352_, lean_object* v_sz_5353_, lean_object* v_i_5354_, lean_object* v_b_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
size_t v_sz_boxed_5358_; size_t v_i_boxed_5359_; lean_object* v_res_5360_; 
v_sz_boxed_5358_ = lean_unbox_usize(v_sz_5353_);
lean_dec(v_sz_5353_);
v_i_boxed_5359_ = lean_unbox_usize(v_i_5354_);
lean_dec(v_i_5354_);
v_res_5360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5352_, v_sz_boxed_5358_, v_i_boxed_5359_, v_b_5355_, v___y_5356_);
lean_dec_ref(v___y_5356_);
lean_dec_ref(v_as_5352_);
return v_res_5360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5361_, size_t v_sz_5362_, size_t v_i_5363_, lean_object* v_b_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_){
_start:
{
uint8_t v___x_5373_; 
v___x_5373_ = lean_usize_dec_lt(v_i_5363_, v_sz_5362_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; 
v___x_5374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5374_, 0, v_b_5364_);
return v___x_5374_;
}
else
{
lean_object* v_ref_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v_a_5378_; uint8_t v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; size_t v___x_5412_; size_t v___x_5413_; lean_object* v___x_5414_; 
v_ref_5375_ = lean_ctor_get(v___y_5370_, 2);
v___x_5376_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5377_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5378_ = lean_array_uget_borrowed(v_as_5361_, v_i_5363_);
v___x_5379_ = 0;
v___x_5380_ = l_Lean_SourceInfo_fromRef(v_ref_5375_, v___x_5379_);
v___x_5381_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5382_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5383_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5384_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5380_, 17);
v___x_5385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5385_, 0, v___x_5380_);
lean_ctor_set(v___x_5385_, 1, v___x_5384_);
v___x_5386_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5380_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5381_, v___x_5387_);
v___x_5389_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5390_, 0, v___x_5380_);
lean_ctor_set(v___x_5390_, 1, v___x_5381_);
lean_ctor_set(v___x_5390_, 2, v___x_5389_);
lean_inc_ref_n(v___x_5390_, 3);
v___x_5391_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5376_, v___x_5390_);
v___x_5392_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5393_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5394_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5378_, 2);
v___x_5395_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5394_, v_a_5378_);
v___x_5396_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5380_);
lean_ctor_set(v___x_5397_, 1, v___x_5396_);
v___x_5398_ = l_Lean_Syntax_node5(v___x_5380_, v___x_5393_, v___x_5395_, v___x_5390_, v___x_5390_, v___x_5397_, v_a_5378_);
v___x_5399_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5392_, v___x_5398_);
v___x_5400_ = l_Lean_Syntax_node4(v___x_5380_, v___x_5383_, v___x_5385_, v___x_5388_, v___x_5391_, v___x_5399_);
v___x_5401_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5380_);
lean_ctor_set(v___x_5402_, 1, v___x_5401_);
v___x_5403_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5381_, v___x_5402_);
v___x_5404_ = l_Lean_Syntax_node2(v___x_5380_, v___x_5382_, v___x_5400_, v___x_5403_);
v___x_5405_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5406_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5407_, 0, v___x_5380_);
lean_ctor_set(v___x_5407_, 1, v___x_5406_);
v___x_5408_ = l_Lean_Syntax_node2(v___x_5380_, v___x_5405_, v___x_5407_, v_b_5364_);
v___x_5409_ = l_Lean_Syntax_node2(v___x_5380_, v___x_5382_, v___x_5408_, v___x_5390_);
v___x_5410_ = l_Lean_Syntax_node2(v___x_5380_, v___x_5381_, v___x_5404_, v___x_5409_);
v___x_5411_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5377_, v___x_5410_);
v___x_5412_ = ((size_t)1ULL);
v___x_5413_ = lean_usize_add(v_i_5363_, v___x_5412_);
v___x_5414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5361_, v_sz_5362_, v___x_5413_, v___x_5411_, v___y_5370_);
return v___x_5414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5415_, lean_object* v_sz_5416_, lean_object* v_i_5417_, lean_object* v_b_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_){
_start:
{
size_t v_sz_boxed_5427_; size_t v_i_boxed_5428_; lean_object* v_res_5429_; 
v_sz_boxed_5427_ = lean_unbox_usize(v_sz_5416_);
lean_dec(v_sz_5416_);
v_i_boxed_5428_ = lean_unbox_usize(v_i_5417_);
lean_dec(v_i_5417_);
v_res_5429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5415_, v_sz_boxed_5427_, v_i_boxed_5428_, v_b_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
lean_dec(v___y_5425_);
lean_dec_ref(v___y_5424_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec_ref(v_as_5415_);
return v_res_5429_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5469_; lean_object* v___x_5470_; 
v___x_5469_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5470_ = l_String_toRawSubstring_x27(v___x_5469_);
return v___x_5470_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5484_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5485_ = l_String_toRawSubstring_x27(v___x_5484_);
return v___x_5485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5502_, lean_object* v_dec_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_){
_start:
{
lean_object* v___x_5512_; uint8_t v___x_5513_; 
v___x_5512_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
lean_inc(v_stx_5502_);
v___x_5513_ = l_Lean_Syntax_isOfKind(v_stx_5502_, v___x_5512_);
if (v___x_5513_ == 0)
{
lean_object* v___x_5514_; 
lean_dec_ref(v_dec_5503_);
lean_dec(v_stx_5502_);
v___x_5514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5514_;
}
else
{
lean_object* v___y_5516_; lean_object* v___y_5517_; lean_object* v___y_5518_; uint8_t v___y_5519_; lean_object* v___y_5520_; lean_object* v_body_5521_; lean_object* v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v___y_5602_; lean_object* v___y_5603_; lean_object* v___y_5604_; lean_object* v___y_5605_; lean_object* v___y_5606_; lean_object* v___y_5607_; lean_object* v___y_5608_; uint8_t v___y_5609_; lean_object* v___y_5610_; lean_object* v___y_5611_; lean_object* v___y_5612_; lean_object* v___y_5613_; lean_object* v___y_5614_; lean_object* v___y_5615_; lean_object* v_a_5616_; lean_object* v___y_5630_; lean_object* v___y_5631_; lean_object* v___y_5632_; lean_object* v___y_5633_; lean_object* v___y_5634_; lean_object* v___y_5635_; lean_object* v___y_5636_; lean_object* v___y_5637_; lean_object* v___y_5638_; lean_object* v___y_5639_; lean_object* v___y_5640_; lean_object* v___y_5641_; lean_object* v___y_5642_; lean_object* v_mutTk_x3f_5715_; lean_object* v___y_5716_; lean_object* v___y_5717_; lean_object* v___y_5718_; lean_object* v___y_5719_; lean_object* v___y_5720_; lean_object* v___y_5721_; lean_object* v___y_5722_; lean_object* v___x_5746_; lean_object* v___x_5747_; uint8_t v___x_5748_; 
v___x_5746_ = lean_unsigned_to_nat(1u);
v___x_5747_ = l_Lean_Syntax_getArg(v_stx_5502_, v___x_5746_);
v___x_5748_ = l_Lean_Syntax_isNone(v___x_5747_);
if (v___x_5748_ == 0)
{
uint8_t v___x_5749_; 
lean_inc(v___x_5747_);
v___x_5749_ = l_Lean_Syntax_matchesNull(v___x_5747_, v___x_5746_);
if (v___x_5749_ == 0)
{
lean_object* v___x_5750_; 
lean_dec(v___x_5747_);
lean_dec_ref(v_dec_5503_);
lean_dec(v_stx_5502_);
v___x_5750_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5750_;
}
else
{
lean_object* v___x_5751_; lean_object* v_mutTk_x3f_5752_; lean_object* v___x_5753_; 
v___x_5751_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5752_ = l_Lean_Syntax_getArg(v___x_5747_, v___x_5751_);
lean_dec(v___x_5747_);
v___x_5753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5753_, 0, v_mutTk_x3f_5752_);
v_mutTk_x3f_5715_ = v___x_5753_;
v___y_5716_ = v_a_5504_;
v___y_5717_ = v_a_5505_;
v___y_5718_ = v_a_5506_;
v___y_5719_ = v_a_5507_;
v___y_5720_ = v_a_5508_;
v___y_5721_ = v_a_5509_;
v___y_5722_ = v_a_5510_;
goto v___jp_5714_;
}
}
else
{
lean_object* v___x_5754_; 
lean_dec(v___x_5747_);
v___x_5754_ = lean_box(0);
v_mutTk_x3f_5715_ = v___x_5754_;
v___y_5716_ = v_a_5504_;
v___y_5717_ = v_a_5505_;
v___y_5718_ = v_a_5506_;
v___y_5719_ = v_a_5507_;
v___y_5720_ = v_a_5508_;
v___y_5721_ = v_a_5509_;
v___y_5722_ = v_a_5510_;
goto v___jp_5714_;
}
v___jp_5515_:
{
lean_object* v_eq_x3f_5529_; 
v_eq_x3f_5529_ = lean_ctor_get(v___y_5516_, 0);
lean_inc(v_eq_x3f_5529_);
lean_dec_ref(v___y_5516_);
if (lean_obj_tag(v_eq_x3f_5529_) == 1)
{
lean_object* v_val_5530_; lean_object* v_ref_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; 
v_val_5530_ = lean_ctor_get(v_eq_x3f_5529_, 0);
lean_inc(v_val_5530_);
lean_dec_ref_known(v_eq_x3f_5529_, 1);
v_ref_5531_ = lean_ctor_get(v___y_5527_, 2);
v___x_5532_ = l_Lean_SourceInfo_fromRef(v_ref_5531_, v___y_5519_);
v___x_5533_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5534_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
lean_inc_n(v___x_5532_, 19);
v___x_5535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5535_, 0, v___x_5532_);
lean_ctor_set(v___x_5535_, 1, v___x_5534_);
v___x_5536_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5537_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5538_, 0, v___x_5532_);
lean_ctor_set(v___x_5538_, 1, v___x_5536_);
lean_ctor_set(v___x_5538_, 2, v___x_5537_);
v___x_5539_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5540_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5541_, 0, v___x_5532_);
lean_ctor_set(v___x_5541_, 1, v___x_5540_);
v___x_5542_ = l_Lean_Syntax_node2(v___x_5532_, v___x_5536_, v_val_5530_, v___x_5541_);
v___x_5543_ = l_Lean_Syntax_node2(v___x_5532_, v___x_5539_, v___x_5542_, v___y_5518_);
v___x_5544_ = l_Lean_Syntax_node1(v___x_5532_, v___x_5536_, v___x_5543_);
v___x_5545_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5532_);
lean_ctor_set(v___x_5546_, 1, v___x_5545_);
v___x_5547_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5548_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5549_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5550_, 0, v___x_5532_);
lean_ctor_set(v___x_5550_, 1, v___x_5549_);
v___x_5551_ = l_Lean_Syntax_node1(v___x_5532_, v___x_5536_, v___y_5517_);
v___x_5552_ = l_Lean_Syntax_node1(v___x_5532_, v___x_5536_, v___x_5551_);
v___x_5553_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5554_, 0, v___x_5532_);
lean_ctor_set(v___x_5554_, 1, v___x_5553_);
lean_inc_ref(v___x_5554_);
lean_inc_ref(v___x_5550_);
v___x_5555_ = l_Lean_Syntax_node4(v___x_5532_, v___x_5548_, v___x_5550_, v___x_5552_, v___x_5554_, v_body_5521_);
v___x_5556_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5557_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5558_, 0, v___x_5532_);
lean_ctor_set(v___x_5558_, 1, v___x_5557_);
v___x_5559_ = l_Lean_Syntax_node1(v___x_5532_, v___x_5556_, v___x_5558_);
v___x_5560_ = l_Lean_Syntax_node1(v___x_5532_, v___x_5536_, v___x_5559_);
v___x_5561_ = l_Lean_Syntax_node1(v___x_5532_, v___x_5536_, v___x_5560_);
v___x_5562_ = l_Lean_Syntax_node4(v___x_5532_, v___x_5548_, v___x_5550_, v___x_5561_, v___x_5554_, v___y_5520_);
v___x_5563_ = l_Lean_Syntax_node2(v___x_5532_, v___x_5536_, v___x_5555_, v___x_5562_);
v___x_5564_ = l_Lean_Syntax_node1(v___x_5532_, v___x_5547_, v___x_5563_);
lean_inc_ref_n(v___x_5538_, 2);
v___x_5565_ = l_Lean_Syntax_node7(v___x_5532_, v___x_5533_, v___x_5535_, v___x_5538_, v___x_5538_, v___x_5538_, v___x_5544_, v___x_5546_, v___x_5564_);
v___x_5566_ = l_Lean_Elab_Do_elabDoElem(v___x_5565_, v_dec_5503_, v___x_5513_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_);
return v___x_5566_;
}
else
{
lean_object* v_ref_5567_; lean_object* v___x_5568_; lean_object* v_a_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; 
lean_dec(v_eq_x3f_5529_);
v_ref_5567_ = lean_ctor_get(v___y_5527_, 2);
v___x_5568_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5567_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_);
v_a_5569_ = lean_ctor_get(v___x_5568_, 0);
lean_inc_n(v_a_5569_, 18);
lean_dec_ref(v___x_5568_);
v___x_5570_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5571_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_5572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5572_, 0, v_a_5569_);
lean_ctor_set(v___x_5572_, 1, v___x_5571_);
v___x_5573_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5574_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5575_, 0, v_a_5569_);
lean_ctor_set(v___x_5575_, 1, v___x_5573_);
lean_ctor_set(v___x_5575_, 2, v___x_5574_);
v___x_5576_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
lean_inc_ref_n(v___x_5575_, 3);
v___x_5577_ = l_Lean_Syntax_node2(v_a_5569_, v___x_5576_, v___x_5575_, v___y_5518_);
v___x_5578_ = l_Lean_Syntax_node1(v_a_5569_, v___x_5573_, v___x_5577_);
v___x_5579_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5580_, 0, v_a_5569_);
lean_ctor_set(v___x_5580_, 1, v___x_5579_);
v___x_5581_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5582_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5583_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5584_, 0, v_a_5569_);
lean_ctor_set(v___x_5584_, 1, v___x_5583_);
v___x_5585_ = l_Lean_Syntax_node1(v_a_5569_, v___x_5573_, v___y_5517_);
v___x_5586_ = l_Lean_Syntax_node1(v_a_5569_, v___x_5573_, v___x_5585_);
v___x_5587_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5588_, 0, v_a_5569_);
lean_ctor_set(v___x_5588_, 1, v___x_5587_);
lean_inc_ref(v___x_5588_);
lean_inc_ref(v___x_5584_);
v___x_5589_ = l_Lean_Syntax_node4(v_a_5569_, v___x_5582_, v___x_5584_, v___x_5586_, v___x_5588_, v_body_5521_);
v___x_5590_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5591_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5592_, 0, v_a_5569_);
lean_ctor_set(v___x_5592_, 1, v___x_5591_);
v___x_5593_ = l_Lean_Syntax_node1(v_a_5569_, v___x_5590_, v___x_5592_);
v___x_5594_ = l_Lean_Syntax_node1(v_a_5569_, v___x_5573_, v___x_5593_);
v___x_5595_ = l_Lean_Syntax_node1(v_a_5569_, v___x_5573_, v___x_5594_);
v___x_5596_ = l_Lean_Syntax_node4(v_a_5569_, v___x_5582_, v___x_5584_, v___x_5595_, v___x_5588_, v___y_5520_);
v___x_5597_ = l_Lean_Syntax_node2(v_a_5569_, v___x_5573_, v___x_5589_, v___x_5596_);
v___x_5598_ = l_Lean_Syntax_node1(v_a_5569_, v___x_5581_, v___x_5597_);
v___x_5599_ = l_Lean_Syntax_node7(v_a_5569_, v___x_5570_, v___x_5572_, v___x_5575_, v___x_5575_, v___x_5575_, v___x_5578_, v___x_5580_, v___x_5598_);
v___x_5600_ = l_Lean_Elab_Do_elabDoElem(v___x_5599_, v_dec_5503_, v___x_5513_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_);
return v___x_5600_;
}
}
v___jp_5601_:
{
if (lean_obj_tag(v___y_5612_) == 0)
{
lean_dec_ref(v___y_5611_);
v___y_5516_ = v___y_5606_;
v___y_5517_ = v___y_5603_;
v___y_5518_ = v___y_5608_;
v___y_5519_ = v___y_5609_;
v___y_5520_ = v___y_5615_;
v_body_5521_ = v_a_5616_;
v___y_5522_ = v___y_5613_;
v___y_5523_ = v___y_5610_;
v___y_5524_ = v___y_5602_;
v___y_5525_ = v___y_5604_;
v___y_5526_ = v___y_5607_;
v___y_5527_ = v___y_5605_;
v___y_5528_ = v___y_5614_;
goto v___jp_5515_;
}
else
{
size_t v_sz_5617_; size_t v___x_5618_; lean_object* v___x_5619_; 
lean_dec_ref_known(v___y_5612_, 1);
v_sz_5617_ = lean_array_size(v___y_5611_);
v___x_5618_ = ((size_t)0ULL);
v___x_5619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5611_, v_sz_5617_, v___x_5618_, v_a_5616_, v___y_5613_, v___y_5610_, v___y_5602_, v___y_5604_, v___y_5607_, v___y_5605_, v___y_5614_);
lean_dec_ref(v___y_5611_);
if (lean_obj_tag(v___x_5619_) == 0)
{
lean_object* v_a_5620_; 
v_a_5620_ = lean_ctor_get(v___x_5619_, 0);
lean_inc(v_a_5620_);
lean_dec_ref_known(v___x_5619_, 1);
v___y_5516_ = v___y_5606_;
v___y_5517_ = v___y_5603_;
v___y_5518_ = v___y_5608_;
v___y_5519_ = v___y_5609_;
v___y_5520_ = v___y_5615_;
v_body_5521_ = v_a_5620_;
v___y_5522_ = v___y_5613_;
v___y_5523_ = v___y_5610_;
v___y_5524_ = v___y_5602_;
v___y_5525_ = v___y_5604_;
v___y_5526_ = v___y_5607_;
v___y_5527_ = v___y_5605_;
v___y_5528_ = v___y_5614_;
goto v___jp_5515_;
}
else
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
lean_dec(v___y_5615_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5606_);
lean_dec(v___y_5603_);
lean_dec_ref(v_dec_5503_);
v_a_5621_ = lean_ctor_get(v___x_5619_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5619_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5619_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5619_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
}
v___jp_5629_:
{
lean_object* v___x_5643_; uint8_t v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; 
v___x_5643_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_5644_ = 0;
v___x_5645_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_5646_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v___y_5634_, v___y_5638_, v___x_5645_, v___y_5639_, v___y_5637_, v___y_5630_, v___y_5632_, v___y_5635_, v___y_5633_, v___y_5640_);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_object* v_a_5647_; lean_object* v___x_5648_; 
v_a_5647_ = lean_ctor_get(v___x_5646_, 0);
lean_inc(v_a_5647_);
lean_dec_ref_known(v___x_5646_, 1);
v___x_5648_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_5647_, v___y_5632_, v___y_5635_, v___y_5633_, v___y_5640_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v___x_5649_; lean_object* v___x_5650_; 
lean_dec_ref_known(v___x_5648_, 1);
lean_inc(v___y_5638_);
v___x_5649_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5649_, 0, v___y_5638_);
lean_ctor_set_uint8(v___x_5649_, sizeof(void*)*1, v___x_5644_);
lean_inc(v___y_5631_);
v___x_5650_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5631_, v___y_5637_, v___y_5630_, v___y_5632_, v___y_5635_, v___y_5633_, v___y_5640_);
if (lean_obj_tag(v___x_5650_) == 0)
{
lean_object* v_a_5651_; lean_object* v___x_5652_; 
v_a_5651_ = lean_ctor_get(v___x_5650_, 0);
lean_inc(v_a_5651_);
lean_dec_ref_known(v___x_5650_, 1);
v___x_5652_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5649_, v_a_5651_, v___y_5639_, v___y_5637_, v___y_5630_, v___y_5632_, v___y_5635_, v___y_5633_, v___y_5640_);
lean_dec_ref_known(v___x_5649_, 1);
if (lean_obj_tag(v___x_5652_) == 0)
{
lean_dec_ref_known(v___x_5652_, 1);
if (lean_obj_tag(v___y_5642_) == 0)
{
lean_object* v_toCold_5653_; lean_object* v_ref_5654_; lean_object* v___x_5655_; lean_object* v_a_5656_; lean_object* v_quotContext_5657_; lean_object* v_currMacroScope_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; 
v_toCold_5653_ = lean_ctor_get(v___y_5633_, 0);
v_ref_5654_ = lean_ctor_get(v___y_5633_, 2);
v___x_5655_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5654_, v___y_5639_, v___y_5637_, v___y_5630_, v___y_5632_, v___y_5635_, v___y_5633_, v___y_5640_);
v_a_5656_ = lean_ctor_get(v___x_5655_, 0);
lean_inc_n(v_a_5656_, 9);
lean_dec_ref(v___x_5655_);
v_quotContext_5657_ = lean_ctor_get(v_toCold_5653_, 8);
v_currMacroScope_5658_ = lean_ctor_get(v_toCold_5653_, 9);
v___x_5659_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5660_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5661_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5662_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1));
v___x_5663_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5664_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5658_, 2);
lean_inc_n(v_quotContext_5657_, 2);
v___x_5665_ = l_Lean_addMacroScope(v_quotContext_5657_, v___x_5664_, v_currMacroScope_5658_);
v___x_5666_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5667_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5667_, 0, v_a_5656_);
lean_ctor_set(v___x_5667_, 1, v___x_5663_);
lean_ctor_set(v___x_5667_, 2, v___x_5665_);
lean_ctor_set(v___x_5667_, 3, v___x_5666_);
v___x_5668_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5669_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5670_ = l_Lean_addMacroScope(v_quotContext_5657_, v___x_5669_, v_currMacroScope_5658_);
v___x_5671_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5672_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5672_, 0, v_a_5656_);
lean_ctor_set(v___x_5672_, 1, v___x_5668_);
lean_ctor_set(v___x_5672_, 2, v___x_5670_);
lean_ctor_set(v___x_5672_, 3, v___x_5671_);
v___x_5673_ = l_Lean_Syntax_node1(v_a_5656_, v___x_5659_, v___x_5672_);
v___x_5674_ = l_Lean_Syntax_node2(v_a_5656_, v___x_5662_, v___x_5667_, v___x_5673_);
v___x_5675_ = l_Lean_Syntax_node1(v_a_5656_, v___x_5661_, v___x_5674_);
v___x_5676_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5677_, 0, v_a_5656_);
lean_ctor_set(v___x_5677_, 1, v___x_5659_);
lean_ctor_set(v___x_5677_, 2, v___x_5676_);
v___x_5678_ = l_Lean_Syntax_node2(v_a_5656_, v___x_5660_, v___x_5675_, v___x_5677_);
v___x_5679_ = l_Lean_Syntax_node1(v_a_5656_, v___x_5659_, v___x_5678_);
v___x_5680_ = l_Lean_Syntax_node1(v_a_5656_, v___x_5643_, v___x_5679_);
v___y_5602_ = v___y_5630_;
v___y_5603_ = v___y_5631_;
v___y_5604_ = v___y_5632_;
v___y_5605_ = v___y_5633_;
v___y_5606_ = v_a_5647_;
v___y_5607_ = v___y_5635_;
v___y_5608_ = v___y_5636_;
v___y_5609_ = v___x_5644_;
v___y_5610_ = v___y_5637_;
v___y_5611_ = v_a_5651_;
v___y_5612_ = v___y_5638_;
v___y_5613_ = v___y_5639_;
v___y_5614_ = v___y_5640_;
v___y_5615_ = v___y_5641_;
v_a_5616_ = v___x_5680_;
goto v___jp_5601_;
}
else
{
lean_object* v_val_5681_; 
v_val_5681_ = lean_ctor_get(v___y_5642_, 0);
lean_inc(v_val_5681_);
lean_dec_ref_known(v___y_5642_, 1);
v___y_5602_ = v___y_5630_;
v___y_5603_ = v___y_5631_;
v___y_5604_ = v___y_5632_;
v___y_5605_ = v___y_5633_;
v___y_5606_ = v_a_5647_;
v___y_5607_ = v___y_5635_;
v___y_5608_ = v___y_5636_;
v___y_5609_ = v___x_5644_;
v___y_5610_ = v___y_5637_;
v___y_5611_ = v_a_5651_;
v___y_5612_ = v___y_5638_;
v___y_5613_ = v___y_5639_;
v___y_5614_ = v___y_5640_;
v___y_5615_ = v___y_5641_;
v_a_5616_ = v_val_5681_;
goto v___jp_5601_;
}
}
else
{
lean_object* v_a_5682_; lean_object* v___x_5684_; uint8_t v_isShared_5685_; uint8_t v_isSharedCheck_5689_; 
lean_dec(v_a_5651_);
lean_dec(v_a_5647_);
lean_dec(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec(v___y_5638_);
lean_dec(v___y_5636_);
lean_dec(v___y_5631_);
lean_dec_ref(v_dec_5503_);
v_a_5682_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5689_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5689_ == 0)
{
v___x_5684_ = v___x_5652_;
v_isShared_5685_ = v_isSharedCheck_5689_;
goto v_resetjp_5683_;
}
else
{
lean_inc(v_a_5682_);
lean_dec(v___x_5652_);
v___x_5684_ = lean_box(0);
v_isShared_5685_ = v_isSharedCheck_5689_;
goto v_resetjp_5683_;
}
v_resetjp_5683_:
{
lean_object* v___x_5687_; 
if (v_isShared_5685_ == 0)
{
v___x_5687_ = v___x_5684_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v_a_5682_);
v___x_5687_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
return v___x_5687_;
}
}
}
}
else
{
lean_object* v_a_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5697_; 
lean_dec_ref_known(v___x_5649_, 1);
lean_dec(v_a_5647_);
lean_dec(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec(v___y_5638_);
lean_dec(v___y_5636_);
lean_dec(v___y_5631_);
lean_dec_ref(v_dec_5503_);
v_a_5690_ = lean_ctor_get(v___x_5650_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5650_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5692_ = v___x_5650_;
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5650_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5693_ == 0)
{
v___x_5695_ = v___x_5692_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_a_5690_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
}
}
else
{
lean_object* v_a_5698_; lean_object* v___x_5700_; uint8_t v_isShared_5701_; uint8_t v_isSharedCheck_5705_; 
lean_dec(v_a_5647_);
lean_dec(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec(v___y_5638_);
lean_dec(v___y_5636_);
lean_dec(v___y_5631_);
lean_dec_ref(v_dec_5503_);
v_a_5698_ = lean_ctor_get(v___x_5648_, 0);
v_isSharedCheck_5705_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5705_ == 0)
{
v___x_5700_ = v___x_5648_;
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
else
{
lean_inc(v_a_5698_);
lean_dec(v___x_5648_);
v___x_5700_ = lean_box(0);
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
v_resetjp_5699_:
{
lean_object* v___x_5703_; 
if (v_isShared_5701_ == 0)
{
v___x_5703_ = v___x_5700_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5698_);
v___x_5703_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
return v___x_5703_;
}
}
}
}
else
{
lean_object* v_a_5706_; lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5713_; 
lean_dec(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec(v___y_5638_);
lean_dec(v___y_5636_);
lean_dec(v___y_5631_);
lean_dec_ref(v_dec_5503_);
v_a_5706_ = lean_ctor_get(v___x_5646_, 0);
v_isSharedCheck_5713_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5713_ == 0)
{
v___x_5708_ = v___x_5646_;
v_isShared_5709_ = v_isSharedCheck_5713_;
goto v_resetjp_5707_;
}
else
{
lean_inc(v_a_5706_);
lean_dec(v___x_5646_);
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
}
v___jp_5714_:
{
lean_object* v___x_5723_; lean_object* v_cfg_5724_; lean_object* v___x_5725_; uint8_t v___x_5726_; 
v___x_5723_ = lean_unsigned_to_nat(2u);
v_cfg_5724_ = l_Lean_Syntax_getArg(v_stx_5502_, v___x_5723_);
v___x_5725_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_5724_);
v___x_5726_ = l_Lean_Syntax_isOfKind(v_cfg_5724_, v___x_5725_);
if (v___x_5726_ == 0)
{
lean_object* v___x_5727_; 
lean_dec(v_cfg_5724_);
lean_dec(v_mutTk_x3f_5715_);
lean_dec_ref(v_dec_5503_);
lean_dec(v_stx_5502_);
v___x_5727_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5727_;
}
else
{
lean_object* v___x_5728_; lean_object* v_pattern_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; 
v___x_5728_ = lean_unsigned_to_nat(3u);
v_pattern_5729_ = l_Lean_Syntax_getArg(v_stx_5502_, v___x_5728_);
v___x_5730_ = lean_unsigned_to_nat(5u);
v___x_5731_ = l_Lean_Syntax_getArg(v_stx_5502_, v___x_5730_);
v___x_5732_ = lean_unsigned_to_nat(7u);
v___x_5733_ = l_Lean_Syntax_getArg(v_stx_5502_, v___x_5732_);
v___x_5734_ = lean_unsigned_to_nat(8u);
v___x_5735_ = l_Lean_Syntax_getArg(v_stx_5502_, v___x_5734_);
lean_dec(v_stx_5502_);
v___x_5736_ = l_Lean_Syntax_getOptional_x3f(v___x_5735_);
lean_dec(v___x_5735_);
if (lean_obj_tag(v___x_5736_) == 0)
{
lean_object* v___x_5737_; 
v___x_5737_ = lean_box(0);
v___y_5630_ = v___y_5718_;
v___y_5631_ = v_pattern_5729_;
v___y_5632_ = v___y_5719_;
v___y_5633_ = v___y_5721_;
v___y_5634_ = v_cfg_5724_;
v___y_5635_ = v___y_5720_;
v___y_5636_ = v___x_5731_;
v___y_5637_ = v___y_5717_;
v___y_5638_ = v_mutTk_x3f_5715_;
v___y_5639_ = v___y_5716_;
v___y_5640_ = v___y_5722_;
v___y_5641_ = v___x_5733_;
v___y_5642_ = v___x_5737_;
goto v___jp_5629_;
}
else
{
lean_object* v_val_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5745_; 
v_val_5738_ = lean_ctor_get(v___x_5736_, 0);
v_isSharedCheck_5745_ = !lean_is_exclusive(v___x_5736_);
if (v_isSharedCheck_5745_ == 0)
{
v___x_5740_ = v___x_5736_;
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_val_5738_);
lean_dec(v___x_5736_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___x_5743_; 
if (v_isShared_5741_ == 0)
{
v___x_5743_ = v___x_5740_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5744_; 
v_reuseFailAlloc_5744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5744_, 0, v_val_5738_);
v___x_5743_ = v_reuseFailAlloc_5744_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
v___y_5630_ = v___y_5718_;
v___y_5631_ = v_pattern_5729_;
v___y_5632_ = v___y_5719_;
v___y_5633_ = v___y_5721_;
v___y_5634_ = v_cfg_5724_;
v___y_5635_ = v___y_5720_;
v___y_5636_ = v___x_5731_;
v___y_5637_ = v___y_5717_;
v___y_5638_ = v_mutTk_x3f_5715_;
v___y_5639_ = v___y_5716_;
v___y_5640_ = v___y_5722_;
v___y_5641_ = v___x_5733_;
v___y_5642_ = v___x_5743_;
goto v___jp_5629_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5755_, lean_object* v_dec_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5755_, v_dec_5756_, v_a_5757_, v_a_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_);
lean_dec(v_a_5763_);
lean_dec_ref(v_a_5762_);
lean_dec(v_a_5761_);
lean_dec_ref(v_a_5760_);
lean_dec(v_a_5759_);
lean_dec_ref(v_a_5758_);
lean_dec_ref(v_a_5757_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5766_, size_t v_sz_5767_, size_t v_i_5768_, lean_object* v_b_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_){
_start:
{
lean_object* v___x_5778_; 
v___x_5778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5766_, v_sz_5767_, v_i_5768_, v_b_5769_, v___y_5775_);
return v___x_5778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5779_, lean_object* v_sz_5780_, lean_object* v_i_5781_, lean_object* v_b_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_){
_start:
{
size_t v_sz_boxed_5791_; size_t v_i_boxed_5792_; lean_object* v_res_5793_; 
v_sz_boxed_5791_ = lean_unbox_usize(v_sz_5780_);
lean_dec(v_sz_5780_);
v_i_boxed_5792_ = lean_unbox_usize(v_i_5781_);
lean_dec(v_i_5781_);
v_res_5793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5779_, v_sz_boxed_5791_, v_i_boxed_5792_, v_b_5782_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
lean_dec_ref(v___y_5783_);
lean_dec_ref(v_as_5779_);
return v_res_5793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; 
v___x_5801_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5802_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
v___x_5803_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5804_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5805_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5801_, v___x_5802_, v___x_5803_, v___x_5804_);
return v___x_5805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5806_){
_start:
{
lean_object* v_res_5807_; 
v_res_5807_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0(lean_object* v_otherwise_x3f_5808_, uint8_t v___x_5809_, lean_object* v___x_5810_, lean_object* v___x_5811_, lean_object* v___x_5812_, lean_object* v___x_5813_, lean_object* v___x_5814_, lean_object* v___x_5815_, lean_object* v_dec_5816_, uint8_t v___x_5817_, lean_object* v_mutTk_x3f_5818_, lean_object* v___x_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5808_) == 0)
{
lean_object* v_ref_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___y_5838_; 
lean_dec(v___y_5820_);
v_ref_5829_ = lean_ctor_get(v___y_5826_, 2);
v___x_5830_ = l_Lean_SourceInfo_fromRef(v_ref_5829_, v___x_5809_);
v___x_5831_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5812_);
lean_inc_ref(v___x_5811_);
lean_inc_ref(v___x_5810_);
v___x_5832_ = l_Lean_Name_mkStr4(v___x_5810_, v___x_5811_, v___x_5812_, v___x_5831_);
v___x_5833_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5830_);
v___x_5834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5830_);
lean_ctor_set(v___x_5834_, 1, v___x_5833_);
v___x_5835_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5836_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5818_) == 1)
{
lean_object* v_val_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; 
v_val_5853_ = lean_ctor_get(v_mutTk_x3f_5818_, 0);
v___x_5854_ = l_Lean_SourceInfo_fromRef(v_val_5853_, v___x_5817_);
v___x_5855_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5854_);
lean_ctor_set(v___x_5856_, 1, v___x_5855_);
v___x_5857_ = l_Array_mkArray1___redArg(v___x_5856_);
v___y_5838_ = v___x_5857_;
goto v___jp_5837_;
}
else
{
lean_object* v___x_5858_; 
v___x_5858_ = lean_mk_empty_array_with_capacity(v___x_5819_);
v___y_5838_ = v___x_5858_;
goto v___jp_5837_;
}
v___jp_5837_:
{
lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5839_ = l_Array_append___redArg(v___x_5836_, v___y_5838_);
lean_dec_ref(v___y_5838_);
lean_inc_n(v___x_5830_, 6);
v___x_5840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5840_, 0, v___x_5830_);
lean_ctor_set(v___x_5840_, 1, v___x_5835_);
lean_ctor_set(v___x_5840_, 2, v___x_5839_);
v___x_5841_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5841_, 0, v___x_5830_);
lean_ctor_set(v___x_5841_, 1, v___x_5835_);
lean_ctor_set(v___x_5841_, 2, v___x_5836_);
lean_inc_ref_n(v___x_5841_, 2);
v___x_5842_ = l_Lean_Syntax_node1(v___x_5830_, v___x_5813_, v___x_5841_);
v___x_5843_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5812_);
lean_inc_ref(v___x_5811_);
lean_inc_ref(v___x_5810_);
v___x_5844_ = l_Lean_Name_mkStr4(v___x_5810_, v___x_5811_, v___x_5812_, v___x_5843_);
v___x_5845_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5846_ = l_Lean_Name_mkStr4(v___x_5810_, v___x_5811_, v___x_5812_, v___x_5845_);
v___x_5847_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5848_, 0, v___x_5830_);
lean_ctor_set(v___x_5848_, 1, v___x_5847_);
v___x_5849_ = l_Lean_Syntax_node5(v___x_5830_, v___x_5846_, v___x_5814_, v___x_5841_, v___x_5841_, v___x_5848_, v___x_5815_);
v___x_5850_ = l_Lean_Syntax_node1(v___x_5830_, v___x_5844_, v___x_5849_);
v___x_5851_ = l_Lean_Syntax_node4(v___x_5830_, v___x_5832_, v___x_5834_, v___x_5840_, v___x_5842_, v___x_5850_);
v___x_5852_ = l_Lean_Elab_Do_elabDoElem(v___x_5851_, v_dec_5816_, v___x_5817_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
return v___x_5852_;
}
}
else
{
lean_object* v_val_5859_; lean_object* v_ref_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___y_5869_; lean_object* v___y_5870_; lean_object* v___y_5871_; lean_object* v___y_5872_; lean_object* v___y_5873_; lean_object* v___y_5890_; 
v_val_5859_ = lean_ctor_get(v_otherwise_x3f_5808_, 0);
lean_inc(v_val_5859_);
lean_dec_ref_known(v_otherwise_x3f_5808_, 1);
v_ref_5860_ = lean_ctor_get(v___y_5826_, 2);
v___x_5861_ = l_Lean_SourceInfo_fromRef(v_ref_5860_, v___x_5809_);
v___x_5862_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5863_ = l_Lean_Name_mkStr4(v___x_5810_, v___x_5811_, v___x_5812_, v___x_5862_);
v___x_5864_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5861_);
v___x_5865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5861_);
lean_ctor_set(v___x_5865_, 1, v___x_5864_);
v___x_5866_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5867_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5818_) == 1)
{
lean_object* v_val_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; 
v_val_5903_ = lean_ctor_get(v_mutTk_x3f_5818_, 0);
v___x_5904_ = l_Lean_SourceInfo_fromRef(v_val_5903_, v___x_5817_);
v___x_5905_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5904_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v___x_5907_ = l_Array_mkArray1___redArg(v___x_5906_);
v___y_5890_ = v___x_5907_;
goto v___jp_5889_;
}
else
{
lean_object* v___x_5908_; 
v___x_5908_ = lean_mk_empty_array_with_capacity(v___x_5819_);
v___y_5890_ = v___x_5908_;
goto v___jp_5889_;
}
v___jp_5868_:
{
lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; 
v___x_5874_ = l_Array_append___redArg(v___x_5867_, v___y_5873_);
lean_dec_ref(v___y_5873_);
lean_inc(v___x_5861_);
v___x_5875_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5861_);
lean_ctor_set(v___x_5875_, 1, v___x_5866_);
lean_ctor_set(v___x_5875_, 2, v___x_5874_);
v___x_5876_ = lean_unsigned_to_nat(9u);
v___x_5877_ = lean_mk_empty_array_with_capacity(v___x_5876_);
v___x_5878_ = lean_array_push(v___x_5877_, v___x_5865_);
v___x_5879_ = lean_array_push(v___x_5878_, v___y_5872_);
v___x_5880_ = lean_array_push(v___x_5879_, v___y_5871_);
v___x_5881_ = lean_array_push(v___x_5880_, v___x_5814_);
v___x_5882_ = lean_array_push(v___x_5881_, v___y_5870_);
v___x_5883_ = lean_array_push(v___x_5882_, v___x_5815_);
v___x_5884_ = lean_array_push(v___x_5883_, v___y_5869_);
v___x_5885_ = lean_array_push(v___x_5884_, v_val_5859_);
v___x_5886_ = lean_array_push(v___x_5885_, v___x_5875_);
v___x_5887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5887_, 0, v___x_5861_);
lean_ctor_set(v___x_5887_, 1, v___x_5863_);
lean_ctor_set(v___x_5887_, 2, v___x_5886_);
v___x_5888_ = l_Lean_Elab_Do_elabDoElem(v___x_5887_, v_dec_5816_, v___x_5817_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
return v___x_5888_;
}
v___jp_5889_:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; 
v___x_5891_ = l_Array_append___redArg(v___x_5867_, v___y_5890_);
lean_dec_ref(v___y_5890_);
lean_inc_n(v___x_5861_, 5);
v___x_5892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5861_);
lean_ctor_set(v___x_5892_, 1, v___x_5866_);
lean_ctor_set(v___x_5892_, 2, v___x_5891_);
v___x_5893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5861_);
lean_ctor_set(v___x_5893_, 1, v___x_5866_);
lean_ctor_set(v___x_5893_, 2, v___x_5867_);
v___x_5894_ = l_Lean_Syntax_node1(v___x_5861_, v___x_5813_, v___x_5893_);
v___x_5895_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5861_);
lean_ctor_set(v___x_5896_, 1, v___x_5895_);
v___x_5897_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5898_, 0, v___x_5861_);
lean_ctor_set(v___x_5898_, 1, v___x_5897_);
if (lean_obj_tag(v___y_5820_) == 0)
{
lean_object* v___x_5899_; 
v___x_5899_ = lean_mk_empty_array_with_capacity(v___x_5819_);
v___y_5869_ = v___x_5898_;
v___y_5870_ = v___x_5896_;
v___y_5871_ = v___x_5894_;
v___y_5872_ = v___x_5892_;
v___y_5873_ = v___x_5899_;
goto v___jp_5868_;
}
else
{
lean_object* v_val_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; 
v_val_5900_ = lean_ctor_get(v___y_5820_, 0);
lean_inc(v_val_5900_);
lean_dec_ref_known(v___y_5820_, 1);
v___x_5901_ = lean_mk_empty_array_with_capacity(v___x_5819_);
v___x_5902_ = lean_array_push(v___x_5901_, v_val_5900_);
v___y_5869_ = v___x_5898_;
v___y_5870_ = v___x_5896_;
v___y_5871_ = v___x_5894_;
v___y_5872_ = v___x_5892_;
v___y_5873_ = v___x_5902_;
goto v___jp_5868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_5909_ = _args[0];
lean_object* v___x_5910_ = _args[1];
lean_object* v___x_5911_ = _args[2];
lean_object* v___x_5912_ = _args[3];
lean_object* v___x_5913_ = _args[4];
lean_object* v___x_5914_ = _args[5];
lean_object* v___x_5915_ = _args[6];
lean_object* v___x_5916_ = _args[7];
lean_object* v_dec_5917_ = _args[8];
lean_object* v___x_5918_ = _args[9];
lean_object* v_mutTk_x3f_5919_ = _args[10];
lean_object* v___x_5920_ = _args[11];
lean_object* v___y_5921_ = _args[12];
lean_object* v___y_5922_ = _args[13];
lean_object* v___y_5923_ = _args[14];
lean_object* v___y_5924_ = _args[15];
lean_object* v___y_5925_ = _args[16];
lean_object* v___y_5926_ = _args[17];
lean_object* v___y_5927_ = _args[18];
lean_object* v___y_5928_ = _args[19];
lean_object* v___y_5929_ = _args[20];
_start:
{
uint8_t v___x_22525__boxed_5930_; uint8_t v___x_22532__boxed_5931_; lean_object* v_res_5932_; 
v___x_22525__boxed_5930_ = lean_unbox(v___x_5910_);
v___x_22532__boxed_5931_ = lean_unbox(v___x_5918_);
v_res_5932_ = l_Lean_Elab_Do_elabDoLetArrow___lam__0(v_otherwise_x3f_5909_, v___x_22525__boxed_5930_, v___x_5911_, v___x_5912_, v___x_5913_, v___x_5914_, v___x_5915_, v___x_5916_, v_dec_5917_, v___x_22532__boxed_5931_, v_mutTk_x3f_5919_, v___x_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_);
lean_dec(v___y_5928_);
lean_dec_ref(v___y_5927_);
lean_dec(v___y_5926_);
lean_dec_ref(v___y_5925_);
lean_dec(v___y_5924_);
lean_dec_ref(v___y_5923_);
lean_dec_ref(v___y_5922_);
lean_dec(v___x_5920_);
lean_dec(v_mutTk_x3f_5919_);
return v_res_5932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1(lean_object* v_otherwise_x3f_5933_, uint8_t v___x_5934_, lean_object* v___x_5935_, lean_object* v___x_5936_, lean_object* v___x_5937_, lean_object* v___x_5938_, lean_object* v___x_5939_, lean_object* v___x_5940_, lean_object* v_dec_5941_, uint8_t v___x_5942_, lean_object* v_mutTk_x3f_5943_, lean_object* v___x_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5933_) == 0)
{
lean_object* v_ref_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___y_5963_; 
lean_dec(v___y_5945_);
v_ref_5954_ = lean_ctor_get(v___y_5951_, 2);
v___x_5955_ = l_Lean_SourceInfo_fromRef(v_ref_5954_, v___x_5934_);
v___x_5956_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5937_);
lean_inc_ref(v___x_5936_);
lean_inc_ref(v___x_5935_);
v___x_5957_ = l_Lean_Name_mkStr4(v___x_5935_, v___x_5936_, v___x_5937_, v___x_5956_);
v___x_5958_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5955_);
v___x_5959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5955_);
lean_ctor_set(v___x_5959_, 1, v___x_5958_);
v___x_5960_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5961_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5943_) == 1)
{
lean_object* v_val_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; 
v_val_5978_ = lean_ctor_get(v_mutTk_x3f_5943_, 0);
v___x_5979_ = l_Lean_SourceInfo_fromRef(v_val_5978_, v___x_5942_);
v___x_5980_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5979_);
lean_ctor_set(v___x_5981_, 1, v___x_5980_);
v___x_5982_ = l_Array_mkArray1___redArg(v___x_5981_);
v___y_5963_ = v___x_5982_;
goto v___jp_5962_;
}
else
{
lean_object* v___x_5983_; 
v___x_5983_ = lean_mk_empty_array_with_capacity(v___x_5944_);
v___y_5963_ = v___x_5983_;
goto v___jp_5962_;
}
v___jp_5962_:
{
lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___x_5964_ = l_Array_append___redArg(v___x_5961_, v___y_5963_);
lean_dec_ref(v___y_5963_);
lean_inc_n(v___x_5955_, 6);
v___x_5965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5955_);
lean_ctor_set(v___x_5965_, 1, v___x_5960_);
lean_ctor_set(v___x_5965_, 2, v___x_5964_);
v___x_5966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5955_);
lean_ctor_set(v___x_5966_, 1, v___x_5960_);
lean_ctor_set(v___x_5966_, 2, v___x_5961_);
lean_inc_ref_n(v___x_5966_, 2);
v___x_5967_ = l_Lean_Syntax_node1(v___x_5955_, v___x_5938_, v___x_5966_);
v___x_5968_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5937_);
lean_inc_ref(v___x_5936_);
lean_inc_ref(v___x_5935_);
v___x_5969_ = l_Lean_Name_mkStr4(v___x_5935_, v___x_5936_, v___x_5937_, v___x_5968_);
v___x_5970_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5971_ = l_Lean_Name_mkStr4(v___x_5935_, v___x_5936_, v___x_5937_, v___x_5970_);
v___x_5972_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5955_);
lean_ctor_set(v___x_5973_, 1, v___x_5972_);
v___x_5974_ = l_Lean_Syntax_node5(v___x_5955_, v___x_5971_, v___x_5939_, v___x_5966_, v___x_5966_, v___x_5973_, v___x_5940_);
v___x_5975_ = l_Lean_Syntax_node1(v___x_5955_, v___x_5969_, v___x_5974_);
v___x_5976_ = l_Lean_Syntax_node4(v___x_5955_, v___x_5957_, v___x_5959_, v___x_5965_, v___x_5967_, v___x_5975_);
v___x_5977_ = l_Lean_Elab_Do_elabDoElem(v___x_5976_, v_dec_5941_, v___x_5942_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
return v___x_5977_;
}
}
else
{
lean_object* v_val_5984_; lean_object* v_ref_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___y_5994_; lean_object* v___y_5995_; lean_object* v___y_5996_; lean_object* v___y_5997_; lean_object* v___y_5998_; lean_object* v___y_6015_; 
v_val_5984_ = lean_ctor_get(v_otherwise_x3f_5933_, 0);
lean_inc(v_val_5984_);
lean_dec_ref_known(v_otherwise_x3f_5933_, 1);
v_ref_5985_ = lean_ctor_get(v___y_5951_, 2);
v___x_5986_ = l_Lean_SourceInfo_fromRef(v_ref_5985_, v___x_5934_);
v___x_5987_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5988_ = l_Lean_Name_mkStr4(v___x_5935_, v___x_5936_, v___x_5937_, v___x_5987_);
v___x_5989_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5986_);
v___x_5990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5986_);
lean_ctor_set(v___x_5990_, 1, v___x_5989_);
v___x_5991_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5992_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5943_) == 1)
{
lean_object* v_val_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; 
v_val_6028_ = lean_ctor_get(v_mutTk_x3f_5943_, 0);
v___x_6029_ = l_Lean_SourceInfo_fromRef(v_val_6028_, v___x_5942_);
v___x_6030_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_6031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6029_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = l_Array_mkArray1___redArg(v___x_6031_);
v___y_6015_ = v___x_6032_;
goto v___jp_6014_;
}
else
{
lean_object* v___x_6033_; 
v___x_6033_ = lean_mk_empty_array_with_capacity(v___x_5944_);
v___y_6015_ = v___x_6033_;
goto v___jp_6014_;
}
v___jp_5993_:
{
lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; 
v___x_5999_ = l_Array_append___redArg(v___x_5992_, v___y_5998_);
lean_dec_ref(v___y_5998_);
lean_inc(v___x_5986_);
v___x_6000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6000_, 0, v___x_5986_);
lean_ctor_set(v___x_6000_, 1, v___x_5991_);
lean_ctor_set(v___x_6000_, 2, v___x_5999_);
v___x_6001_ = lean_unsigned_to_nat(9u);
v___x_6002_ = lean_mk_empty_array_with_capacity(v___x_6001_);
v___x_6003_ = lean_array_push(v___x_6002_, v___x_5990_);
v___x_6004_ = lean_array_push(v___x_6003_, v___y_5995_);
v___x_6005_ = lean_array_push(v___x_6004_, v___y_5996_);
v___x_6006_ = lean_array_push(v___x_6005_, v___x_5939_);
v___x_6007_ = lean_array_push(v___x_6006_, v___y_5997_);
v___x_6008_ = lean_array_push(v___x_6007_, v___x_5940_);
v___x_6009_ = lean_array_push(v___x_6008_, v___y_5994_);
v___x_6010_ = lean_array_push(v___x_6009_, v_val_5984_);
v___x_6011_ = lean_array_push(v___x_6010_, v___x_6000_);
v___x_6012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6012_, 0, v___x_5986_);
lean_ctor_set(v___x_6012_, 1, v___x_5988_);
lean_ctor_set(v___x_6012_, 2, v___x_6011_);
v___x_6013_ = l_Lean_Elab_Do_elabDoElem(v___x_6012_, v_dec_5941_, v___x_5942_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
return v___x_6013_;
}
v___jp_6014_:
{
lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6016_ = l_Array_append___redArg(v___x_5992_, v___y_6015_);
lean_dec_ref(v___y_6015_);
lean_inc_n(v___x_5986_, 5);
v___x_6017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6017_, 0, v___x_5986_);
lean_ctor_set(v___x_6017_, 1, v___x_5991_);
lean_ctor_set(v___x_6017_, 2, v___x_6016_);
v___x_6018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6018_, 0, v___x_5986_);
lean_ctor_set(v___x_6018_, 1, v___x_5991_);
lean_ctor_set(v___x_6018_, 2, v___x_5992_);
v___x_6019_ = l_Lean_Syntax_node1(v___x_5986_, v___x_5938_, v___x_6018_);
v___x_6020_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_5986_);
lean_ctor_set(v___x_6021_, 1, v___x_6020_);
v___x_6022_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_6023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_5986_);
lean_ctor_set(v___x_6023_, 1, v___x_6022_);
if (lean_obj_tag(v___y_5945_) == 0)
{
lean_object* v___x_6024_; 
v___x_6024_ = lean_mk_empty_array_with_capacity(v___x_5944_);
v___y_5994_ = v___x_6023_;
v___y_5995_ = v___x_6017_;
v___y_5996_ = v___x_6019_;
v___y_5997_ = v___x_6021_;
v___y_5998_ = v___x_6024_;
goto v___jp_5993_;
}
else
{
lean_object* v_val_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; 
v_val_6025_ = lean_ctor_get(v___y_5945_, 0);
lean_inc(v_val_6025_);
lean_dec_ref_known(v___y_5945_, 1);
v___x_6026_ = lean_mk_empty_array_with_capacity(v___x_5944_);
v___x_6027_ = lean_array_push(v___x_6026_, v_val_6025_);
v___y_5994_ = v___x_6023_;
v___y_5995_ = v___x_6017_;
v___y_5996_ = v___x_6019_;
v___y_5997_ = v___x_6021_;
v___y_5998_ = v___x_6027_;
goto v___jp_5993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_6034_ = _args[0];
lean_object* v___x_6035_ = _args[1];
lean_object* v___x_6036_ = _args[2];
lean_object* v___x_6037_ = _args[3];
lean_object* v___x_6038_ = _args[4];
lean_object* v___x_6039_ = _args[5];
lean_object* v___x_6040_ = _args[6];
lean_object* v___x_6041_ = _args[7];
lean_object* v_dec_6042_ = _args[8];
lean_object* v___x_6043_ = _args[9];
lean_object* v_mutTk_x3f_6044_ = _args[10];
lean_object* v___x_6045_ = _args[11];
lean_object* v___y_6046_ = _args[12];
lean_object* v___y_6047_ = _args[13];
lean_object* v___y_6048_ = _args[14];
lean_object* v___y_6049_ = _args[15];
lean_object* v___y_6050_ = _args[16];
lean_object* v___y_6051_ = _args[17];
lean_object* v___y_6052_ = _args[18];
lean_object* v___y_6053_ = _args[19];
lean_object* v___y_6054_ = _args[20];
_start:
{
uint8_t v___x_22756__boxed_6055_; uint8_t v___x_22763__boxed_6056_; lean_object* v_res_6057_; 
v___x_22756__boxed_6055_ = lean_unbox(v___x_6035_);
v___x_22763__boxed_6056_ = lean_unbox(v___x_6043_);
v_res_6057_ = l_Lean_Elab_Do_elabDoLetArrow___lam__1(v_otherwise_x3f_6034_, v___x_22756__boxed_6055_, v___x_6036_, v___x_6037_, v___x_6038_, v___x_6039_, v___x_6040_, v___x_6041_, v_dec_6042_, v___x_22763__boxed_6056_, v_mutTk_x3f_6044_, v___x_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_);
lean_dec(v___y_6053_);
lean_dec_ref(v___y_6052_);
lean_dec(v___y_6051_);
lean_dec_ref(v___y_6050_);
lean_dec(v___y_6049_);
lean_dec_ref(v___y_6048_);
lean_dec_ref(v___y_6047_);
lean_dec(v___x_6045_);
lean_dec(v_mutTk_x3f_6044_);
return v_res_6057_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1(void){
_start:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6059_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__0));
v___x_6060_ = l_Lean_stringToMessageData(v___x_6059_);
return v___x_6060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_6067_, lean_object* v_dec_6068_, lean_object* v_a_6069_, lean_object* v_a_6070_, lean_object* v_a_6071_, lean_object* v_a_6072_, lean_object* v_a_6073_, lean_object* v_a_6074_, lean_object* v_a_6075_){
_start:
{
lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; uint8_t v___x_6081_; 
v___x_6077_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_6078_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_6079_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_6080_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
lean_inc(v_stx_6067_);
v___x_6081_ = l_Lean_Syntax_isOfKind(v_stx_6067_, v___x_6080_);
if (v___x_6081_ == 0)
{
lean_object* v___x_6082_; 
lean_dec_ref(v_dec_6068_);
lean_dec(v_stx_6067_);
v___x_6082_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6082_;
}
else
{
lean_object* v___x_6083_; uint8_t v___y_6085_; uint8_t v___y_6086_; lean_object* v___y_6087_; lean_object* v___y_6088_; lean_object* v___y_6089_; lean_object* v___y_6090_; lean_object* v___y_6091_; lean_object* v___y_6092_; lean_object* v___y_6093_; lean_object* v___y_6094_; lean_object* v___y_6095_; lean_object* v___y_6096_; lean_object* v___y_6097_; lean_object* v___y_6098_; lean_object* v___y_6099_; lean_object* v___y_6100_; lean_object* v___y_6101_; lean_object* v___y_6120_; uint8_t v___y_6121_; lean_object* v___y_6122_; lean_object* v___y_6123_; lean_object* v___y_6124_; lean_object* v___y_6125_; lean_object* v___y_6126_; lean_object* v___y_6127_; lean_object* v___y_6128_; lean_object* v___y_6129_; uint8_t v___y_6130_; lean_object* v___y_6131_; lean_object* v___y_6132_; lean_object* v___y_6133_; lean_object* v___y_6134_; lean_object* v___y_6135_; lean_object* v___y_6136_; lean_object* v___y_6139_; lean_object* v___y_6140_; lean_object* v___y_6141_; lean_object* v___y_6142_; lean_object* v___y_6143_; lean_object* v___y_6144_; lean_object* v___y_6145_; lean_object* v___y_6146_; lean_object* v___y_6147_; uint8_t v___y_6148_; uint8_t v___y_6149_; lean_object* v___y_6150_; lean_object* v___y_6151_; lean_object* v___y_6152_; lean_object* v___y_6153_; lean_object* v___y_6154_; lean_object* v___y_6155_; lean_object* v___y_6174_; uint8_t v___y_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; lean_object* v___y_6179_; lean_object* v___y_6180_; lean_object* v___y_6181_; uint8_t v___y_6182_; lean_object* v___y_6183_; lean_object* v___y_6184_; lean_object* v___y_6185_; lean_object* v___y_6186_; lean_object* v___y_6187_; lean_object* v___y_6188_; lean_object* v___y_6189_; lean_object* v___y_6190_; lean_object* v_tk_6192_; lean_object* v___x_6193_; lean_object* v___y_6195_; uint8_t v___y_6196_; lean_object* v___y_6197_; lean_object* v___y_6198_; lean_object* v___y_6199_; lean_object* v___y_6200_; lean_object* v___y_6201_; lean_object* v___y_6202_; lean_object* v___y_6203_; uint8_t v___y_6204_; lean_object* v___y_6205_; lean_object* v_patType_x3f_6206_; lean_object* v___y_6207_; lean_object* v___y_6208_; lean_object* v___y_6209_; lean_object* v___y_6210_; lean_object* v___y_6211_; lean_object* v___y_6212_; lean_object* v___y_6213_; lean_object* v___y_6258_; uint8_t v___y_6259_; lean_object* v___y_6260_; lean_object* v___y_6261_; lean_object* v___y_6262_; lean_object* v___y_6263_; lean_object* v___y_6264_; lean_object* v___y_6265_; uint8_t v___y_6266_; lean_object* v___y_6267_; lean_object* v_patType_x3f_6268_; lean_object* v___y_6269_; lean_object* v___y_6270_; lean_object* v___y_6271_; lean_object* v___y_6272_; lean_object* v___y_6273_; lean_object* v___y_6274_; lean_object* v___y_6275_; lean_object* v___y_6294_; lean_object* v___y_6295_; lean_object* v___y_6296_; lean_object* v___y_6297_; uint8_t v___y_6298_; lean_object* v_xType_x3f_6299_; lean_object* v___y_6300_; lean_object* v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6306_; lean_object* v___y_6335_; lean_object* v___y_6336_; lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___y_6339_; lean_object* v___y_6340_; lean_object* v___y_6341_; lean_object* v___y_6342_; lean_object* v___y_6343_; uint8_t v___y_6344_; lean_object* v___y_6345_; lean_object* v___y_6346_; lean_object* v___y_6347_; lean_object* v___y_6348_; lean_object* v___y_6349_; lean_object* v___y_6350_; lean_object* v___y_6351_; lean_object* v___y_6394_; lean_object* v___y_6395_; lean_object* v___y_6396_; lean_object* v___y_6397_; lean_object* v___y_6398_; lean_object* v___y_6399_; uint8_t v___y_6400_; lean_object* v___y_6401_; lean_object* v___y_6402_; lean_object* v___y_6403_; lean_object* v___y_6404_; lean_object* v___y_6405_; lean_object* v___y_6406_; lean_object* v___y_6407_; lean_object* v___y_6408_; lean_object* v___y_6409_; lean_object* v___y_6410_; lean_object* v___y_6411_; lean_object* v_mutTk_x3f_6423_; lean_object* v___y_6424_; lean_object* v___y_6425_; lean_object* v___y_6426_; lean_object* v___y_6427_; lean_object* v___y_6428_; lean_object* v___y_6429_; lean_object* v___y_6430_; lean_object* v___x_6466_; uint8_t v___x_6467_; 
v___x_6083_ = lean_unsigned_to_nat(0u);
v_tk_6192_ = l_Lean_Syntax_getArg(v_stx_6067_, v___x_6083_);
v___x_6193_ = lean_unsigned_to_nat(1u);
v___x_6466_ = l_Lean_Syntax_getArg(v_stx_6067_, v___x_6193_);
v___x_6467_ = l_Lean_Syntax_isNone(v___x_6466_);
if (v___x_6467_ == 0)
{
uint8_t v___x_6468_; 
lean_inc(v___x_6466_);
v___x_6468_ = l_Lean_Syntax_matchesNull(v___x_6466_, v___x_6193_);
if (v___x_6468_ == 0)
{
lean_object* v___x_6469_; 
lean_dec(v___x_6466_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
lean_dec(v_stx_6067_);
v___x_6469_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6469_;
}
else
{
lean_object* v_mutTk_x3f_6470_; lean_object* v___x_6471_; 
v_mutTk_x3f_6470_ = l_Lean_Syntax_getArg(v___x_6466_, v___x_6083_);
lean_dec(v___x_6466_);
v___x_6471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6471_, 0, v_mutTk_x3f_6470_);
v_mutTk_x3f_6423_ = v___x_6471_;
v___y_6424_ = v_a_6069_;
v___y_6425_ = v_a_6070_;
v___y_6426_ = v_a_6071_;
v___y_6427_ = v_a_6072_;
v___y_6428_ = v_a_6073_;
v___y_6429_ = v_a_6074_;
v___y_6430_ = v_a_6075_;
goto v___jp_6422_;
}
}
else
{
lean_object* v___x_6472_; 
lean_dec(v___x_6466_);
v___x_6472_ = lean_box(0);
v_mutTk_x3f_6423_ = v___x_6472_;
v___y_6424_ = v_a_6069_;
v___y_6425_ = v_a_6070_;
v___y_6426_ = v_a_6071_;
v___y_6427_ = v_a_6072_;
v___y_6428_ = v_a_6073_;
v___y_6429_ = v_a_6074_;
v___y_6430_ = v_a_6075_;
goto v___jp_6422_;
}
v___jp_6084_:
{
lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6102_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6103_ = l_Lean_Core_mkFreshUserName(v___x_6102_, v___y_6096_, v___y_6088_);
if (lean_obj_tag(v___x_6103_) == 0)
{
lean_object* v_a_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___y_6108_; uint8_t v___x_6109_; lean_object* v___x_6110_; 
v_a_6104_ = lean_ctor_get(v___x_6103_, 0);
lean_inc(v_a_6104_);
lean_dec_ref_known(v___x_6103_, 1);
v___x_6105_ = l_Lean_mkIdentFrom(v___y_6094_, v_a_6104_, v___y_6085_);
lean_dec(v___y_6094_);
v___x_6106_ = lean_box(v___y_6086_);
v___x_6107_ = lean_box(v___x_6081_);
lean_inc(v___x_6105_);
lean_inc(v___y_6100_);
v___y_6108_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_6108_, 0, v___y_6098_);
lean_closure_set(v___y_6108_, 1, v___x_6106_);
lean_closure_set(v___y_6108_, 2, v___x_6077_);
lean_closure_set(v___y_6108_, 3, v___x_6078_);
lean_closure_set(v___y_6108_, 4, v___x_6079_);
lean_closure_set(v___y_6108_, 5, v___y_6100_);
lean_closure_set(v___y_6108_, 6, v___y_6090_);
lean_closure_set(v___y_6108_, 7, v___x_6105_);
lean_closure_set(v___y_6108_, 8, v_dec_6068_);
lean_closure_set(v___y_6108_, 9, v___x_6107_);
lean_closure_set(v___y_6108_, 10, v___y_6093_);
lean_closure_set(v___y_6108_, 11, v___x_6083_);
lean_closure_set(v___y_6108_, 12, v___y_6101_);
v___x_6109_ = 0;
v___x_6110_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6105_, v___y_6099_, v___y_6089_, v___y_6108_, v___x_6109_, v___y_6091_, v___y_6097_, v___y_6092_, v___y_6095_, v___y_6087_, v___y_6096_, v___y_6088_);
return v___x_6110_;
}
else
{
lean_object* v_a_6111_; lean_object* v___x_6113_; uint8_t v_isShared_6114_; uint8_t v_isSharedCheck_6118_; 
lean_dec(v___y_6101_);
lean_dec(v___y_6099_);
lean_dec(v___y_6098_);
lean_dec(v___y_6094_);
lean_dec(v___y_6093_);
lean_dec(v___y_6090_);
lean_dec(v___y_6089_);
lean_dec_ref(v_dec_6068_);
v_a_6111_ = lean_ctor_get(v___x_6103_, 0);
v_isSharedCheck_6118_ = !lean_is_exclusive(v___x_6103_);
if (v_isSharedCheck_6118_ == 0)
{
v___x_6113_ = v___x_6103_;
v_isShared_6114_ = v_isSharedCheck_6118_;
goto v_resetjp_6112_;
}
else
{
lean_inc(v_a_6111_);
lean_dec(v___x_6103_);
v___x_6113_ = lean_box(0);
v_isShared_6114_ = v_isSharedCheck_6118_;
goto v_resetjp_6112_;
}
v_resetjp_6112_:
{
lean_object* v___x_6116_; 
if (v_isShared_6114_ == 0)
{
v___x_6116_ = v___x_6113_;
goto v_reusejp_6115_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_a_6111_);
v___x_6116_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6115_;
}
v_reusejp_6115_:
{
return v___x_6116_;
}
}
}
}
v___jp_6119_:
{
lean_object* v___x_6137_; 
v___x_6137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6137_, 0, v___y_6127_);
v___y_6085_ = v___y_6130_;
v___y_6086_ = v___y_6121_;
v___y_6087_ = v___y_6133_;
v___y_6088_ = v___y_6129_;
v___y_6089_ = v___y_6135_;
v___y_6090_ = v___y_6122_;
v___y_6091_ = v___y_6132_;
v___y_6092_ = v___y_6124_;
v___y_6093_ = v___y_6120_;
v___y_6094_ = v___y_6131_;
v___y_6095_ = v___y_6125_;
v___y_6096_ = v___y_6126_;
v___y_6097_ = v___y_6128_;
v___y_6098_ = v___x_6137_;
v___y_6099_ = v___y_6134_;
v___y_6100_ = v___y_6123_;
v___y_6101_ = v___y_6136_;
goto v___jp_6084_;
}
v___jp_6138_:
{
lean_object* v___x_6156_; lean_object* v___x_6157_; 
v___x_6156_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6157_ = l_Lean_Core_mkFreshUserName(v___x_6156_, v___y_6139_, v___y_6142_);
if (lean_obj_tag(v___x_6157_) == 0)
{
lean_object* v_a_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___y_6162_; uint8_t v___x_6163_; lean_object* v___x_6164_; 
v_a_6158_ = lean_ctor_get(v___x_6157_, 0);
lean_inc(v_a_6158_);
lean_dec_ref_known(v___x_6157_, 1);
v___x_6159_ = l_Lean_mkIdentFrom(v___y_6143_, v_a_6158_, v___y_6149_);
lean_dec(v___y_6143_);
v___x_6160_ = lean_box(v___y_6148_);
v___x_6161_ = lean_box(v___x_6081_);
lean_inc(v___x_6159_);
lean_inc(v___y_6154_);
v___y_6162_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed), 21, 13);
lean_closure_set(v___y_6162_, 0, v___y_6140_);
lean_closure_set(v___y_6162_, 1, v___x_6160_);
lean_closure_set(v___y_6162_, 2, v___x_6077_);
lean_closure_set(v___y_6162_, 3, v___x_6078_);
lean_closure_set(v___y_6162_, 4, v___x_6079_);
lean_closure_set(v___y_6162_, 5, v___y_6154_);
lean_closure_set(v___y_6162_, 6, v___y_6144_);
lean_closure_set(v___y_6162_, 7, v___x_6159_);
lean_closure_set(v___y_6162_, 8, v_dec_6068_);
lean_closure_set(v___y_6162_, 9, v___x_6161_);
lean_closure_set(v___y_6162_, 10, v___y_6147_);
lean_closure_set(v___y_6162_, 11, v___x_6083_);
lean_closure_set(v___y_6162_, 12, v___y_6155_);
v___x_6163_ = 0;
v___x_6164_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6159_, v___y_6151_, v___y_6153_, v___y_6162_, v___x_6163_, v___y_6145_, v___y_6150_, v___y_6146_, v___y_6141_, v___y_6152_, v___y_6139_, v___y_6142_);
return v___x_6164_;
}
else
{
lean_object* v_a_6165_; lean_object* v___x_6167_; uint8_t v_isShared_6168_; uint8_t v_isSharedCheck_6172_; 
lean_dec(v___y_6155_);
lean_dec(v___y_6153_);
lean_dec(v___y_6151_);
lean_dec(v___y_6147_);
lean_dec(v___y_6144_);
lean_dec(v___y_6143_);
lean_dec(v___y_6140_);
lean_dec_ref(v_dec_6068_);
v_a_6165_ = lean_ctor_get(v___x_6157_, 0);
v_isSharedCheck_6172_ = !lean_is_exclusive(v___x_6157_);
if (v_isSharedCheck_6172_ == 0)
{
v___x_6167_ = v___x_6157_;
v_isShared_6168_ = v_isSharedCheck_6172_;
goto v_resetjp_6166_;
}
else
{
lean_inc(v_a_6165_);
lean_dec(v___x_6157_);
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
v___jp_6173_:
{
lean_object* v___x_6191_; 
v___x_6191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6191_, 0, v___y_6186_);
v___y_6139_ = v___y_6178_;
v___y_6140_ = v___x_6191_;
v___y_6141_ = v___y_6184_;
v___y_6142_ = v___y_6179_;
v___y_6143_ = v___y_6181_;
v___y_6144_ = v___y_6176_;
v___y_6145_ = v___y_6185_;
v___y_6146_ = v___y_6188_;
v___y_6147_ = v___y_6174_;
v___y_6148_ = v___y_6175_;
v___y_6149_ = v___y_6182_;
v___y_6150_ = v___y_6183_;
v___y_6151_ = v___y_6187_;
v___y_6152_ = v___y_6180_;
v___y_6153_ = v___y_6189_;
v___y_6154_ = v___y_6177_;
v___y_6155_ = v___y_6190_;
goto v___jp_6138_;
}
v___jp_6194_:
{
lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; uint8_t v___x_6217_; 
v___x_6214_ = l_Lean_Syntax_getArg(v___y_6201_, v___y_6199_);
v___x_6215_ = lean_unsigned_to_nat(4u);
v___x_6216_ = l_Lean_Syntax_getArg(v___y_6201_, v___x_6215_);
lean_dec(v___y_6201_);
lean_inc(v___x_6216_);
v___x_6217_ = l_Lean_Syntax_matchesNull(v___x_6216_, v___x_6083_);
if (v___x_6217_ == 0)
{
uint8_t v___x_6218_; 
lean_dec(v___y_6203_);
lean_dec(v_tk_6192_);
v___x_6218_ = l_Lean_Syntax_isNone(v___x_6216_);
if (v___x_6218_ == 0)
{
uint8_t v___x_6219_; 
lean_inc(v___x_6216_);
v___x_6219_ = l_Lean_Syntax_matchesNull(v___x_6216_, v___y_6199_);
if (v___x_6219_ == 0)
{
lean_object* v___x_6220_; 
lean_dec(v___x_6216_);
lean_dec(v___x_6214_);
lean_dec(v_patType_x3f_6206_);
lean_dec(v___y_6205_);
lean_dec(v___y_6198_);
lean_dec(v___y_6195_);
lean_dec_ref(v_dec_6068_);
v___x_6220_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6220_;
}
else
{
lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; 
v___x_6221_ = l_Lean_Syntax_getArg(v___x_6216_, v___x_6193_);
v___x_6222_ = l_Lean_Syntax_getArg(v___x_6216_, v___y_6202_);
lean_dec(v___x_6216_);
v___x_6223_ = l_Lean_Syntax_getOptional_x3f(v___x_6222_);
lean_dec(v___x_6222_);
if (lean_obj_tag(v___x_6223_) == 0)
{
lean_inc(v___y_6200_);
v___y_6120_ = v___y_6195_;
v___y_6121_ = v___y_6196_;
v___y_6122_ = v___y_6198_;
v___y_6123_ = v___y_6197_;
v___y_6124_ = v___y_6209_;
v___y_6125_ = v___y_6210_;
v___y_6126_ = v___y_6212_;
v___y_6127_ = v___x_6221_;
v___y_6128_ = v___y_6208_;
v___y_6129_ = v___y_6213_;
v___y_6130_ = v___y_6204_;
v___y_6131_ = v___y_6205_;
v___y_6132_ = v___y_6207_;
v___y_6133_ = v___y_6211_;
v___y_6134_ = v_patType_x3f_6206_;
v___y_6135_ = v___x_6214_;
v___y_6136_ = v___y_6200_;
goto v___jp_6119_;
}
else
{
lean_object* v_val_6224_; lean_object* v___x_6226_; uint8_t v_isShared_6227_; uint8_t v_isSharedCheck_6231_; 
v_val_6224_ = lean_ctor_get(v___x_6223_, 0);
v_isSharedCheck_6231_ = !lean_is_exclusive(v___x_6223_);
if (v_isSharedCheck_6231_ == 0)
{
v___x_6226_ = v___x_6223_;
v_isShared_6227_ = v_isSharedCheck_6231_;
goto v_resetjp_6225_;
}
else
{
lean_inc(v_val_6224_);
lean_dec(v___x_6223_);
v___x_6226_ = lean_box(0);
v_isShared_6227_ = v_isSharedCheck_6231_;
goto v_resetjp_6225_;
}
v_resetjp_6225_:
{
lean_object* v___x_6229_; 
if (v_isShared_6227_ == 0)
{
v___x_6229_ = v___x_6226_;
goto v_reusejp_6228_;
}
else
{
lean_object* v_reuseFailAlloc_6230_; 
v_reuseFailAlloc_6230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_val_6224_);
v___x_6229_ = v_reuseFailAlloc_6230_;
goto v_reusejp_6228_;
}
v_reusejp_6228_:
{
v___y_6120_ = v___y_6195_;
v___y_6121_ = v___y_6196_;
v___y_6122_ = v___y_6198_;
v___y_6123_ = v___y_6197_;
v___y_6124_ = v___y_6209_;
v___y_6125_ = v___y_6210_;
v___y_6126_ = v___y_6212_;
v___y_6127_ = v___x_6221_;
v___y_6128_ = v___y_6208_;
v___y_6129_ = v___y_6213_;
v___y_6130_ = v___y_6204_;
v___y_6131_ = v___y_6205_;
v___y_6132_ = v___y_6207_;
v___y_6133_ = v___y_6211_;
v___y_6134_ = v_patType_x3f_6206_;
v___y_6135_ = v___x_6214_;
v___y_6136_ = v___x_6229_;
goto v___jp_6119_;
}
}
}
}
}
else
{
lean_dec(v___x_6216_);
lean_inc_n(v___y_6200_, 2);
v___y_6085_ = v___y_6204_;
v___y_6086_ = v___y_6196_;
v___y_6087_ = v___y_6211_;
v___y_6088_ = v___y_6213_;
v___y_6089_ = v___x_6214_;
v___y_6090_ = v___y_6198_;
v___y_6091_ = v___y_6207_;
v___y_6092_ = v___y_6209_;
v___y_6093_ = v___y_6195_;
v___y_6094_ = v___y_6205_;
v___y_6095_ = v___y_6210_;
v___y_6096_ = v___y_6212_;
v___y_6097_ = v___y_6208_;
v___y_6098_ = v___y_6200_;
v___y_6099_ = v_patType_x3f_6206_;
v___y_6100_ = v___y_6197_;
v___y_6101_ = v___y_6200_;
goto v___jp_6084_;
}
}
else
{
lean_object* v___x_6232_; lean_object* v___x_6233_; 
lean_dec(v___x_6216_);
lean_dec(v___y_6205_);
lean_dec(v___y_6198_);
lean_dec(v___y_6195_);
v___x_6232_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6233_ = l_Lean_Core_mkFreshUserName(v___x_6232_, v___y_6212_, v___y_6213_);
if (lean_obj_tag(v___x_6233_) == 0)
{
lean_object* v_a_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; 
v_a_6234_ = lean_ctor_get(v___x_6233_, 0);
lean_inc(v_a_6234_);
lean_dec_ref_known(v___x_6233_, 1);
v___x_6235_ = l_Lean_mkIdentFrom(v___y_6203_, v_a_6234_, v___y_6204_);
lean_dec(v___y_6203_);
v___x_6236_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_6068_, v_tk_6192_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
lean_dec(v_tk_6192_);
if (lean_obj_tag(v___x_6236_) == 0)
{
lean_object* v_a_6237_; uint8_t v_kind_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; 
v_a_6237_ = lean_ctor_get(v___x_6236_, 0);
lean_inc(v_a_6237_);
lean_dec_ref_known(v___x_6236_, 1);
v_kind_6238_ = lean_ctor_get_uint8(v_a_6237_, sizeof(void*)*3);
v___x_6239_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6239_, 0, v_a_6237_);
v___x_6240_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6235_, v_patType_x3f_6206_, v___x_6214_, v___x_6239_, v_kind_6238_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
return v___x_6240_;
}
else
{
lean_object* v_a_6241_; lean_object* v___x_6243_; uint8_t v_isShared_6244_; uint8_t v_isSharedCheck_6248_; 
lean_dec(v___x_6235_);
lean_dec(v___x_6214_);
lean_dec(v_patType_x3f_6206_);
v_a_6241_ = lean_ctor_get(v___x_6236_, 0);
v_isSharedCheck_6248_ = !lean_is_exclusive(v___x_6236_);
if (v_isSharedCheck_6248_ == 0)
{
v___x_6243_ = v___x_6236_;
v_isShared_6244_ = v_isSharedCheck_6248_;
goto v_resetjp_6242_;
}
else
{
lean_inc(v_a_6241_);
lean_dec(v___x_6236_);
v___x_6243_ = lean_box(0);
v_isShared_6244_ = v_isSharedCheck_6248_;
goto v_resetjp_6242_;
}
v_resetjp_6242_:
{
lean_object* v___x_6246_; 
if (v_isShared_6244_ == 0)
{
v___x_6246_ = v___x_6243_;
goto v_reusejp_6245_;
}
else
{
lean_object* v_reuseFailAlloc_6247_; 
v_reuseFailAlloc_6247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6247_, 0, v_a_6241_);
v___x_6246_ = v_reuseFailAlloc_6247_;
goto v_reusejp_6245_;
}
v_reusejp_6245_:
{
return v___x_6246_;
}
}
}
}
else
{
lean_object* v_a_6249_; lean_object* v___x_6251_; uint8_t v_isShared_6252_; uint8_t v_isSharedCheck_6256_; 
lean_dec(v___x_6214_);
lean_dec(v_patType_x3f_6206_);
lean_dec(v___y_6203_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v_a_6249_ = lean_ctor_get(v___x_6233_, 0);
v_isSharedCheck_6256_ = !lean_is_exclusive(v___x_6233_);
if (v_isSharedCheck_6256_ == 0)
{
v___x_6251_ = v___x_6233_;
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
else
{
lean_inc(v_a_6249_);
lean_dec(v___x_6233_);
v___x_6251_ = lean_box(0);
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
v_resetjp_6250_:
{
lean_object* v___x_6254_; 
if (v_isShared_6252_ == 0)
{
v___x_6254_ = v___x_6251_;
goto v_reusejp_6253_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_a_6249_);
v___x_6254_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6253_;
}
v_reusejp_6253_:
{
return v___x_6254_;
}
}
}
}
}
v___jp_6257_:
{
lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; uint8_t v___x_6279_; 
v___x_6276_ = l_Lean_Syntax_getArg(v___y_6264_, v___y_6262_);
v___x_6277_ = lean_unsigned_to_nat(4u);
v___x_6278_ = l_Lean_Syntax_getArg(v___y_6264_, v___x_6277_);
lean_dec(v___y_6264_);
v___x_6279_ = l_Lean_Syntax_isNone(v___x_6278_);
if (v___x_6279_ == 0)
{
uint8_t v___x_6280_; 
lean_inc(v___x_6278_);
v___x_6280_ = l_Lean_Syntax_matchesNull(v___x_6278_, v___y_6262_);
if (v___x_6280_ == 0)
{
lean_object* v___x_6281_; 
lean_dec(v___x_6278_);
lean_dec(v___x_6276_);
lean_dec(v_patType_x3f_6268_);
lean_dec(v___y_6267_);
lean_dec(v___y_6261_);
lean_dec(v___y_6258_);
lean_dec_ref(v_dec_6068_);
v___x_6281_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6281_;
}
else
{
lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; 
v___x_6282_ = l_Lean_Syntax_getArg(v___x_6278_, v___x_6193_);
v___x_6283_ = l_Lean_Syntax_getArg(v___x_6278_, v___y_6265_);
lean_dec(v___x_6278_);
v___x_6284_ = l_Lean_Syntax_getOptional_x3f(v___x_6283_);
lean_dec(v___x_6283_);
if (lean_obj_tag(v___x_6284_) == 0)
{
lean_inc(v___y_6263_);
v___y_6174_ = v___y_6258_;
v___y_6175_ = v___y_6259_;
v___y_6176_ = v___y_6261_;
v___y_6177_ = v___y_6260_;
v___y_6178_ = v___y_6274_;
v___y_6179_ = v___y_6275_;
v___y_6180_ = v___y_6273_;
v___y_6181_ = v___y_6267_;
v___y_6182_ = v___y_6266_;
v___y_6183_ = v___y_6270_;
v___y_6184_ = v___y_6272_;
v___y_6185_ = v___y_6269_;
v___y_6186_ = v___x_6282_;
v___y_6187_ = v_patType_x3f_6268_;
v___y_6188_ = v___y_6271_;
v___y_6189_ = v___x_6276_;
v___y_6190_ = v___y_6263_;
goto v___jp_6173_;
}
else
{
lean_object* v_val_6285_; lean_object* v___x_6287_; uint8_t v_isShared_6288_; uint8_t v_isSharedCheck_6292_; 
v_val_6285_ = lean_ctor_get(v___x_6284_, 0);
v_isSharedCheck_6292_ = !lean_is_exclusive(v___x_6284_);
if (v_isSharedCheck_6292_ == 0)
{
v___x_6287_ = v___x_6284_;
v_isShared_6288_ = v_isSharedCheck_6292_;
goto v_resetjp_6286_;
}
else
{
lean_inc(v_val_6285_);
lean_dec(v___x_6284_);
v___x_6287_ = lean_box(0);
v_isShared_6288_ = v_isSharedCheck_6292_;
goto v_resetjp_6286_;
}
v_resetjp_6286_:
{
lean_object* v___x_6290_; 
if (v_isShared_6288_ == 0)
{
v___x_6290_ = v___x_6287_;
goto v_reusejp_6289_;
}
else
{
lean_object* v_reuseFailAlloc_6291_; 
v_reuseFailAlloc_6291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6291_, 0, v_val_6285_);
v___x_6290_ = v_reuseFailAlloc_6291_;
goto v_reusejp_6289_;
}
v_reusejp_6289_:
{
v___y_6174_ = v___y_6258_;
v___y_6175_ = v___y_6259_;
v___y_6176_ = v___y_6261_;
v___y_6177_ = v___y_6260_;
v___y_6178_ = v___y_6274_;
v___y_6179_ = v___y_6275_;
v___y_6180_ = v___y_6273_;
v___y_6181_ = v___y_6267_;
v___y_6182_ = v___y_6266_;
v___y_6183_ = v___y_6270_;
v___y_6184_ = v___y_6272_;
v___y_6185_ = v___y_6269_;
v___y_6186_ = v___x_6282_;
v___y_6187_ = v_patType_x3f_6268_;
v___y_6188_ = v___y_6271_;
v___y_6189_ = v___x_6276_;
v___y_6190_ = v___x_6290_;
goto v___jp_6173_;
}
}
}
}
}
else
{
lean_dec(v___x_6278_);
lean_inc_n(v___y_6263_, 2);
v___y_6139_ = v___y_6274_;
v___y_6140_ = v___y_6263_;
v___y_6141_ = v___y_6272_;
v___y_6142_ = v___y_6275_;
v___y_6143_ = v___y_6267_;
v___y_6144_ = v___y_6261_;
v___y_6145_ = v___y_6269_;
v___y_6146_ = v___y_6271_;
v___y_6147_ = v___y_6258_;
v___y_6148_ = v___y_6259_;
v___y_6149_ = v___y_6266_;
v___y_6150_ = v___y_6270_;
v___y_6151_ = v_patType_x3f_6268_;
v___y_6152_ = v___y_6273_;
v___y_6153_ = v___x_6276_;
v___y_6154_ = v___y_6260_;
v___y_6155_ = v___y_6263_;
goto v___jp_6138_;
}
}
v___jp_6293_:
{
lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; 
v___x_6307_ = l_Lean_Syntax_getArg(v___y_6296_, v___y_6294_);
lean_dec(v___y_6296_);
v___x_6308_ = lean_mk_empty_array_with_capacity(v___x_6193_);
lean_inc(v___y_6297_);
v___x_6309_ = lean_array_push(v___x_6308_, v___y_6297_);
v___x_6310_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_6309_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_);
lean_dec_ref(v___x_6309_);
if (lean_obj_tag(v___x_6310_) == 0)
{
lean_object* v___x_6311_; 
lean_dec_ref_known(v___x_6310_, 1);
v___x_6311_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_6068_, v_tk_6192_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_);
lean_dec(v_tk_6192_);
if (lean_obj_tag(v___x_6311_) == 0)
{
lean_object* v_a_6312_; uint8_t v_kind_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; 
v_a_6312_ = lean_ctor_get(v___x_6311_, 0);
lean_inc(v_a_6312_);
lean_dec_ref_known(v___x_6311_, 1);
v_kind_6313_ = lean_ctor_get_uint8(v_a_6312_, sizeof(void*)*3);
v___x_6314_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6314_, 0, v_a_6312_);
v___x_6315_ = lean_box(v___y_6298_);
lean_inc(v___y_6297_);
v___x_6316_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 13, 5);
lean_closure_set(v___x_6316_, 0, lean_box(0));
lean_closure_set(v___x_6316_, 1, v___y_6295_);
lean_closure_set(v___x_6316_, 2, v___y_6297_);
lean_closure_set(v___x_6316_, 3, v___x_6315_);
lean_closure_set(v___x_6316_, 4, v___x_6314_);
v___x_6317_ = l_Lean_Elab_Do_elabDoIdDecl(v___y_6297_, v_xType_x3f_6299_, v___x_6307_, v___x_6316_, v_kind_6313_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_);
return v___x_6317_;
}
else
{
lean_object* v_a_6318_; lean_object* v___x_6320_; uint8_t v_isShared_6321_; uint8_t v_isSharedCheck_6325_; 
lean_dec(v___x_6307_);
lean_dec(v_xType_x3f_6299_);
lean_dec(v___y_6297_);
lean_dec(v___y_6295_);
v_a_6318_ = lean_ctor_get(v___x_6311_, 0);
v_isSharedCheck_6325_ = !lean_is_exclusive(v___x_6311_);
if (v_isSharedCheck_6325_ == 0)
{
v___x_6320_ = v___x_6311_;
v_isShared_6321_ = v_isSharedCheck_6325_;
goto v_resetjp_6319_;
}
else
{
lean_inc(v_a_6318_);
lean_dec(v___x_6311_);
v___x_6320_ = lean_box(0);
v_isShared_6321_ = v_isSharedCheck_6325_;
goto v_resetjp_6319_;
}
v_resetjp_6319_:
{
lean_object* v___x_6323_; 
if (v_isShared_6321_ == 0)
{
v___x_6323_ = v___x_6320_;
goto v_reusejp_6322_;
}
else
{
lean_object* v_reuseFailAlloc_6324_; 
v_reuseFailAlloc_6324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6324_, 0, v_a_6318_);
v___x_6323_ = v_reuseFailAlloc_6324_;
goto v_reusejp_6322_;
}
v_reusejp_6322_:
{
return v___x_6323_;
}
}
}
}
else
{
lean_object* v_a_6326_; lean_object* v___x_6328_; uint8_t v_isShared_6329_; uint8_t v_isSharedCheck_6333_; 
lean_dec(v___x_6307_);
lean_dec(v_xType_x3f_6299_);
lean_dec(v___y_6297_);
lean_dec(v___y_6295_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v_a_6326_ = lean_ctor_get(v___x_6310_, 0);
v_isSharedCheck_6333_ = !lean_is_exclusive(v___x_6310_);
if (v_isSharedCheck_6333_ == 0)
{
v___x_6328_ = v___x_6310_;
v_isShared_6329_ = v_isSharedCheck_6333_;
goto v_resetjp_6327_;
}
else
{
lean_inc(v_a_6326_);
lean_dec(v___x_6310_);
v___x_6328_ = lean_box(0);
v_isShared_6329_ = v_isSharedCheck_6333_;
goto v_resetjp_6327_;
}
v_resetjp_6327_:
{
lean_object* v___x_6331_; 
if (v_isShared_6329_ == 0)
{
v___x_6331_ = v___x_6328_;
goto v_reusejp_6330_;
}
else
{
lean_object* v_reuseFailAlloc_6332_; 
v_reuseFailAlloc_6332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6332_, 0, v_a_6326_);
v___x_6331_ = v_reuseFailAlloc_6332_;
goto v_reusejp_6330_;
}
v_reusejp_6330_:
{
return v___x_6331_;
}
}
}
}
v___jp_6334_:
{
uint8_t v___x_6352_; 
lean_inc(v___y_6341_);
v___x_6352_ = l_Lean_Syntax_isOfKind(v___y_6341_, v___y_6342_);
if (v___x_6352_ == 0)
{
uint8_t v___x_6353_; 
lean_dec(v___y_6338_);
lean_inc(v___y_6341_);
v___x_6353_ = l_Lean_Syntax_isOfKind(v___y_6341_, v___y_6339_);
if (v___x_6353_ == 0)
{
lean_object* v___x_6354_; 
lean_dec(v___y_6341_);
lean_dec(v___y_6335_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v___x_6354_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6354_;
}
else
{
lean_object* v___x_6355_; lean_object* v___x_6356_; uint8_t v___x_6357_; 
v___x_6355_ = l_Lean_Syntax_getArg(v___y_6341_, v___x_6083_);
v___x_6356_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
lean_inc(v___x_6355_);
v___x_6357_ = l_Lean_Syntax_isOfKind(v___x_6355_, v___x_6356_);
if (v___x_6357_ == 0)
{
lean_object* v___x_6358_; uint8_t v___x_6359_; 
lean_dec(v_tk_6192_);
v___x_6358_ = l_Lean_Syntax_getArg(v___y_6341_, v___x_6193_);
v___x_6359_ = l_Lean_Syntax_isNone(v___x_6358_);
if (v___x_6359_ == 0)
{
uint8_t v___x_6360_; 
lean_inc(v___x_6358_);
v___x_6360_ = l_Lean_Syntax_matchesNull(v___x_6358_, v___x_6193_);
if (v___x_6360_ == 0)
{
lean_object* v___x_6361_; 
lean_dec(v___x_6358_);
lean_dec(v___x_6355_);
lean_dec(v___y_6341_);
lean_dec(v___y_6335_);
lean_dec_ref(v_dec_6068_);
v___x_6361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6361_;
}
else
{
lean_object* v___x_6362_; lean_object* v___x_6363_; uint8_t v___x_6364_; 
v___x_6362_ = l_Lean_Syntax_getArg(v___x_6358_, v___x_6083_);
lean_dec(v___x_6358_);
v___x_6363_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6362_);
v___x_6364_ = l_Lean_Syntax_isOfKind(v___x_6362_, v___x_6363_);
if (v___x_6364_ == 0)
{
lean_object* v___x_6365_; 
lean_dec(v___x_6362_);
lean_dec(v___x_6355_);
lean_dec(v___y_6341_);
lean_dec(v___y_6335_);
lean_dec_ref(v_dec_6068_);
v___x_6365_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6365_;
}
else
{
lean_object* v___x_6366_; lean_object* v___x_6367_; 
v___x_6366_ = l_Lean_Syntax_getArg(v___x_6362_, v___x_6193_);
lean_dec(v___x_6362_);
v___x_6367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6367_, 0, v___x_6366_);
lean_inc(v___x_6355_);
v___y_6258_ = v___y_6335_;
v___y_6259_ = v___x_6357_;
v___y_6260_ = v___y_6336_;
v___y_6261_ = v___x_6355_;
v___y_6262_ = v___y_6337_;
v___y_6263_ = v___y_6340_;
v___y_6264_ = v___y_6341_;
v___y_6265_ = v___y_6343_;
v___y_6266_ = v___y_6344_;
v___y_6267_ = v___x_6355_;
v_patType_x3f_6268_ = v___x_6367_;
v___y_6269_ = v___y_6345_;
v___y_6270_ = v___y_6346_;
v___y_6271_ = v___y_6347_;
v___y_6272_ = v___y_6348_;
v___y_6273_ = v___y_6349_;
v___y_6274_ = v___y_6350_;
v___y_6275_ = v___y_6351_;
goto v___jp_6257_;
}
}
}
else
{
lean_dec(v___x_6358_);
lean_inc(v___y_6340_);
lean_inc(v___x_6355_);
v___y_6258_ = v___y_6335_;
v___y_6259_ = v___x_6357_;
v___y_6260_ = v___y_6336_;
v___y_6261_ = v___x_6355_;
v___y_6262_ = v___y_6337_;
v___y_6263_ = v___y_6340_;
v___y_6264_ = v___y_6341_;
v___y_6265_ = v___y_6343_;
v___y_6266_ = v___y_6344_;
v___y_6267_ = v___x_6355_;
v_patType_x3f_6268_ = v___y_6340_;
v___y_6269_ = v___y_6345_;
v___y_6270_ = v___y_6346_;
v___y_6271_ = v___y_6347_;
v___y_6272_ = v___y_6348_;
v___y_6273_ = v___y_6349_;
v___y_6274_ = v___y_6350_;
v___y_6275_ = v___y_6351_;
goto v___jp_6257_;
}
}
else
{
lean_object* v___x_6368_; lean_object* v___x_6369_; uint8_t v___x_6370_; 
v___x_6368_ = l_Lean_Syntax_getArg(v___x_6355_, v___x_6083_);
v___x_6369_ = l_Lean_Syntax_getArg(v___y_6341_, v___x_6193_);
v___x_6370_ = l_Lean_Syntax_isNone(v___x_6369_);
if (v___x_6370_ == 0)
{
uint8_t v___x_6371_; 
lean_inc(v___x_6369_);
v___x_6371_ = l_Lean_Syntax_matchesNull(v___x_6369_, v___x_6193_);
if (v___x_6371_ == 0)
{
lean_object* v___x_6372_; 
lean_dec(v___x_6369_);
lean_dec(v___x_6368_);
lean_dec(v___x_6355_);
lean_dec(v___y_6341_);
lean_dec(v___y_6335_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v___x_6372_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6372_;
}
else
{
lean_object* v___x_6373_; lean_object* v___x_6374_; uint8_t v___x_6375_; 
v___x_6373_ = l_Lean_Syntax_getArg(v___x_6369_, v___x_6083_);
lean_dec(v___x_6369_);
v___x_6374_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6373_);
v___x_6375_ = l_Lean_Syntax_isOfKind(v___x_6373_, v___x_6374_);
if (v___x_6375_ == 0)
{
lean_object* v___x_6376_; 
lean_dec(v___x_6373_);
lean_dec(v___x_6368_);
lean_dec(v___x_6355_);
lean_dec(v___y_6341_);
lean_dec(v___y_6335_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v___x_6376_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6376_;
}
else
{
lean_object* v___x_6377_; lean_object* v___x_6378_; 
v___x_6377_ = l_Lean_Syntax_getArg(v___x_6373_, v___x_6193_);
lean_dec(v___x_6373_);
v___x_6378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6378_, 0, v___x_6377_);
lean_inc(v___x_6355_);
v___y_6195_ = v___y_6335_;
v___y_6196_ = v___x_6352_;
v___y_6197_ = v___y_6336_;
v___y_6198_ = v___x_6355_;
v___y_6199_ = v___y_6337_;
v___y_6200_ = v___y_6340_;
v___y_6201_ = v___y_6341_;
v___y_6202_ = v___y_6343_;
v___y_6203_ = v___x_6368_;
v___y_6204_ = v___y_6344_;
v___y_6205_ = v___x_6355_;
v_patType_x3f_6206_ = v___x_6378_;
v___y_6207_ = v___y_6345_;
v___y_6208_ = v___y_6346_;
v___y_6209_ = v___y_6347_;
v___y_6210_ = v___y_6348_;
v___y_6211_ = v___y_6349_;
v___y_6212_ = v___y_6350_;
v___y_6213_ = v___y_6351_;
goto v___jp_6194_;
}
}
}
else
{
lean_dec(v___x_6369_);
lean_inc(v___y_6340_);
lean_inc(v___x_6355_);
v___y_6195_ = v___y_6335_;
v___y_6196_ = v___x_6352_;
v___y_6197_ = v___y_6336_;
v___y_6198_ = v___x_6355_;
v___y_6199_ = v___y_6337_;
v___y_6200_ = v___y_6340_;
v___y_6201_ = v___y_6341_;
v___y_6202_ = v___y_6343_;
v___y_6203_ = v___x_6368_;
v___y_6204_ = v___y_6344_;
v___y_6205_ = v___x_6355_;
v_patType_x3f_6206_ = v___y_6340_;
v___y_6207_ = v___y_6345_;
v___y_6208_ = v___y_6346_;
v___y_6209_ = v___y_6347_;
v___y_6210_ = v___y_6348_;
v___y_6211_ = v___y_6349_;
v___y_6212_ = v___y_6350_;
v___y_6213_ = v___y_6351_;
goto v___jp_6194_;
}
}
}
}
else
{
lean_object* v___x_6379_; lean_object* v___x_6380_; uint8_t v___x_6381_; 
lean_dec(v___y_6335_);
v___x_6379_ = l_Lean_Syntax_getArg(v___y_6341_, v___x_6083_);
v___x_6380_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_6379_);
v___x_6381_ = l_Lean_Syntax_isOfKind(v___x_6379_, v___x_6380_);
if (v___x_6381_ == 0)
{
lean_object* v___x_6382_; 
lean_dec(v___x_6379_);
lean_dec(v___y_6341_);
lean_dec(v___y_6338_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v___x_6382_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6382_;
}
else
{
lean_object* v___x_6383_; uint8_t v___x_6384_; 
v___x_6383_ = l_Lean_Syntax_getArg(v___y_6341_, v___x_6193_);
v___x_6384_ = l_Lean_Syntax_isNone(v___x_6383_);
if (v___x_6384_ == 0)
{
uint8_t v___x_6385_; 
lean_inc(v___x_6383_);
v___x_6385_ = l_Lean_Syntax_matchesNull(v___x_6383_, v___x_6193_);
if (v___x_6385_ == 0)
{
lean_object* v___x_6386_; 
lean_dec(v___x_6383_);
lean_dec(v___x_6379_);
lean_dec(v___y_6341_);
lean_dec(v___y_6338_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v___x_6386_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6386_;
}
else
{
lean_object* v___x_6387_; lean_object* v___x_6388_; uint8_t v___x_6389_; 
v___x_6387_ = l_Lean_Syntax_getArg(v___x_6383_, v___x_6083_);
lean_dec(v___x_6383_);
v___x_6388_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6387_);
v___x_6389_ = l_Lean_Syntax_isOfKind(v___x_6387_, v___x_6388_);
if (v___x_6389_ == 0)
{
lean_object* v___x_6390_; 
lean_dec(v___x_6387_);
lean_dec(v___x_6379_);
lean_dec(v___y_6341_);
lean_dec(v___y_6338_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v___x_6390_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6390_;
}
else
{
lean_object* v___x_6391_; lean_object* v___x_6392_; 
v___x_6391_ = l_Lean_Syntax_getArg(v___x_6387_, v___x_6193_);
lean_dec(v___x_6387_);
v___x_6392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6392_, 0, v___x_6391_);
v___y_6294_ = v___y_6337_;
v___y_6295_ = v___y_6338_;
v___y_6296_ = v___y_6341_;
v___y_6297_ = v___x_6379_;
v___y_6298_ = v___y_6344_;
v_xType_x3f_6299_ = v___x_6392_;
v___y_6300_ = v___y_6345_;
v___y_6301_ = v___y_6346_;
v___y_6302_ = v___y_6347_;
v___y_6303_ = v___y_6348_;
v___y_6304_ = v___y_6349_;
v___y_6305_ = v___y_6350_;
v___y_6306_ = v___y_6351_;
goto v___jp_6293_;
}
}
}
else
{
lean_dec(v___x_6383_);
lean_inc(v___y_6340_);
v___y_6294_ = v___y_6337_;
v___y_6295_ = v___y_6338_;
v___y_6296_ = v___y_6341_;
v___y_6297_ = v___x_6379_;
v___y_6298_ = v___y_6344_;
v_xType_x3f_6299_ = v___y_6340_;
v___y_6300_ = v___y_6345_;
v___y_6301_ = v___y_6346_;
v___y_6302_ = v___y_6347_;
v___y_6303_ = v___y_6348_;
v___y_6304_ = v___y_6349_;
v___y_6305_ = v___y_6350_;
v___y_6306_ = v___y_6351_;
goto v___jp_6293_;
}
}
}
}
v___jp_6393_:
{
lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v_a_6414_; lean_object* v___x_6416_; uint8_t v_isShared_6417_; uint8_t v_isSharedCheck_6421_; 
lean_dec(v___y_6408_);
lean_dec(v___y_6407_);
lean_dec(v___y_6394_);
v___x_6412_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__1, &l_Lean_Elab_Do_elabDoLetArrow___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1);
v___x_6413_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v___y_6406_, v___x_6412_, v___y_6401_, v___y_6402_, v___y_6405_, v___y_6411_, v___y_6399_, v___y_6398_, v___y_6403_);
lean_dec(v___y_6406_);
v_a_6414_ = lean_ctor_get(v___x_6413_, 0);
v_isSharedCheck_6421_ = !lean_is_exclusive(v___x_6413_);
if (v_isSharedCheck_6421_ == 0)
{
v___x_6416_ = v___x_6413_;
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
else
{
lean_inc(v_a_6414_);
lean_dec(v___x_6413_);
v___x_6416_ = lean_box(0);
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
v_resetjp_6415_:
{
lean_object* v___x_6419_; 
if (v_isShared_6417_ == 0)
{
v___x_6419_ = v___x_6416_;
goto v_reusejp_6418_;
}
else
{
lean_object* v_reuseFailAlloc_6420_; 
v_reuseFailAlloc_6420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_a_6414_);
v___x_6419_ = v_reuseFailAlloc_6420_;
goto v_reusejp_6418_;
}
v_reusejp_6418_:
{
return v___x_6419_;
}
}
}
v___jp_6422_:
{
lean_object* v___x_6431_; lean_object* v_cfg_6432_; lean_object* v___x_6433_; uint8_t v___x_6434_; 
v___x_6431_ = lean_unsigned_to_nat(2u);
v_cfg_6432_ = l_Lean_Syntax_getArg(v_stx_6067_, v___x_6431_);
v___x_6433_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_6432_);
v___x_6434_ = l_Lean_Syntax_isOfKind(v_cfg_6432_, v___x_6433_);
if (v___x_6434_ == 0)
{
lean_object* v___x_6435_; 
lean_dec(v_cfg_6432_);
lean_dec(v_mutTk_x3f_6423_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
lean_dec(v_stx_6067_);
v___x_6435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6435_;
}
else
{
lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; uint8_t v___x_6440_; lean_object* v___x_6441_; lean_object* v___x_6442_; lean_object* v___x_6443_; 
v___x_6436_ = lean_unsigned_to_nat(3u);
v___x_6437_ = l_Lean_Syntax_getArg(v_stx_6067_, v___x_6436_);
lean_dec(v_stx_6067_);
v___x_6438_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
v___x_6439_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
v___x_6440_ = 0;
v___x_6441_ = lean_box(0);
v___x_6442_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
lean_inc(v_cfg_6432_);
v___x_6443_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_cfg_6432_, v_mutTk_x3f_6423_, v___x_6442_, v___y_6424_, v___y_6425_, v___y_6426_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_);
if (lean_obj_tag(v___x_6443_) == 0)
{
lean_object* v_a_6444_; lean_object* v___x_6445_; 
v_a_6444_ = lean_ctor_get(v___x_6443_, 0);
lean_inc(v_a_6444_);
lean_dec_ref_known(v___x_6443_, 1);
v___x_6445_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_6444_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_);
if (lean_obj_tag(v___x_6445_) == 0)
{
uint8_t v_nondep_6446_; 
lean_dec_ref_known(v___x_6445_, 1);
v_nondep_6446_ = lean_ctor_get_uint8(v_a_6444_, sizeof(void*)*1);
if (v_nondep_6446_ == 0)
{
uint8_t v_usedOnly_6447_; 
v_usedOnly_6447_ = lean_ctor_get_uint8(v_a_6444_, sizeof(void*)*1 + 1);
if (v_usedOnly_6447_ == 0)
{
uint8_t v_zeta_6448_; 
v_zeta_6448_ = lean_ctor_get_uint8(v_a_6444_, sizeof(void*)*1 + 2);
if (v_zeta_6448_ == 0)
{
lean_object* v_eq_x3f_6449_; 
v_eq_x3f_6449_ = lean_ctor_get(v_a_6444_, 0);
lean_inc(v_eq_x3f_6449_);
lean_dec(v_a_6444_);
if (lean_obj_tag(v_eq_x3f_6449_) == 0)
{
lean_dec(v_cfg_6432_);
lean_inc(v_mutTk_x3f_6423_);
v___y_6335_ = v_mutTk_x3f_6423_;
v___y_6336_ = v___x_6433_;
v___y_6337_ = v___x_6436_;
v___y_6338_ = v_mutTk_x3f_6423_;
v___y_6339_ = v___x_6439_;
v___y_6340_ = v___x_6441_;
v___y_6341_ = v___x_6437_;
v___y_6342_ = v___x_6438_;
v___y_6343_ = v___x_6431_;
v___y_6344_ = v___x_6440_;
v___y_6345_ = v___y_6424_;
v___y_6346_ = v___y_6425_;
v___y_6347_ = v___y_6426_;
v___y_6348_ = v___y_6427_;
v___y_6349_ = v___y_6428_;
v___y_6350_ = v___y_6429_;
v___y_6351_ = v___y_6430_;
goto v___jp_6334_;
}
else
{
lean_dec_ref_known(v_eq_x3f_6449_, 1);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
lean_inc(v_mutTk_x3f_6423_);
v___y_6394_ = v_mutTk_x3f_6423_;
v___y_6395_ = v___x_6433_;
v___y_6396_ = v___x_6439_;
v___y_6397_ = v___x_6441_;
v___y_6398_ = v___y_6429_;
v___y_6399_ = v___y_6428_;
v___y_6400_ = v___x_6440_;
v___y_6401_ = v___y_6424_;
v___y_6402_ = v___y_6425_;
v___y_6403_ = v___y_6430_;
v___y_6404_ = v___x_6436_;
v___y_6405_ = v___y_6426_;
v___y_6406_ = v_cfg_6432_;
v___y_6407_ = v_mutTk_x3f_6423_;
v___y_6408_ = v___x_6437_;
v___y_6409_ = v___x_6438_;
v___y_6410_ = v___x_6431_;
v___y_6411_ = v___y_6427_;
goto v___jp_6393_;
}
}
else
{
lean_dec(v_a_6444_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
lean_inc(v_mutTk_x3f_6423_);
v___y_6394_ = v_mutTk_x3f_6423_;
v___y_6395_ = v___x_6433_;
v___y_6396_ = v___x_6439_;
v___y_6397_ = v___x_6441_;
v___y_6398_ = v___y_6429_;
v___y_6399_ = v___y_6428_;
v___y_6400_ = v___x_6440_;
v___y_6401_ = v___y_6424_;
v___y_6402_ = v___y_6425_;
v___y_6403_ = v___y_6430_;
v___y_6404_ = v___x_6436_;
v___y_6405_ = v___y_6426_;
v___y_6406_ = v_cfg_6432_;
v___y_6407_ = v_mutTk_x3f_6423_;
v___y_6408_ = v___x_6437_;
v___y_6409_ = v___x_6438_;
v___y_6410_ = v___x_6431_;
v___y_6411_ = v___y_6427_;
goto v___jp_6393_;
}
}
else
{
lean_dec(v_a_6444_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
lean_inc(v_mutTk_x3f_6423_);
v___y_6394_ = v_mutTk_x3f_6423_;
v___y_6395_ = v___x_6433_;
v___y_6396_ = v___x_6439_;
v___y_6397_ = v___x_6441_;
v___y_6398_ = v___y_6429_;
v___y_6399_ = v___y_6428_;
v___y_6400_ = v___x_6440_;
v___y_6401_ = v___y_6424_;
v___y_6402_ = v___y_6425_;
v___y_6403_ = v___y_6430_;
v___y_6404_ = v___x_6436_;
v___y_6405_ = v___y_6426_;
v___y_6406_ = v_cfg_6432_;
v___y_6407_ = v_mutTk_x3f_6423_;
v___y_6408_ = v___x_6437_;
v___y_6409_ = v___x_6438_;
v___y_6410_ = v___x_6431_;
v___y_6411_ = v___y_6427_;
goto v___jp_6393_;
}
}
else
{
lean_dec(v_a_6444_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
lean_inc(v_mutTk_x3f_6423_);
v___y_6394_ = v_mutTk_x3f_6423_;
v___y_6395_ = v___x_6433_;
v___y_6396_ = v___x_6439_;
v___y_6397_ = v___x_6441_;
v___y_6398_ = v___y_6429_;
v___y_6399_ = v___y_6428_;
v___y_6400_ = v___x_6440_;
v___y_6401_ = v___y_6424_;
v___y_6402_ = v___y_6425_;
v___y_6403_ = v___y_6430_;
v___y_6404_ = v___x_6436_;
v___y_6405_ = v___y_6426_;
v___y_6406_ = v_cfg_6432_;
v___y_6407_ = v_mutTk_x3f_6423_;
v___y_6408_ = v___x_6437_;
v___y_6409_ = v___x_6438_;
v___y_6410_ = v___x_6431_;
v___y_6411_ = v___y_6427_;
goto v___jp_6393_;
}
}
else
{
lean_object* v_a_6450_; lean_object* v___x_6452_; uint8_t v_isShared_6453_; uint8_t v_isSharedCheck_6457_; 
lean_dec(v_a_6444_);
lean_dec(v___x_6437_);
lean_dec(v_cfg_6432_);
lean_dec(v_mutTk_x3f_6423_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v_a_6450_ = lean_ctor_get(v___x_6445_, 0);
v_isSharedCheck_6457_ = !lean_is_exclusive(v___x_6445_);
if (v_isSharedCheck_6457_ == 0)
{
v___x_6452_ = v___x_6445_;
v_isShared_6453_ = v_isSharedCheck_6457_;
goto v_resetjp_6451_;
}
else
{
lean_inc(v_a_6450_);
lean_dec(v___x_6445_);
v___x_6452_ = lean_box(0);
v_isShared_6453_ = v_isSharedCheck_6457_;
goto v_resetjp_6451_;
}
v_resetjp_6451_:
{
lean_object* v___x_6455_; 
if (v_isShared_6453_ == 0)
{
v___x_6455_ = v___x_6452_;
goto v_reusejp_6454_;
}
else
{
lean_object* v_reuseFailAlloc_6456_; 
v_reuseFailAlloc_6456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_a_6450_);
v___x_6455_ = v_reuseFailAlloc_6456_;
goto v_reusejp_6454_;
}
v_reusejp_6454_:
{
return v___x_6455_;
}
}
}
}
else
{
lean_object* v_a_6458_; lean_object* v___x_6460_; uint8_t v_isShared_6461_; uint8_t v_isSharedCheck_6465_; 
lean_dec(v___x_6437_);
lean_dec(v_cfg_6432_);
lean_dec(v_mutTk_x3f_6423_);
lean_dec(v_tk_6192_);
lean_dec_ref(v_dec_6068_);
v_a_6458_ = lean_ctor_get(v___x_6443_, 0);
v_isSharedCheck_6465_ = !lean_is_exclusive(v___x_6443_);
if (v_isSharedCheck_6465_ == 0)
{
v___x_6460_ = v___x_6443_;
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
else
{
lean_inc(v_a_6458_);
lean_dec(v___x_6443_);
v___x_6460_ = lean_box(0);
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
v_resetjp_6459_:
{
lean_object* v___x_6463_; 
if (v_isShared_6461_ == 0)
{
v___x_6463_ = v___x_6460_;
goto v_reusejp_6462_;
}
else
{
lean_object* v_reuseFailAlloc_6464_; 
v_reuseFailAlloc_6464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6464_, 0, v_a_6458_);
v___x_6463_ = v_reuseFailAlloc_6464_;
goto v_reusejp_6462_;
}
v_reusejp_6462_:
{
return v___x_6463_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_6473_, lean_object* v_dec_6474_, lean_object* v_a_6475_, lean_object* v_a_6476_, lean_object* v_a_6477_, lean_object* v_a_6478_, lean_object* v_a_6479_, lean_object* v_a_6480_, lean_object* v_a_6481_, lean_object* v_a_6482_){
_start:
{
lean_object* v_res_6483_; 
v_res_6483_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_6473_, v_dec_6474_, v_a_6475_, v_a_6476_, v_a_6477_, v_a_6478_, v_a_6479_, v_a_6480_, v_a_6481_);
lean_dec(v_a_6481_);
lean_dec_ref(v_a_6480_);
lean_dec(v_a_6479_);
lean_dec_ref(v_a_6478_);
lean_dec(v_a_6477_);
lean_dec_ref(v_a_6476_);
lean_dec_ref(v_a_6475_);
return v_res_6483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; 
v___x_6491_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6492_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_6493_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_6494_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_6495_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6491_, v___x_6492_, v___x_6493_, v___x_6494_);
return v___x_6495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_6496_){
_start:
{
lean_object* v_res_6497_; 
v_res_6497_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_6497_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3(void){
_start:
{
lean_object* v___x_6505_; lean_object* v___x_6506_; 
v___x_6505_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__2));
v___x_6506_ = l_Lean_stringToMessageData(v___x_6505_);
return v___x_6506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_6507_, lean_object* v_dec_6508_, lean_object* v_a_6509_, lean_object* v_a_6510_, lean_object* v_a_6511_, lean_object* v_a_6512_, lean_object* v_a_6513_, lean_object* v_a_6514_, lean_object* v_a_6515_){
_start:
{
lean_object* v___x_6517_; uint8_t v___x_6518_; 
v___x_6517_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_6507_);
v___x_6518_ = l_Lean_Syntax_isOfKind(v_stx_6507_, v___x_6517_);
if (v___x_6518_ == 0)
{
lean_object* v___x_6519_; 
lean_dec_ref(v_dec_6508_);
lean_dec(v_stx_6507_);
v___x_6519_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6519_;
}
else
{
lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; uint8_t v___x_6523_; 
v___x_6520_ = lean_unsigned_to_nat(0u);
v___x_6521_ = l_Lean_Syntax_getArg(v_stx_6507_, v___x_6520_);
lean_dec(v_stx_6507_);
v___x_6522_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_6521_);
v___x_6523_ = l_Lean_Syntax_isOfKind(v___x_6521_, v___x_6522_);
if (v___x_6523_ == 0)
{
lean_object* v___x_6524_; uint8_t v___x_6525_; 
v___x_6524_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
lean_inc(v___x_6521_);
v___x_6525_ = l_Lean_Syntax_isOfKind(v___x_6521_, v___x_6524_);
if (v___x_6525_ == 0)
{
lean_object* v___x_6526_; 
lean_dec(v___x_6521_);
lean_dec_ref(v_dec_6508_);
v___x_6526_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6526_;
}
else
{
lean_object* v___x_6527_; lean_object* v___y_6529_; lean_object* v___y_6530_; lean_object* v___y_6531_; lean_object* v___y_6532_; lean_object* v___y_6533_; lean_object* v___y_6534_; lean_object* v___y_6535_; lean_object* v___y_6536_; lean_object* v___y_6537_; lean_object* v_t_x3f_6566_; lean_object* v___y_6567_; lean_object* v___y_6568_; lean_object* v___y_6569_; lean_object* v___y_6570_; lean_object* v___y_6571_; lean_object* v___y_6572_; lean_object* v___y_6573_; lean_object* v___x_6591_; lean_object* v___x_6592_; uint8_t v___x_6593_; 
v___x_6527_ = l_Lean_Syntax_getArg(v___x_6521_, v___x_6520_);
v___x_6591_ = lean_unsigned_to_nat(1u);
v___x_6592_ = l_Lean_Syntax_getArg(v___x_6521_, v___x_6591_);
v___x_6593_ = l_Lean_Syntax_isNone(v___x_6592_);
if (v___x_6593_ == 0)
{
uint8_t v___x_6594_; 
lean_inc(v___x_6592_);
v___x_6594_ = l_Lean_Syntax_matchesNull(v___x_6592_, v___x_6591_);
if (v___x_6594_ == 0)
{
lean_object* v___x_6595_; 
lean_dec(v___x_6592_);
lean_dec(v___x_6527_);
lean_dec(v___x_6521_);
lean_dec_ref(v_dec_6508_);
v___x_6595_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6595_;
}
else
{
lean_object* v___x_6596_; lean_object* v___x_6597_; uint8_t v___x_6598_; 
v___x_6596_ = l_Lean_Syntax_getArg(v___x_6592_, v___x_6520_);
lean_dec(v___x_6592_);
v___x_6597_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6596_);
v___x_6598_ = l_Lean_Syntax_isOfKind(v___x_6596_, v___x_6597_);
if (v___x_6598_ == 0)
{
lean_object* v___x_6599_; 
lean_dec(v___x_6596_);
lean_dec(v___x_6527_);
lean_dec(v___x_6521_);
lean_dec_ref(v_dec_6508_);
v___x_6599_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6599_;
}
else
{
lean_object* v_t_x3f_6600_; lean_object* v___x_6601_; 
v_t_x3f_6600_ = l_Lean_Syntax_getArg(v___x_6596_, v___x_6591_);
lean_dec(v___x_6596_);
v___x_6601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6601_, 0, v_t_x3f_6600_);
v_t_x3f_6566_ = v___x_6601_;
v___y_6567_ = v_a_6509_;
v___y_6568_ = v_a_6510_;
v___y_6569_ = v_a_6511_;
v___y_6570_ = v_a_6512_;
v___y_6571_ = v_a_6513_;
v___y_6572_ = v_a_6514_;
v___y_6573_ = v_a_6515_;
goto v___jp_6565_;
}
}
}
else
{
lean_object* v___x_6602_; 
lean_dec(v___x_6592_);
v___x_6602_ = lean_box(0);
v_t_x3f_6566_ = v___x_6602_;
v___y_6567_ = v_a_6509_;
v___y_6568_ = v_a_6510_;
v___y_6569_ = v_a_6511_;
v___y_6570_ = v_a_6512_;
v___y_6571_ = v_a_6513_;
v___y_6572_ = v_a_6514_;
v___y_6573_ = v_a_6515_;
goto v___jp_6565_;
}
v___jp_6528_:
{
lean_object* v___x_6538_; lean_object* v___x_6539_; 
v___x_6538_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6539_ = l_Lean_Core_mkFreshUserName(v___x_6538_, v___y_6536_, v___y_6537_);
if (lean_obj_tag(v___x_6539_) == 0)
{
lean_object* v_a_6540_; lean_object* v_ref_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; uint8_t v_kind_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; lean_object* v___x_6556_; 
v_a_6540_ = lean_ctor_get(v___x_6539_, 0);
lean_inc(v_a_6540_);
lean_dec_ref_known(v___x_6539_, 1);
v_ref_6541_ = lean_ctor_get(v___y_6536_, 2);
v___x_6542_ = l_Lean_mkIdentFrom(v___x_6527_, v_a_6540_, v___x_6523_);
v___x_6543_ = l_Lean_SourceInfo_fromRef(v_ref_6541_, v___x_6523_);
v___x_6544_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6545_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
v___x_6546_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6547_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_6543_, 3);
v___x_6548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6548_, 0, v___x_6543_);
lean_ctor_set(v___x_6548_, 1, v___x_6546_);
lean_ctor_set(v___x_6548_, 2, v___x_6547_);
v___x_6549_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6550_, 0, v___x_6543_);
lean_ctor_set(v___x_6550_, 1, v___x_6549_);
lean_inc(v___x_6542_);
lean_inc_ref(v___x_6548_);
v___x_6551_ = l_Lean_Syntax_node5(v___x_6543_, v___x_6545_, v___x_6527_, v___x_6548_, v___x_6548_, v___x_6550_, v___x_6542_);
v_kind_6552_ = lean_ctor_get_uint8(v_dec_6508_, sizeof(void*)*3);
v___x_6553_ = l_Lean_Syntax_node1(v___x_6543_, v___x_6544_, v___x_6551_);
v___x_6554_ = lean_box(v___x_6518_);
v___x_6555_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6555_, 0, v___x_6553_);
lean_closure_set(v___x_6555_, 1, v_dec_6508_);
lean_closure_set(v___x_6555_, 2, v___x_6554_);
v___x_6556_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6542_, v___y_6529_, v___y_6530_, v___x_6555_, v_kind_6552_, v___y_6531_, v___y_6532_, v___y_6533_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_);
return v___x_6556_;
}
else
{
lean_object* v_a_6557_; lean_object* v___x_6559_; uint8_t v_isShared_6560_; uint8_t v_isSharedCheck_6564_; 
lean_dec(v___y_6530_);
lean_dec(v___y_6529_);
lean_dec(v___x_6527_);
lean_dec_ref(v_dec_6508_);
v_a_6557_ = lean_ctor_get(v___x_6539_, 0);
v_isSharedCheck_6564_ = !lean_is_exclusive(v___x_6539_);
if (v_isSharedCheck_6564_ == 0)
{
v___x_6559_ = v___x_6539_;
v_isShared_6560_ = v_isSharedCheck_6564_;
goto v_resetjp_6558_;
}
else
{
lean_inc(v_a_6557_);
lean_dec(v___x_6539_);
v___x_6559_ = lean_box(0);
v_isShared_6560_ = v_isSharedCheck_6564_;
goto v_resetjp_6558_;
}
v_resetjp_6558_:
{
lean_object* v___x_6562_; 
if (v_isShared_6560_ == 0)
{
v___x_6562_ = v___x_6559_;
goto v_reusejp_6561_;
}
else
{
lean_object* v_reuseFailAlloc_6563_; 
v_reuseFailAlloc_6563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6563_, 0, v_a_6557_);
v___x_6562_ = v_reuseFailAlloc_6563_;
goto v_reusejp_6561_;
}
v_reusejp_6561_:
{
return v___x_6562_;
}
}
}
}
v___jp_6565_:
{
lean_object* v___x_6574_; lean_object* v_rhs_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; uint8_t v___x_6578_; 
v___x_6574_ = lean_unsigned_to_nat(3u);
v_rhs_6575_ = l_Lean_Syntax_getArg(v___x_6521_, v___x_6574_);
v___x_6576_ = lean_unsigned_to_nat(4u);
v___x_6577_ = l_Lean_Syntax_getArg(v___x_6521_, v___x_6576_);
lean_dec(v___x_6521_);
v___x_6578_ = l_Lean_Syntax_isNone(v___x_6577_);
if (v___x_6578_ == 0)
{
uint8_t v___x_6579_; 
lean_dec(v_rhs_6575_);
lean_dec(v_t_x3f_6566_);
lean_dec(v___x_6527_);
lean_dec_ref(v_dec_6508_);
v___x_6579_ = l_Lean_Syntax_matchesNull(v___x_6577_, v___x_6574_);
if (v___x_6579_ == 0)
{
lean_object* v___x_6580_; 
v___x_6580_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6580_;
}
else
{
lean_object* v___x_6581_; lean_object* v___x_6582_; lean_object* v_a_6583_; lean_object* v___x_6585_; uint8_t v_isShared_6586_; uint8_t v_isSharedCheck_6590_; 
v___x_6581_ = lean_obj_once(&l_Lean_Elab_Do_elabDoReassignArrow___closed__3, &l_Lean_Elab_Do_elabDoReassignArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3);
v___x_6582_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v___x_6581_, v___y_6570_, v___y_6571_, v___y_6572_, v___y_6573_);
v_a_6583_ = lean_ctor_get(v___x_6582_, 0);
v_isSharedCheck_6590_ = !lean_is_exclusive(v___x_6582_);
if (v_isSharedCheck_6590_ == 0)
{
v___x_6585_ = v___x_6582_;
v_isShared_6586_ = v_isSharedCheck_6590_;
goto v_resetjp_6584_;
}
else
{
lean_inc(v_a_6583_);
lean_dec(v___x_6582_);
v___x_6585_ = lean_box(0);
v_isShared_6586_ = v_isSharedCheck_6590_;
goto v_resetjp_6584_;
}
v_resetjp_6584_:
{
lean_object* v___x_6588_; 
if (v_isShared_6586_ == 0)
{
v___x_6588_ = v___x_6585_;
goto v_reusejp_6587_;
}
else
{
lean_object* v_reuseFailAlloc_6589_; 
v_reuseFailAlloc_6589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6589_, 0, v_a_6583_);
v___x_6588_ = v_reuseFailAlloc_6589_;
goto v_reusejp_6587_;
}
v_reusejp_6587_:
{
return v___x_6588_;
}
}
}
}
else
{
lean_dec(v___x_6577_);
v___y_6529_ = v_t_x3f_6566_;
v___y_6530_ = v_rhs_6575_;
v___y_6531_ = v___y_6567_;
v___y_6532_ = v___y_6568_;
v___y_6533_ = v___y_6569_;
v___y_6534_ = v___y_6570_;
v___y_6535_ = v___y_6571_;
v___y_6536_ = v___y_6572_;
v___y_6537_ = v___y_6573_;
goto v___jp_6528_;
}
}
}
}
else
{
lean_object* v_x_6603_; lean_object* v___y_6605_; lean_object* v_t_6606_; lean_object* v___y_6607_; lean_object* v___y_6608_; lean_object* v___y_6609_; lean_object* v___y_6610_; lean_object* v___y_6611_; lean_object* v___y_6612_; lean_object* v___y_6613_; lean_object* v_t_x3f_6646_; lean_object* v___y_6647_; lean_object* v___y_6648_; lean_object* v___y_6649_; lean_object* v___y_6650_; lean_object* v___y_6651_; lean_object* v___y_6652_; lean_object* v___y_6653_; lean_object* v___x_6688_; uint8_t v___x_6689_; 
v_x_6603_ = l_Lean_Syntax_getArg(v___x_6521_, v___x_6520_);
v___x_6688_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_6603_);
v___x_6689_ = l_Lean_Syntax_isOfKind(v_x_6603_, v___x_6688_);
if (v___x_6689_ == 0)
{
lean_object* v___x_6690_; 
lean_dec(v_x_6603_);
lean_dec(v___x_6521_);
lean_dec_ref(v_dec_6508_);
v___x_6690_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6690_;
}
else
{
lean_object* v___x_6691_; lean_object* v___x_6692_; uint8_t v___x_6693_; 
v___x_6691_ = lean_unsigned_to_nat(1u);
v___x_6692_ = l_Lean_Syntax_getArg(v___x_6521_, v___x_6691_);
v___x_6693_ = l_Lean_Syntax_isNone(v___x_6692_);
if (v___x_6693_ == 0)
{
uint8_t v___x_6694_; 
lean_inc(v___x_6692_);
v___x_6694_ = l_Lean_Syntax_matchesNull(v___x_6692_, v___x_6691_);
if (v___x_6694_ == 0)
{
lean_object* v___x_6695_; 
lean_dec(v___x_6692_);
lean_dec(v_x_6603_);
lean_dec(v___x_6521_);
lean_dec_ref(v_dec_6508_);
v___x_6695_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6695_;
}
else
{
lean_object* v___x_6696_; lean_object* v___x_6697_; uint8_t v___x_6698_; 
v___x_6696_ = l_Lean_Syntax_getArg(v___x_6692_, v___x_6520_);
lean_dec(v___x_6692_);
v___x_6697_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6696_);
v___x_6698_ = l_Lean_Syntax_isOfKind(v___x_6696_, v___x_6697_);
if (v___x_6698_ == 0)
{
lean_object* v___x_6699_; 
lean_dec(v___x_6696_);
lean_dec(v_x_6603_);
lean_dec(v___x_6521_);
lean_dec_ref(v_dec_6508_);
v___x_6699_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6699_;
}
else
{
lean_object* v_t_x3f_6700_; lean_object* v___x_6701_; 
v_t_x3f_6700_ = l_Lean_Syntax_getArg(v___x_6696_, v___x_6691_);
lean_dec(v___x_6696_);
v___x_6701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6701_, 0, v_t_x3f_6700_);
v_t_x3f_6646_ = v___x_6701_;
v___y_6647_ = v_a_6509_;
v___y_6648_ = v_a_6510_;
v___y_6649_ = v_a_6511_;
v___y_6650_ = v_a_6512_;
v___y_6651_ = v_a_6513_;
v___y_6652_ = v_a_6514_;
v___y_6653_ = v_a_6515_;
goto v___jp_6645_;
}
}
}
else
{
lean_object* v___x_6702_; 
lean_dec(v___x_6692_);
v___x_6702_ = lean_box(0);
v_t_x3f_6646_ = v___x_6702_;
v___y_6647_ = v_a_6509_;
v___y_6648_ = v_a_6510_;
v___y_6649_ = v_a_6511_;
v___y_6650_ = v_a_6512_;
v___y_6651_ = v_a_6513_;
v___y_6652_ = v_a_6514_;
v___y_6653_ = v_a_6515_;
goto v___jp_6645_;
}
}
v___jp_6604_:
{
lean_object* v___x_6614_; lean_object* v___x_6615_; 
v___x_6614_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6615_ = l_Lean_Core_mkFreshUserName(v___x_6614_, v___y_6612_, v___y_6613_);
if (lean_obj_tag(v___x_6615_) == 0)
{
lean_object* v_a_6616_; lean_object* v_ref_6617_; uint8_t v___x_6618_; lean_object* v___x_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6630_; uint8_t v_kind_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; lean_object* v___x_6634_; lean_object* v___x_6635_; lean_object* v___x_6636_; 
v_a_6616_ = lean_ctor_get(v___x_6615_, 0);
lean_inc(v_a_6616_);
lean_dec_ref_known(v___x_6615_, 1);
v_ref_6617_ = lean_ctor_get(v___y_6612_, 2);
v___x_6618_ = 0;
v___x_6619_ = l_Lean_mkIdentFrom(v_x_6603_, v_a_6616_, v___x_6618_);
v___x_6620_ = l_Lean_SourceInfo_fromRef(v_ref_6617_, v___x_6618_);
v___x_6621_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6622_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_6623_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v___x_6620_, 4);
v___x_6624_ = l_Lean_Syntax_node1(v___x_6620_, v___x_6623_, v_x_6603_);
v___x_6625_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6626_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_6627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6627_, 0, v___x_6620_);
lean_ctor_set(v___x_6627_, 1, v___x_6625_);
lean_ctor_set(v___x_6627_, 2, v___x_6626_);
v___x_6628_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6629_, 0, v___x_6620_);
lean_ctor_set(v___x_6629_, 1, v___x_6628_);
lean_inc(v___x_6619_);
lean_inc_ref(v___x_6627_);
v___x_6630_ = l_Lean_Syntax_node5(v___x_6620_, v___x_6622_, v___x_6624_, v___x_6627_, v___x_6627_, v___x_6629_, v___x_6619_);
v_kind_6631_ = lean_ctor_get_uint8(v_dec_6508_, sizeof(void*)*3);
v___x_6632_ = l_Lean_Syntax_node1(v___x_6620_, v___x_6621_, v___x_6630_);
v___x_6633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6633_, 0, v_t_6606_);
v___x_6634_ = lean_box(v___x_6518_);
v___x_6635_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6635_, 0, v___x_6632_);
lean_closure_set(v___x_6635_, 1, v_dec_6508_);
lean_closure_set(v___x_6635_, 2, v___x_6634_);
v___x_6636_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6619_, v___x_6633_, v___y_6605_, v___x_6635_, v_kind_6631_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_, v___y_6611_, v___y_6612_, v___y_6613_);
return v___x_6636_;
}
else
{
lean_object* v_a_6637_; lean_object* v___x_6639_; uint8_t v_isShared_6640_; uint8_t v_isSharedCheck_6644_; 
lean_dec(v_t_6606_);
lean_dec(v___y_6605_);
lean_dec(v_x_6603_);
lean_dec_ref(v_dec_6508_);
v_a_6637_ = lean_ctor_get(v___x_6615_, 0);
v_isSharedCheck_6644_ = !lean_is_exclusive(v___x_6615_);
if (v_isSharedCheck_6644_ == 0)
{
v___x_6639_ = v___x_6615_;
v_isShared_6640_ = v_isSharedCheck_6644_;
goto v_resetjp_6638_;
}
else
{
lean_inc(v_a_6637_);
lean_dec(v___x_6615_);
v___x_6639_ = lean_box(0);
v_isShared_6640_ = v_isSharedCheck_6644_;
goto v_resetjp_6638_;
}
v_resetjp_6638_:
{
lean_object* v___x_6642_; 
if (v_isShared_6640_ == 0)
{
v___x_6642_ = v___x_6639_;
goto v_reusejp_6641_;
}
else
{
lean_object* v_reuseFailAlloc_6643_; 
v_reuseFailAlloc_6643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6643_, 0, v_a_6637_);
v___x_6642_ = v_reuseFailAlloc_6643_;
goto v_reusejp_6641_;
}
v_reusejp_6641_:
{
return v___x_6642_;
}
}
}
}
v___jp_6645_:
{
lean_object* v___x_6654_; lean_object* v_rhs_6655_; lean_object* v___x_6656_; 
v___x_6654_ = lean_unsigned_to_nat(3u);
v_rhs_6655_ = l_Lean_Syntax_getArg(v___x_6521_, v___x_6654_);
lean_dec(v___x_6521_);
v___x_6656_ = l_Lean_Elab_Do_throwUnlessMutVarDeclared(v_x_6603_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_, v___y_6653_);
if (lean_obj_tag(v___x_6656_) == 0)
{
lean_dec_ref_known(v___x_6656_, 1);
if (lean_obj_tag(v_t_x3f_6646_) == 0)
{
lean_object* v___x_6657_; lean_object* v___x_6658_; 
v___x_6657_ = l_Lean_TSyntax_getId(v_x_6603_);
v___x_6658_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_6657_, v___y_6650_, v___y_6651_, v___y_6652_, v___y_6653_);
if (lean_obj_tag(v___x_6658_) == 0)
{
lean_object* v_a_6659_; lean_object* v___x_6660_; lean_object* v___x_6661_; 
v_a_6659_ = lean_ctor_get(v___x_6658_, 0);
lean_inc(v_a_6659_);
lean_dec_ref_known(v___x_6658_, 1);
v___x_6660_ = l_Lean_LocalDecl_type(v_a_6659_);
lean_dec(v_a_6659_);
v___x_6661_ = l_Lean_Elab_Term_exprToSyntax(v___x_6660_, v___y_6648_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_, v___y_6653_);
if (lean_obj_tag(v___x_6661_) == 0)
{
lean_object* v_a_6662_; 
v_a_6662_ = lean_ctor_get(v___x_6661_, 0);
lean_inc(v_a_6662_);
lean_dec_ref_known(v___x_6661_, 1);
v___y_6605_ = v_rhs_6655_;
v_t_6606_ = v_a_6662_;
v___y_6607_ = v___y_6647_;
v___y_6608_ = v___y_6648_;
v___y_6609_ = v___y_6649_;
v___y_6610_ = v___y_6650_;
v___y_6611_ = v___y_6651_;
v___y_6612_ = v___y_6652_;
v___y_6613_ = v___y_6653_;
goto v___jp_6604_;
}
else
{
lean_object* v_a_6663_; lean_object* v___x_6665_; uint8_t v_isShared_6666_; uint8_t v_isSharedCheck_6670_; 
lean_dec(v_rhs_6655_);
lean_dec(v_x_6603_);
lean_dec_ref(v_dec_6508_);
v_a_6663_ = lean_ctor_get(v___x_6661_, 0);
v_isSharedCheck_6670_ = !lean_is_exclusive(v___x_6661_);
if (v_isSharedCheck_6670_ == 0)
{
v___x_6665_ = v___x_6661_;
v_isShared_6666_ = v_isSharedCheck_6670_;
goto v_resetjp_6664_;
}
else
{
lean_inc(v_a_6663_);
lean_dec(v___x_6661_);
v___x_6665_ = lean_box(0);
v_isShared_6666_ = v_isSharedCheck_6670_;
goto v_resetjp_6664_;
}
v_resetjp_6664_:
{
lean_object* v___x_6668_; 
if (v_isShared_6666_ == 0)
{
v___x_6668_ = v___x_6665_;
goto v_reusejp_6667_;
}
else
{
lean_object* v_reuseFailAlloc_6669_; 
v_reuseFailAlloc_6669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6669_, 0, v_a_6663_);
v___x_6668_ = v_reuseFailAlloc_6669_;
goto v_reusejp_6667_;
}
v_reusejp_6667_:
{
return v___x_6668_;
}
}
}
}
else
{
lean_object* v_a_6671_; lean_object* v___x_6673_; uint8_t v_isShared_6674_; uint8_t v_isSharedCheck_6678_; 
lean_dec(v_rhs_6655_);
lean_dec(v_x_6603_);
lean_dec_ref(v_dec_6508_);
v_a_6671_ = lean_ctor_get(v___x_6658_, 0);
v_isSharedCheck_6678_ = !lean_is_exclusive(v___x_6658_);
if (v_isSharedCheck_6678_ == 0)
{
v___x_6673_ = v___x_6658_;
v_isShared_6674_ = v_isSharedCheck_6678_;
goto v_resetjp_6672_;
}
else
{
lean_inc(v_a_6671_);
lean_dec(v___x_6658_);
v___x_6673_ = lean_box(0);
v_isShared_6674_ = v_isSharedCheck_6678_;
goto v_resetjp_6672_;
}
v_resetjp_6672_:
{
lean_object* v___x_6676_; 
if (v_isShared_6674_ == 0)
{
v___x_6676_ = v___x_6673_;
goto v_reusejp_6675_;
}
else
{
lean_object* v_reuseFailAlloc_6677_; 
v_reuseFailAlloc_6677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6677_, 0, v_a_6671_);
v___x_6676_ = v_reuseFailAlloc_6677_;
goto v_reusejp_6675_;
}
v_reusejp_6675_:
{
return v___x_6676_;
}
}
}
}
else
{
lean_object* v_val_6679_; 
v_val_6679_ = lean_ctor_get(v_t_x3f_6646_, 0);
lean_inc(v_val_6679_);
lean_dec_ref_known(v_t_x3f_6646_, 1);
v___y_6605_ = v_rhs_6655_;
v_t_6606_ = v_val_6679_;
v___y_6607_ = v___y_6647_;
v___y_6608_ = v___y_6648_;
v___y_6609_ = v___y_6649_;
v___y_6610_ = v___y_6650_;
v___y_6611_ = v___y_6651_;
v___y_6612_ = v___y_6652_;
v___y_6613_ = v___y_6653_;
goto v___jp_6604_;
}
}
else
{
lean_object* v_a_6680_; lean_object* v___x_6682_; uint8_t v_isShared_6683_; uint8_t v_isSharedCheck_6687_; 
lean_dec(v_rhs_6655_);
lean_dec(v_t_x3f_6646_);
lean_dec(v_x_6603_);
lean_dec_ref(v_dec_6508_);
v_a_6680_ = lean_ctor_get(v___x_6656_, 0);
v_isSharedCheck_6687_ = !lean_is_exclusive(v___x_6656_);
if (v_isSharedCheck_6687_ == 0)
{
v___x_6682_ = v___x_6656_;
v_isShared_6683_ = v_isSharedCheck_6687_;
goto v_resetjp_6681_;
}
else
{
lean_inc(v_a_6680_);
lean_dec(v___x_6656_);
v___x_6682_ = lean_box(0);
v_isShared_6683_ = v_isSharedCheck_6687_;
goto v_resetjp_6681_;
}
v_resetjp_6681_:
{
lean_object* v___x_6685_; 
if (v_isShared_6683_ == 0)
{
v___x_6685_ = v___x_6682_;
goto v_reusejp_6684_;
}
else
{
lean_object* v_reuseFailAlloc_6686_; 
v_reuseFailAlloc_6686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6686_, 0, v_a_6680_);
v___x_6685_ = v_reuseFailAlloc_6686_;
goto v_reusejp_6684_;
}
v_reusejp_6684_:
{
return v___x_6685_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_6703_, lean_object* v_dec_6704_, lean_object* v_a_6705_, lean_object* v_a_6706_, lean_object* v_a_6707_, lean_object* v_a_6708_, lean_object* v_a_6709_, lean_object* v_a_6710_, lean_object* v_a_6711_, lean_object* v_a_6712_){
_start:
{
lean_object* v_res_6713_; 
v_res_6713_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_6703_, v_dec_6704_, v_a_6705_, v_a_6706_, v_a_6707_, v_a_6708_, v_a_6709_, v_a_6710_, v_a_6711_);
lean_dec(v_a_6711_);
lean_dec_ref(v_a_6710_);
lean_dec(v_a_6709_);
lean_dec_ref(v_a_6708_);
lean_dec(v_a_6707_);
lean_dec_ref(v_a_6706_);
lean_dec_ref(v_a_6705_);
return v_res_6713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; 
v___x_6721_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6722_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_6723_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_6724_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_6725_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6721_, v___x_6722_, v___x_6723_, v___x_6724_);
return v___x_6725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_6726_){
_start:
{
lean_object* v_res_6727_; 
v_res_6727_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_6727_;
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
