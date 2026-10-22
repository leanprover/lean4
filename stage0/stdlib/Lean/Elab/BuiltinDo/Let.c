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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24___boxed(lean_object*, lean_object*, lean_object*);
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
v___x_997_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_986_, v_a_995_, v___x_831_, v___x_831_, v___x_996_, v___y_989_, v___y_994_, v___y_990_, v___y_988_, v___y_993_, v___y_992_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref_known(v___x_997_, 1);
v___x_998_ = l_Lean_TSyntax_getId(v_x_986_);
v___x_999_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_998_, v___y_990_, v___y_988_, v___y_993_, v___y_992_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Lean_LocalDecl_type(v_a_1000_);
lean_dec(v_a_1000_);
v___x_1002_ = l_Lean_Elab_Term_exprToSyntax(v___x_1001_, v___y_989_, v___y_994_, v___y_990_, v___y_988_, v___y_993_, v___y_992_);
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
v___x_1021_ = l_Lean_Syntax_node5(v___x_1009_, v___x_838_, v___x_1010_, v___x_1013_, v___x_1018_, v___x_1020_, v___y_991_);
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
lean_dec(v___y_991_);
lean_dec(v_x_986_);
return v___x_1002_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v___y_991_);
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
lean_dec(v___y_991_);
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
v___y_989_ = v___y_1045_;
v___y_990_ = v___y_1047_;
v___y_991_ = v___x_1052_;
v___y_992_ = v___y_1050_;
v___y_993_ = v___y_1049_;
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
v___y_988_ = v___y_1048_;
v___y_989_ = v___y_1045_;
v___y_990_ = v___y_1047_;
v___y_991_ = v___x_1052_;
v___y_992_ = v___y_1050_;
v___y_993_ = v___y_1049_;
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
uint8_t v___x_88290__boxed_1602_; uint8_t v___x_88293__boxed_1603_; lean_object* v_res_1604_; 
v___x_88290__boxed_1602_ = lean_unbox(v___x_1591_);
v___x_88293__boxed_1603_ = lean_unbox(v___x_1594_);
v_res_1604_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1589_, v___x_1590_, v___x_88290__boxed_1602_, v___x_1592_, v___x_1593_, v___x_88293__boxed_1603_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14___redArg(lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
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
v___x_1657_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14___redArg(v_n_1653_, v___x_1656_, v_k_1654_, v_v_1655_);
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
size_t v_x_88425__boxed_1762_; size_t v_x_88426__boxed_1763_; lean_object* v_res_1764_; 
v_x_88425__boxed_1762_ = lean_unbox_usize(v_x_1758_);
lean_dec(v_x_1758_);
v_x_88426__boxed_1763_ = lean_unbox_usize(v_x_1759_);
lean_dec(v_x_1759_);
v_res_1764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1757_, v_x_88425__boxed_1762_, v_x_88426__boxed_1763_, v_x_1760_, v_x_1761_);
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
uint8_t v___x_88722__boxed_1951_; uint8_t v___x_88723__boxed_1952_; uint8_t v___y_88725__boxed_1953_; lean_object* v_res_1954_; 
v___x_88722__boxed_1951_ = lean_unbox(v___x_1939_);
v___x_88723__boxed_1952_ = lean_unbox(v___x_1940_);
v___y_88725__boxed_1953_ = lean_unbox(v___y_1942_);
v_res_1954_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1937_, v_value_1938_, v___x_88722__boxed_1951_, v___x_88723__boxed_1952_, v___x_1941_, v___y_88725__boxed_1953_, v_xs_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
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
uint8_t v_zeta_boxed_2048_; uint8_t v___y_88944__boxed_2049_; uint8_t v_usedOnly_boxed_2050_; uint8_t v___x_88945__boxed_2051_; lean_object* v_res_2052_; 
v_zeta_boxed_2048_ = lean_unbox(v_zeta_2033_);
v___y_88944__boxed_2049_ = lean_unbox(v___y_2034_);
v_usedOnly_boxed_2050_ = lean_unbox(v_usedOnly_2036_);
v___x_88945__boxed_2051_ = lean_unbox(v___x_2037_);
v_res_2052_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_2029_, v_a_2030_, v_letOrReassign_2031_, v_a_2032_, v_zeta_boxed_2048_, v___y_88944__boxed_2049_, v_x_2035_, v_usedOnly_boxed_2050_, v___x_88945__boxed_2051_, v_snd_2038_, v_h_x27_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
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
uint8_t v_zeta_boxed_2135_; uint8_t v_usedOnly_boxed_2136_; uint8_t v___y_89102__boxed_2137_; uint8_t v___x_89103__boxed_2138_; lean_object* v_res_2139_; 
v_zeta_boxed_2135_ = lean_unbox(v_zeta_2121_);
v_usedOnly_boxed_2136_ = lean_unbox(v_usedOnly_2122_);
v___y_89102__boxed_2137_ = lean_unbox(v___y_2124_);
v___x_89103__boxed_2138_ = lean_unbox(v___x_2125_);
v_res_2139_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_id_2116_, v_eq_x3f_2117_, v_a_2118_, v_letOrReassign_2119_, v_a_2120_, v_zeta_boxed_2135_, v_usedOnly_boxed_2136_, v_snd_2123_, v___y_89102__boxed_2137_, v___x_89103__boxed_2138_, v_x_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
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
uint8_t v___x_89230__boxed_2162_; lean_object* v_res_2163_; 
v___x_89230__boxed_2162_ = lean_unbox(v___x_2152_);
v_res_2163_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v___x_89230__boxed_2162_, v_____do__lift_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
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
uint8_t v___x_89265__boxed_2189_; lean_object* v_res_2190_; 
v___x_89265__boxed_2189_ = lean_unbox(v___x_2179_);
v_res_2190_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v_term_2177_, v___x_2178_, v___x_89265__boxed_2189_, v___x_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0(lean_object* v_stx_2191_, lean_object* v_output_2192_, lean_object* v_trees_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_stx_2206_, lean_object* v_output_2207_, lean_object* v_trees_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0(v_stx_2206_, v_output_2207_, v_trees_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0(lean_object* v___y_2217_, lean_object* v_mkInfoTree_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v_a_2224_, lean_object* v_a_x3f_2225_){
_start:
{
lean_object* v___x_2227_; lean_object* v_infoState_2228_; lean_object* v_trees_2229_; lean_object* v___x_2230_; 
v___x_2227_ = lean_st_ref_get(v___y_2217_);
v_infoState_2228_ = lean_ctor_get(v___x_2227_, 8);
lean_inc_ref(v_infoState_2228_);
lean_dec(v___x_2227_);
v_trees_2229_ = lean_ctor_get(v_infoState_2228_, 2);
lean_inc_ref(v_trees_2229_);
lean_dec_ref(v_infoState_2228_);
lean_inc(v___y_2217_);
lean_inc_ref(v___y_2223_);
lean_inc(v___y_2222_);
lean_inc_ref(v___y_2221_);
lean_inc(v___y_2220_);
lean_inc_ref(v___y_2219_);
v___x_2230_ = lean_apply_8(v_mkInfoTree_2218_, v_trees_2229_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2217_, lean_box(0));
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2270_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2270_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2270_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v_infoState_2236_; lean_object* v_env_2237_; lean_object* v_nextMacroScope_2238_; lean_object* v_ngen_2239_; lean_object* v_auxDeclNGen_2240_; lean_object* v_traceState_2241_; lean_object* v_cache_2242_; lean_object* v_recordedDeps_2243_; lean_object* v_messages_2244_; lean_object* v_snapshotTasks_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2269_; 
v___x_2235_ = lean_st_ref_take(v___y_2217_);
v_infoState_2236_ = lean_ctor_get(v___x_2235_, 8);
v_env_2237_ = lean_ctor_get(v___x_2235_, 0);
v_nextMacroScope_2238_ = lean_ctor_get(v___x_2235_, 1);
v_ngen_2239_ = lean_ctor_get(v___x_2235_, 2);
v_auxDeclNGen_2240_ = lean_ctor_get(v___x_2235_, 3);
v_traceState_2241_ = lean_ctor_get(v___x_2235_, 4);
v_cache_2242_ = lean_ctor_get(v___x_2235_, 5);
v_recordedDeps_2243_ = lean_ctor_get(v___x_2235_, 6);
v_messages_2244_ = lean_ctor_get(v___x_2235_, 7);
v_snapshotTasks_2245_ = lean_ctor_get(v___x_2235_, 9);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2247_ = v___x_2235_;
v_isShared_2248_ = v_isSharedCheck_2269_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_snapshotTasks_2245_);
lean_inc(v_infoState_2236_);
lean_inc(v_messages_2244_);
lean_inc(v_recordedDeps_2243_);
lean_inc(v_cache_2242_);
lean_inc(v_traceState_2241_);
lean_inc(v_auxDeclNGen_2240_);
lean_inc(v_ngen_2239_);
lean_inc(v_nextMacroScope_2238_);
lean_inc(v_env_2237_);
lean_dec(v___x_2235_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2269_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
uint8_t v_enabled_2249_; lean_object* v_assignment_2250_; lean_object* v_lazyAssignment_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2267_; 
v_enabled_2249_ = lean_ctor_get_uint8(v_infoState_2236_, sizeof(void*)*3);
v_assignment_2250_ = lean_ctor_get(v_infoState_2236_, 0);
v_lazyAssignment_2251_ = lean_ctor_get(v_infoState_2236_, 1);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_infoState_2236_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; 
v_unused_2268_ = lean_ctor_get(v_infoState_2236_, 2);
lean_dec(v_unused_2268_);
v___x_2253_ = v_infoState_2236_;
v_isShared_2254_ = v_isSharedCheck_2267_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_lazyAssignment_2251_);
lean_inc(v_assignment_2250_);
lean_dec(v_infoState_2236_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2267_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = l_Lean_PersistentArray_push___redArg(v_a_2224_, v_a_2231_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 2, v___x_2256_);
v___x_2258_ = v___x_2253_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_assignment_2250_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_lazyAssignment_2251_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v___x_2256_);
lean_ctor_set_uint8(v_reuseFailAlloc_2266_, sizeof(void*)*3, v_enabled_2249_);
v___x_2258_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2260_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 8, v___x_2258_);
v___x_2260_ = v___x_2247_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_env_2237_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_nextMacroScope_2238_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_ngen_2239_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_auxDeclNGen_2240_);
lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_traceState_2241_);
lean_ctor_set(v_reuseFailAlloc_2265_, 5, v_cache_2242_);
lean_ctor_set(v_reuseFailAlloc_2265_, 6, v_recordedDeps_2243_);
lean_ctor_set(v_reuseFailAlloc_2265_, 7, v_messages_2244_);
lean_ctor_set(v_reuseFailAlloc_2265_, 8, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2265_, 9, v_snapshotTasks_2245_);
v___x_2260_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2261_ = lean_st_ref_put(v___y_2217_, v___x_2260_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2255_);
v___x_2263_ = v___x_2233_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2255_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v_a_2224_);
v_a_2271_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2230_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2230_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_2279_, lean_object* v_mkInfoTree_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v_a_2286_, lean_object* v_a_x3f_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0(v___y_2279_, v_mkInfoTree_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v_a_2286_, v_a_x3f_2287_);
lean_dec(v_a_x3f_2287_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2279_);
return v_res_2289_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_unsigned_to_nat(32u);
v___x_2291_ = lean_mk_empty_array_with_capacity(v___x_2290_);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1(void){
_start:
{
size_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2293_ = ((size_t)5ULL);
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2295_ = lean_unsigned_to_nat(32u);
v___x_2296_ = lean_mk_empty_array_with_capacity(v___x_2295_);
v___x_2297_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__0);
v___x_2298_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2296_);
lean_ctor_set(v___x_2298_, 2, v___x_2294_);
lean_ctor_set(v___x_2298_, 3, v___x_2294_);
lean_ctor_set_usize(v___x_2298_, 4, v___x_2293_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg(lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; lean_object* v_infoState_2302_; lean_object* v_trees_2303_; lean_object* v___x_2304_; lean_object* v_infoState_2305_; lean_object* v_env_2306_; lean_object* v_nextMacroScope_2307_; lean_object* v_ngen_2308_; lean_object* v_auxDeclNGen_2309_; lean_object* v_traceState_2310_; lean_object* v_cache_2311_; lean_object* v_recordedDeps_2312_; lean_object* v_messages_2313_; lean_object* v_snapshotTasks_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2335_; 
v___x_2301_ = lean_st_ref_get(v___y_2299_);
v_infoState_2302_ = lean_ctor_get(v___x_2301_, 8);
lean_inc_ref(v_infoState_2302_);
lean_dec(v___x_2301_);
v_trees_2303_ = lean_ctor_get(v_infoState_2302_, 2);
lean_inc_ref(v_trees_2303_);
lean_dec_ref(v_infoState_2302_);
v___x_2304_ = lean_st_ref_take(v___y_2299_);
v_infoState_2305_ = lean_ctor_get(v___x_2304_, 8);
v_env_2306_ = lean_ctor_get(v___x_2304_, 0);
v_nextMacroScope_2307_ = lean_ctor_get(v___x_2304_, 1);
v_ngen_2308_ = lean_ctor_get(v___x_2304_, 2);
v_auxDeclNGen_2309_ = lean_ctor_get(v___x_2304_, 3);
v_traceState_2310_ = lean_ctor_get(v___x_2304_, 4);
v_cache_2311_ = lean_ctor_get(v___x_2304_, 5);
v_recordedDeps_2312_ = lean_ctor_get(v___x_2304_, 6);
v_messages_2313_ = lean_ctor_get(v___x_2304_, 7);
v_snapshotTasks_2314_ = lean_ctor_get(v___x_2304_, 9);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2316_ = v___x_2304_;
v_isShared_2317_ = v_isSharedCheck_2335_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snapshotTasks_2314_);
lean_inc(v_infoState_2305_);
lean_inc(v_messages_2313_);
lean_inc(v_recordedDeps_2312_);
lean_inc(v_cache_2311_);
lean_inc(v_traceState_2310_);
lean_inc(v_auxDeclNGen_2309_);
lean_inc(v_ngen_2308_);
lean_inc(v_nextMacroScope_2307_);
lean_inc(v_env_2306_);
lean_dec(v___x_2304_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2335_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
uint8_t v_enabled_2318_; lean_object* v_assignment_2319_; lean_object* v_lazyAssignment_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2333_; 
v_enabled_2318_ = lean_ctor_get_uint8(v_infoState_2305_, sizeof(void*)*3);
v_assignment_2319_ = lean_ctor_get(v_infoState_2305_, 0);
v_lazyAssignment_2320_ = lean_ctor_get(v_infoState_2305_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_infoState_2305_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v_infoState_2305_, 2);
lean_dec(v_unused_2334_);
v___x_2322_ = v_infoState_2305_;
v_isShared_2323_ = v_isSharedCheck_2333_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_lazyAssignment_2320_);
lean_inc(v_assignment_2319_);
lean_dec(v_infoState_2305_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2333_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2324_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___closed__1);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 2, v___x_2324_);
v___x_2326_ = v___x_2322_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_assignment_2319_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_lazyAssignment_2320_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v___x_2324_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3, v_enabled_2318_);
v___x_2326_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2328_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 8, v___x_2326_);
v___x_2328_ = v___x_2316_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_env_2306_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_nextMacroScope_2307_);
lean_ctor_set(v_reuseFailAlloc_2331_, 2, v_ngen_2308_);
lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_auxDeclNGen_2309_);
lean_ctor_set(v_reuseFailAlloc_2331_, 4, v_traceState_2310_);
lean_ctor_set(v_reuseFailAlloc_2331_, 5, v_cache_2311_);
lean_ctor_set(v_reuseFailAlloc_2331_, 6, v_recordedDeps_2312_);
lean_ctor_set(v_reuseFailAlloc_2331_, 7, v_messages_2313_);
lean_ctor_set(v_reuseFailAlloc_2331_, 8, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2331_, 9, v_snapshotTasks_2314_);
v___x_2328_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = lean_st_ref_put(v___y_2299_, v___x_2328_);
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_trees_2303_);
return v___x_2330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg(v___y_2336_);
lean_dec(v___y_2336_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg(lean_object* v_x_2339_, lean_object* v_mkInfoTree_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
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
v___x_2352_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg(v___y_2346_);
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
v___x_2361_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0(v___y_2346_, v_mkInfoTree_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v_a_2353_, v___x_2360_);
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
v___x_2382_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___lam__0(v___y_2346_, v_mkInfoTree_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v_a_2353_, v___x_2381_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_x_2399_, lean_object* v_mkInfoTree_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg(v_x_2399_, v_mkInfoTree_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg(lean_object* v_stx_2409_, lean_object* v_output_2410_, lean_object* v_x_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___f_2419_; lean_object* v___x_2420_; 
v___f_2419_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2419_, 0, v_stx_2409_);
lean_closure_set(v___f_2419_, 1, v_output_2410_);
v___x_2420_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg(v_x_2411_, v___f_2419_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg___boxed(lean_object* v_stx_2421_, lean_object* v_output_2422_, lean_object* v_x_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg(v_stx_2421_, v_output_2422_, v_x_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(lean_object* v_beforeStx_2452_, lean_object* v_afterStx_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_declName_x3f_2462_; lean_object* v_macroStack_2463_; uint8_t v_mayPostpone_2464_; uint8_t v_errToSorry_2465_; lean_object* v_autoBoundImplicitContext_2466_; lean_object* v_autoBoundImplicitForbidden_2467_; lean_object* v_sectionVars_2468_; lean_object* v_sectionFVars_2469_; uint8_t v_implicitLambda_2470_; uint8_t v_heedElabAsElim_2471_; uint8_t v_isNoncomputableSection_2472_; uint8_t v_isMetaSection_2473_; uint8_t v_ignoreTCFailures_2474_; uint8_t v_inPattern_2475_; lean_object* v_tacSnap_x3f_2476_; uint8_t v_saveRecAppSyntax_2477_; uint8_t v_holesAsSyntheticOpaque_2478_; uint8_t v_checkDeprecated_2479_; lean_object* v_fixedTermElabs_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_declName_x3f_2462_ = lean_ctor_get(v___y_2455_, 0);
v_macroStack_2463_ = lean_ctor_get(v___y_2455_, 1);
v_mayPostpone_2464_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8);
v_errToSorry_2465_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_2466_ = lean_ctor_get(v___y_2455_, 2);
v_autoBoundImplicitForbidden_2467_ = lean_ctor_get(v___y_2455_, 3);
v_sectionVars_2468_ = lean_ctor_get(v___y_2455_, 4);
v_sectionFVars_2469_ = lean_ctor_get(v___y_2455_, 5);
v_implicitLambda_2470_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 2);
v_heedElabAsElim_2471_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_2472_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 4);
v_isMetaSection_2473_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_2474_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 6);
v_inPattern_2475_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_2476_ = lean_ctor_get(v___y_2455_, 6);
v_saveRecAppSyntax_2477_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_2478_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 9);
v_checkDeprecated_2479_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*8 + 10);
v_fixedTermElabs_2480_ = lean_ctor_get(v___y_2455_, 7);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_beforeStx_2452_);
lean_ctor_set(v___x_2481_, 1, v_afterStx_2453_);
lean_inc(v_macroStack_2463_);
v___x_2482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v_macroStack_2463_);
lean_inc_ref(v_fixedTermElabs_2480_);
lean_inc(v_tacSnap_x3f_2476_);
lean_inc(v_sectionFVars_2469_);
lean_inc(v_sectionVars_2468_);
lean_inc_ref(v_autoBoundImplicitForbidden_2467_);
lean_inc(v_autoBoundImplicitContext_2466_);
lean_inc(v_declName_x3f_2462_);
v___x_2483_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_2483_, 0, v_declName_x3f_2462_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
lean_ctor_set(v___x_2483_, 2, v_autoBoundImplicitContext_2466_);
lean_ctor_set(v___x_2483_, 3, v_autoBoundImplicitForbidden_2467_);
lean_ctor_set(v___x_2483_, 4, v_sectionVars_2468_);
lean_ctor_set(v___x_2483_, 5, v_sectionFVars_2469_);
lean_ctor_set(v___x_2483_, 6, v_tacSnap_x3f_2476_);
lean_ctor_set(v___x_2483_, 7, v_fixedTermElabs_2480_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8, v_mayPostpone_2464_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 1, v_errToSorry_2465_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 2, v_implicitLambda_2470_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 3, v_heedElabAsElim_2471_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 4, v_isNoncomputableSection_2472_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 5, v_isMetaSection_2473_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 6, v_ignoreTCFailures_2474_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 7, v_inPattern_2475_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_2477_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_2478_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*8 + 10, v_checkDeprecated_2479_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2459_);
lean_inc(v___y_2458_);
lean_inc_ref(v___y_2457_);
lean_inc(v___y_2456_);
v___x_2484_ = lean_apply_7(v_x_2454_, v___x_2483_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, lean_box(0));
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
uint8_t v___x_89846__boxed_2789_; uint8_t v___x_89848__boxed_2790_; lean_object* v_res_2791_; 
v___x_89846__boxed_2789_ = lean_unbox(v___x_2771_);
v___x_89848__boxed_2790_ = lean_unbox(v___x_2774_);
v_res_2791_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_rhs_2770_, v___x_89846__boxed_2789_, v_config_2772_, v_a_2773_, v___x_89848__boxed_2790_, v___x_2775_, v___x_2776_, v___x_2777_, v___f_2778_, v___x_2779_, v_body_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
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
size_t v_x_90531__boxed_3015_; uint8_t v_res_3016_; lean_object* v_r_3017_; 
v_x_90531__boxed_3015_ = lean_unbox_usize(v_x_3013_);
lean_dec(v_x_3013_);
v_res_3016_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___redArg(v_x_3012_, v_x_90531__boxed_3015_, v_x_3014_);
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3027_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__0);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
return v___x_3031_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__1);
v___x_3033_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
lean_ctor_set(v___x_3033_, 2, v___x_3032_);
lean_ctor_set(v___x_3033_, 3, v___x_3032_);
lean_ctor_set(v___x_3033_, 4, v___x_3032_);
lean_ctor_set(v___x_3033_, 5, v___x_3032_);
lean_ctor_set(v___x_3033_, 6, v___x_3032_);
return v___x_3033_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_3034_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__7));
v___x_3040_ = l_Lean_stringToMessageData(v___x_3039_);
return v___x_3040_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__9));
v___x_3043_ = l_Lean_stringToMessageData(v___x_3042_);
return v___x_3043_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_3045_ = l_Lean_stringToMessageData(v___x_3044_);
return v___x_3045_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v_cls_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_cls_3046_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__6));
v___x_3047_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__1));
v___x_3048_ = l_Lean_Name_append(v___x_3047_, v_cls_3046_);
return v___x_3048_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__13));
v___x_3051_ = l_Lean_stringToMessageData(v___x_3050_);
return v___x_3051_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__15));
v___x_3054_ = l_Lean_stringToMessageData(v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17(lean_object* v_mod_3059_, uint8_t v_isMeta_3060_, lean_object* v_hint_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_env_3104_; uint8_t v_isExporting_3105_; lean_object* v_entry_3106_; lean_object* v___x_3107_; lean_object* v_env_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3102_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__4);
v___x_3103_ = lean_st_ref_get(v___y_3068_);
v_env_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc_ref(v_env_3104_);
lean_dec(v___x_3103_);
v_isExporting_3105_ = lean_ctor_get_uint8(v_env_3104_, sizeof(void*)*13);
lean_dec_ref(v_env_3104_);
lean_inc(v_mod_3059_);
v_entry_3106_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3106_, 0, v_mod_3059_);
lean_ctor_set_uint8(v_entry_3106_, sizeof(void*)*1, v_isExporting_3105_);
lean_ctor_set_uint8(v_entry_3106_, sizeof(void*)*1 + 1, v_isMeta_3060_);
v___x_3107_ = lean_st_ref_get(v___y_3068_);
v_env_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc_ref(v_env_3108_);
lean_dec(v___x_3107_);
v___x_3109_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3110_ = lean_box(1);
v___x_3111_ = lean_box(0);
v___x_3112_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3102_, v___x_3109_, v_env_3108_, v___x_3110_, v___x_3111_);
v___x_3113_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___redArg(v___x_3112_, v_entry_3106_);
lean_dec(v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v_toCold_3114_; lean_object* v_options_3115_; lean_object* v_inheritedTraceOptions_3116_; uint8_t v_hasTrace_3117_; lean_object* v___f_3118_; uint8_t v___x_3119_; lean_object* v___y_3121_; lean_object* v___y_3122_; 
v_toCold_3114_ = lean_ctor_get(v___y_3067_, 0);
v_options_3115_ = lean_ctor_get(v_toCold_3114_, 2);
v_inheritedTraceOptions_3116_ = lean_ctor_get(v_toCold_3114_, 11);
v_hasTrace_3117_ = lean_ctor_get_uint8(v_options_3115_, sizeof(void*)*1);
v___f_3118_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___lam__0), 3, 2);
lean_closure_set(v___f_3118_, 0, v___x_3109_);
lean_closure_set(v___f_3118_, 1, v_entry_3106_);
v___x_3119_ = 1;
if (v_hasTrace_3117_ == 0)
{
lean_dec(v_hint_3061_);
lean_dec(v_mod_3059_);
v___y_3121_ = v___y_3066_;
v___y_3122_ = v___y_3068_;
goto v___jp_3120_;
}
else
{
lean_object* v_cls_3149_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_cls_3149_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__6));
v___x_3169_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__12);
v___x_3170_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3116_, v_options_3115_, v___x_3169_);
if (v___x_3170_ == 0)
{
lean_dec(v_hint_3061_);
lean_dec(v_mod_3059_);
v___y_3121_ = v___y_3066_;
v___y_3122_ = v___y_3068_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3171_; lean_object* v___y_3173_; 
v___x_3171_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__14);
if (v_isExporting_3105_ == 0)
{
lean_object* v___x_3180_; 
v___x_3180_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__19));
v___y_3173_ = v___x_3180_;
goto v___jp_3172_;
}
else
{
lean_object* v___x_3181_; 
v___x_3181_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__20));
v___y_3173_ = v___x_3181_;
goto v___jp_3172_;
}
v___jp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_inc_ref(v___y_3173_);
v___x_3174_ = l_Lean_stringToMessageData(v___y_3173_);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3171_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__16);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
if (v_isMeta_3060_ == 0)
{
lean_object* v___x_3178_; 
v___x_3178_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__17));
v___y_3156_ = v___x_3177_;
v___y_3157_ = v___x_3178_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3179_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__18));
v___y_3156_ = v___x_3177_;
v___y_3157_ = v___x_3179_;
goto v___jp_3155_;
}
}
}
v___jp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___y_3151_);
lean_ctor_set(v___x_3153_, 1, v___y_3152_);
v___x_3154_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_3149_, v___x_3153_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_dec_ref_known(v___x_3154_, 1);
v___y_3121_ = v___y_3066_;
v___y_3122_ = v___y_3068_;
goto v___jp_3120_;
}
else
{
lean_dec_ref(v___f_3118_);
return v___x_3154_;
}
}
v___jp_3155_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; 
lean_inc_ref(v___y_3157_);
v___x_3158_ = l_Lean_stringToMessageData(v___y_3157_);
v___x_3159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___y_3156_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__8);
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = l_Lean_MessageData_ofName(v_mod_3059_);
v___x_3163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = l_Lean_Name_isAnonymous(v_hint_3061_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__10);
v___x_3166_ = l_Lean_MessageData_ofName(v_hint_3061_);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___y_3151_ = v___x_3163_;
v___y_3152_ = v___x_3167_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3168_; 
lean_dec(v_hint_3061_);
v___x_3168_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__11);
v___y_3151_ = v___x_3163_;
v___y_3152_ = v___x_3168_;
goto v___jp_3150_;
}
}
}
v___jp_3120_:
{
lean_object* v___x_3123_; lean_object* v_toEnvExtension_3124_; uint8_t v_logWrites_3125_; 
v___x_3123_ = lean_st_ref_take(v___y_3122_);
v_toEnvExtension_3124_ = lean_ctor_get(v___x_3109_, 0);
v_logWrites_3125_ = lean_ctor_get_uint8(v_toEnvExtension_3124_, sizeof(void*)*6);
if (v_logWrites_3125_ == 0)
{
lean_object* v_env_3126_; lean_object* v_nextMacroScope_3127_; lean_object* v_ngen_3128_; lean_object* v_auxDeclNGen_3129_; lean_object* v_traceState_3130_; lean_object* v_recordedDeps_3131_; lean_object* v_messages_3132_; lean_object* v_infoState_3133_; lean_object* v_snapshotTasks_3134_; lean_object* v_asyncMode_3135_; lean_object* v___x_3136_; 
v_env_3126_ = lean_ctor_get(v___x_3123_, 0);
lean_inc_ref(v_env_3126_);
v_nextMacroScope_3127_ = lean_ctor_get(v___x_3123_, 1);
lean_inc(v_nextMacroScope_3127_);
v_ngen_3128_ = lean_ctor_get(v___x_3123_, 2);
lean_inc_ref(v_ngen_3128_);
v_auxDeclNGen_3129_ = lean_ctor_get(v___x_3123_, 3);
lean_inc_ref(v_auxDeclNGen_3129_);
v_traceState_3130_ = lean_ctor_get(v___x_3123_, 4);
lean_inc_ref(v_traceState_3130_);
v_recordedDeps_3131_ = lean_ctor_get(v___x_3123_, 6);
lean_inc_ref(v_recordedDeps_3131_);
v_messages_3132_ = lean_ctor_get(v___x_3123_, 7);
lean_inc_ref(v_messages_3132_);
v_infoState_3133_ = lean_ctor_get(v___x_3123_, 8);
lean_inc_ref(v_infoState_3133_);
v_snapshotTasks_3134_ = lean_ctor_get(v___x_3123_, 9);
lean_inc_ref(v_snapshotTasks_3134_);
lean_dec(v___x_3123_);
v_asyncMode_3135_ = lean_ctor_get(v_toEnvExtension_3124_, 2);
lean_inc_ref(v_toEnvExtension_3124_);
v___x_3136_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3124_, v_env_3126_, v___f_3118_, v_asyncMode_3135_, v___x_3111_, v___x_3119_);
v___y_3071_ = v___y_3122_;
v___y_3072_ = v_infoState_3133_;
v___y_3073_ = v_nextMacroScope_3127_;
v___y_3074_ = v_recordedDeps_3131_;
v___y_3075_ = v_traceState_3130_;
v___y_3076_ = v_snapshotTasks_3134_;
v___y_3077_ = v_messages_3132_;
v___y_3078_ = v_ngen_3128_;
v___y_3079_ = v_auxDeclNGen_3129_;
v___y_3080_ = v___y_3121_;
v___y_3081_ = v___x_3136_;
goto v___jp_3070_;
}
else
{
lean_object* v_env_3137_; lean_object* v_nextMacroScope_3138_; lean_object* v_ngen_3139_; lean_object* v_auxDeclNGen_3140_; lean_object* v_traceState_3141_; lean_object* v_recordedDeps_3142_; lean_object* v_messages_3143_; lean_object* v_infoState_3144_; lean_object* v_snapshotTasks_3145_; lean_object* v_asyncMode_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_env_3137_ = lean_ctor_get(v___x_3123_, 0);
lean_inc_ref(v_env_3137_);
v_nextMacroScope_3138_ = lean_ctor_get(v___x_3123_, 1);
lean_inc(v_nextMacroScope_3138_);
v_ngen_3139_ = lean_ctor_get(v___x_3123_, 2);
lean_inc_ref(v_ngen_3139_);
v_auxDeclNGen_3140_ = lean_ctor_get(v___x_3123_, 3);
lean_inc_ref(v_auxDeclNGen_3140_);
v_traceState_3141_ = lean_ctor_get(v___x_3123_, 4);
lean_inc_ref(v_traceState_3141_);
v_recordedDeps_3142_ = lean_ctor_get(v___x_3123_, 6);
lean_inc_ref(v_recordedDeps_3142_);
v_messages_3143_ = lean_ctor_get(v___x_3123_, 7);
lean_inc_ref(v_messages_3143_);
v_infoState_3144_ = lean_ctor_get(v___x_3123_, 8);
lean_inc_ref(v_infoState_3144_);
v_snapshotTasks_3145_ = lean_ctor_get(v___x_3123_, 9);
lean_inc_ref(v_snapshotTasks_3145_);
lean_dec(v___x_3123_);
v_asyncMode_3146_ = lean_ctor_get(v_toEnvExtension_3124_, 2);
lean_inc_ref_n(v_toEnvExtension_3124_, 2);
v___x_3147_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3124_, v_env_3137_);
lean_dec_ref(v_env_3137_);
v___x_3148_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3124_, v___x_3147_, v___f_3118_, v_asyncMode_3146_, v___x_3111_, v___x_3119_);
v___y_3071_ = v___y_3122_;
v___y_3072_ = v_infoState_3144_;
v___y_3073_ = v_nextMacroScope_3138_;
v___y_3074_ = v_recordedDeps_3142_;
v___y_3075_ = v_traceState_3141_;
v___y_3076_ = v_snapshotTasks_3145_;
v___y_3077_ = v_messages_3143_;
v___y_3078_ = v_ngen_3139_;
v___y_3079_ = v_auxDeclNGen_3140_;
v___y_3080_ = v___y_3121_;
v___y_3081_ = v___x_3148_;
goto v___jp_3070_;
}
}
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec_ref_known(v_entry_3106_, 1);
lean_dec(v_hint_3061_);
lean_dec(v_mod_3059_);
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
v___jp_3070_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v_mctx_3086_; lean_object* v_zetaDeltaFVarIds_3087_; lean_object* v_postponed_3088_; lean_object* v_diag_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3100_; 
v___x_3082_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__2);
v___x_3083_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3083_, 0, v___y_3081_);
lean_ctor_set(v___x_3083_, 1, v___y_3073_);
lean_ctor_set(v___x_3083_, 2, v___y_3078_);
lean_ctor_set(v___x_3083_, 3, v___y_3079_);
lean_ctor_set(v___x_3083_, 4, v___y_3075_);
lean_ctor_set(v___x_3083_, 5, v___x_3082_);
lean_ctor_set(v___x_3083_, 6, v___y_3074_);
lean_ctor_set(v___x_3083_, 7, v___y_3077_);
lean_ctor_set(v___x_3083_, 8, v___y_3072_);
lean_ctor_set(v___x_3083_, 9, v___y_3076_);
v___x_3084_ = lean_st_ref_put(v___y_3071_, v___x_3083_);
v___x_3085_ = lean_st_ref_take(v___y_3080_);
v_mctx_3086_ = lean_ctor_get(v___x_3085_, 0);
v_zetaDeltaFVarIds_3087_ = lean_ctor_get(v___x_3085_, 2);
v_postponed_3088_ = lean_ctor_get(v___x_3085_, 3);
v_diag_3089_ = lean_ctor_get(v___x_3085_, 4);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; 
v_unused_3101_ = lean_ctor_get(v___x_3085_, 1);
lean_dec(v_unused_3101_);
v___x_3091_ = v___x_3085_;
v_isShared_3092_ = v_isSharedCheck_3100_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_diag_3089_);
lean_inc(v_postponed_3088_);
lean_inc(v_zetaDeltaFVarIds_3087_);
lean_inc(v_mctx_3086_);
lean_dec(v___x_3085_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3100_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___closed__3);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 1, v___x_3094_);
v___x_3096_ = v___x_3091_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_mctx_3086_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_zetaDeltaFVarIds_3087_);
lean_ctor_set(v_reuseFailAlloc_3099_, 3, v_postponed_3088_);
lean_ctor_set(v_reuseFailAlloc_3099_, 4, v_diag_3089_);
v___x_3096_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_st_ref_put(v___y_3080_, v___x_3096_);
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3093_);
return v___x_3098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17___boxed(lean_object* v_mod_3184_, lean_object* v_isMeta_3185_, lean_object* v_hint_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
uint8_t v_isMeta_boxed_3195_; lean_object* v_res_3196_; 
v_isMeta_boxed_3195_ = lean_unbox(v_isMeta_3185_);
v_res_3196_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17(v_mod_3184_, v_isMeta_boxed_3195_, v_hint_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18(lean_object* v___x_3197_, lean_object* v_declName_3198_, lean_object* v_as_3199_, size_t v_sz_3200_, size_t v_i_3201_, lean_object* v_b_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
uint8_t v___x_3211_; 
v___x_3211_ = lean_usize_dec_lt(v_i_3201_, v_sz_3200_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; 
lean_dec(v_declName_3198_);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v_b_3202_);
return v___x_3212_;
}
else
{
lean_object* v___x_3213_; lean_object* v_modules_3214_; lean_object* v___x_3215_; lean_object* v_a_3216_; lean_object* v___x_3217_; lean_object* v_toImport_3218_; lean_object* v_module_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; lean_object* v___x_3222_; 
v___x_3213_ = l_Lean_Environment_header(v___x_3197_);
v_modules_3214_ = lean_ctor_get(v___x_3213_, 3);
lean_inc_ref(v_modules_3214_);
lean_dec_ref(v___x_3213_);
v___x_3215_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3216_ = lean_array_uget_borrowed(v_as_3199_, v_i_3201_);
v___x_3217_ = lean_array_get(v___x_3215_, v_modules_3214_, v_a_3216_);
lean_dec_ref(v_modules_3214_);
v_toImport_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc_ref(v_toImport_3218_);
lean_dec(v___x_3217_);
v_module_3219_ = lean_ctor_get(v_toImport_3218_, 0);
lean_inc(v_module_3219_);
lean_dec_ref(v_toImport_3218_);
v___x_3220_ = lean_box(0);
v___x_3221_ = 0;
lean_inc(v_declName_3198_);
v___x_3222_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17(v_module_3219_, v___x_3221_, v_declName_3198_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3222_) == 0)
{
size_t v___x_3223_; size_t v___x_3224_; 
lean_dec_ref_known(v___x_3222_, 1);
v___x_3223_ = ((size_t)1ULL);
v___x_3224_ = lean_usize_add(v_i_3201_, v___x_3223_);
v_i_3201_ = v___x_3224_;
v_b_3202_ = v___x_3220_;
goto _start;
}
else
{
lean_dec(v_declName_3198_);
return v___x_3222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18___boxed(lean_object* v___x_3226_, lean_object* v_declName_3227_, lean_object* v_as_3228_, lean_object* v_sz_3229_, lean_object* v_i_3230_, lean_object* v_b_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
size_t v_sz_boxed_3240_; size_t v_i_boxed_3241_; lean_object* v_res_3242_; 
v_sz_boxed_3240_ = lean_unbox_usize(v_sz_3229_);
lean_dec(v_sz_3229_);
v_i_boxed_3241_ = lean_unbox_usize(v_i_3230_);
lean_dec(v_i_3230_);
v_res_3242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18(v___x_3226_, v_declName_3227_, v_as_3228_, v_sz_boxed_3240_, v_i_boxed_3241_, v_b_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec_ref(v_as_3228_);
lean_dec_ref(v___x_3226_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24___redArg(lean_object* v_a_3243_, lean_object* v_x_3244_){
_start:
{
if (lean_obj_tag(v_x_3244_) == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_box(0);
return v___x_3245_;
}
else
{
lean_object* v_key_3246_; lean_object* v_value_3247_; lean_object* v_tail_3248_; uint8_t v___x_3249_; 
v_key_3246_ = lean_ctor_get(v_x_3244_, 0);
v_value_3247_ = lean_ctor_get(v_x_3244_, 1);
v_tail_3248_ = lean_ctor_get(v_x_3244_, 2);
v___x_3249_ = lean_name_eq(v_key_3246_, v_a_3243_);
if (v___x_3249_ == 0)
{
v_x_3244_ = v_tail_3248_;
goto _start;
}
else
{
lean_object* v___x_3251_; 
lean_inc(v_value_3247_);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_value_3247_);
return v___x_3251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24___redArg___boxed(lean_object* v_a_3252_, lean_object* v_x_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24___redArg(v_a_3252_, v_x_3253_);
lean_dec(v_x_3253_);
lean_dec(v_a_3252_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg(lean_object* v_m_3255_, lean_object* v_a_3256_){
_start:
{
lean_object* v_buckets_3257_; lean_object* v___x_3258_; uint64_t v___y_3260_; 
v_buckets_3257_ = lean_ctor_get(v_m_3255_, 1);
v___x_3258_ = lean_array_get_size(v_buckets_3257_);
if (lean_obj_tag(v_a_3256_) == 0)
{
uint64_t v___x_3274_; 
v___x_3274_ = 1723ULL;
v___y_3260_ = v___x_3274_;
goto v___jp_3259_;
}
else
{
uint64_t v_hash_3275_; 
v_hash_3275_ = lean_ctor_get_uint64(v_a_3256_, sizeof(void*)*2);
v___y_3260_ = v_hash_3275_;
goto v___jp_3259_;
}
v___jp_3259_:
{
uint64_t v___x_3261_; uint64_t v___x_3262_; uint64_t v_fold_3263_; uint64_t v___x_3264_; uint64_t v___x_3265_; uint64_t v___x_3266_; size_t v___x_3267_; size_t v___x_3268_; size_t v___x_3269_; size_t v___x_3270_; size_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3261_ = 32ULL;
v___x_3262_ = lean_uint64_shift_right(v___y_3260_, v___x_3261_);
v_fold_3263_ = lean_uint64_xor(v___y_3260_, v___x_3262_);
v___x_3264_ = 16ULL;
v___x_3265_ = lean_uint64_shift_right(v_fold_3263_, v___x_3264_);
v___x_3266_ = lean_uint64_xor(v_fold_3263_, v___x_3265_);
v___x_3267_ = lean_uint64_to_usize(v___x_3266_);
v___x_3268_ = lean_usize_of_nat(v___x_3258_);
v___x_3269_ = ((size_t)1ULL);
v___x_3270_ = lean_usize_sub(v___x_3268_, v___x_3269_);
v___x_3271_ = lean_usize_land(v___x_3267_, v___x_3270_);
v___x_3272_ = lean_array_uget_borrowed(v_buckets_3257_, v___x_3271_);
v___x_3273_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24___redArg(v_a_3256_, v___x_3272_);
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg___boxed(lean_object* v_m_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg(v_m_3276_, v_a_3277_);
lean_dec(v_a_3277_);
lean_dec_ref(v_m_3276_);
return v_res_3278_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0(void){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Std_HashMap_instInhabited___redArg();
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(lean_object* v_declName_3282_, uint8_t v_isMeta_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v_env_3297_; lean_object* v___y_3299_; lean_object* v___x_3312_; 
v___x_3292_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__0);
v___x_3293_ = lean_st_ref_get(v___y_3290_);
v_env_3297_ = lean_ctor_get(v___x_3293_, 0);
lean_inc_ref(v_env_3297_);
lean_dec(v___x_3293_);
v___x_3312_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3297_, v_declName_3282_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref(v_env_3297_);
lean_dec(v_declName_3282_);
goto v___jp_3294_;
}
else
{
lean_object* v_val_3313_; lean_object* v___x_3314_; lean_object* v_modules_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v_val_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_val_3313_);
lean_dec_ref_known(v___x_3312_, 1);
v___x_3314_ = l_Lean_Environment_header(v_env_3297_);
v_modules_3315_ = lean_ctor_get(v___x_3314_, 3);
lean_inc_ref(v_modules_3315_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = lean_array_get_size(v_modules_3315_);
v___x_3317_ = lean_nat_dec_lt(v_val_3313_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_dec_ref(v_modules_3315_);
lean_dec(v_val_3313_);
lean_dec_ref(v_env_3297_);
lean_dec(v_declName_3282_);
goto v___jp_3294_;
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___y_3321_; 
v___x_3318_ = lean_array_fget(v_modules_3315_, v_val_3313_);
lean_dec(v_val_3313_);
lean_dec_ref(v_modules_3315_);
v___x_3319_ = lean_st_ref_get(v___y_3290_);
if (v_isMeta_3283_ == 0)
{
lean_dec(v___x_3319_);
v___y_3321_ = v_isMeta_3283_;
goto v___jp_3320_;
}
else
{
lean_object* v_env_3332_; uint8_t v___x_3333_; 
v_env_3332_ = lean_ctor_get(v___x_3319_, 0);
lean_inc_ref(v_env_3332_);
lean_dec(v___x_3319_);
lean_inc(v_declName_3282_);
v___x_3333_ = l_Lean_isMarkedMeta(v_env_3332_, v_declName_3282_);
if (v___x_3333_ == 0)
{
v___y_3321_ = v_isMeta_3283_;
goto v___jp_3320_;
}
else
{
uint8_t v___x_3334_; 
v___x_3334_ = 0;
v___y_3321_ = v___x_3334_;
goto v___jp_3320_;
}
}
v___jp_3320_:
{
lean_object* v_toImport_3322_; lean_object* v_module_3323_; lean_object* v___x_3324_; 
v_toImport_3322_ = lean_ctor_get(v___x_3318_, 0);
lean_inc_ref(v_toImport_3322_);
lean_dec(v___x_3318_);
v_module_3323_ = lean_ctor_get(v_toImport_3322_, 0);
lean_inc(v_module_3323_);
lean_dec_ref(v_toImport_3322_);
lean_inc(v_declName_3282_);
v___x_3324_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17(v_module_3323_, v___y_3321_, v_declName_3282_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec_ref_known(v___x_3324_, 1);
v___x_3325_ = l_Lean_indirectModUseExt;
v___x_3326_ = lean_box(1);
v___x_3327_ = lean_box(0);
lean_inc_ref(v_env_3297_);
v___x_3328_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3292_, v___x_3325_, v_env_3297_, v___x_3326_, v___x_3327_);
v___x_3329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg(v___x_3328_, v_declName_3282_);
lean_dec(v___x_3328_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v___x_3330_; 
v___x_3330_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___closed__1));
v___y_3299_ = v___x_3330_;
goto v___jp_3298_;
}
else
{
lean_object* v_val_3331_; 
v_val_3331_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v___x_3329_, 1);
v___y_3299_ = v_val_3331_;
goto v___jp_3298_;
}
}
else
{
lean_dec_ref(v_env_3297_);
lean_dec(v_declName_3282_);
return v___x_3324_;
}
}
}
}
v___jp_3294_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
return v___x_3296_;
}
v___jp_3298_:
{
lean_object* v___x_3300_; size_t v_sz_3301_; size_t v___x_3302_; lean_object* v___x_3303_; 
v___x_3300_ = lean_box(0);
v_sz_3301_ = lean_array_size(v___y_3299_);
v___x_3302_ = ((size_t)0ULL);
v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__18(v_env_3297_, v_declName_3282_, v___y_3299_, v_sz_3301_, v___x_3302_, v___x_3300_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
lean_dec_ref(v___y_3299_);
lean_dec_ref(v_env_3297_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3310_ == 0)
{
lean_object* v_unused_3311_; 
v_unused_3311_ = lean_ctor_get(v___x_3303_, 0);
lean_dec(v_unused_3311_);
v___x_3305_ = v___x_3303_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_dec(v___x_3303_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v___x_3300_);
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3300_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
else
{
return v___x_3303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___boxed(lean_object* v_declName_3335_, lean_object* v_isMeta_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
uint8_t v_isMeta_boxed_3345_; lean_object* v_res_3346_; 
v_isMeta_boxed_3345_ = lean_unbox(v_isMeta_3336_);
v_res_3346_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(v_declName_3335_, v_isMeta_boxed_3345_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec_ref(v___y_3337_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg(lean_object* v_as_x27_3347_, lean_object* v_b_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
if (lean_obj_tag(v_as_x27_3347_) == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_b_3348_);
return v___x_3357_;
}
else
{
lean_object* v_head_3358_; lean_object* v_tail_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; 
v_head_3358_ = lean_ctor_get(v_as_x27_3347_, 0);
v_tail_3359_ = lean_ctor_get(v_as_x27_3347_, 1);
v___x_3360_ = lean_box(0);
v___x_3361_ = 1;
lean_inc(v_head_3358_);
v___x_3362_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(v_head_3358_, v___x_3361_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_dec_ref_known(v___x_3362_, 1);
v_as_x27_3347_ = v_tail_3359_;
v_b_3348_ = v___x_3360_;
goto _start;
}
else
{
return v___x_3362_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg___boxed(lean_object* v_as_x27_3364_, lean_object* v_b_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg(v_as_x27_3364_, v_b_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v_as_x27_3364_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(lean_object* v_env_3375_, lean_object* v___x_3376_, lean_object* v_currNamespace_3377_, lean_object* v_openDecls_3378_, lean_object* v_n_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = l_Lean_ResolveName_resolveGlobalName(v_env_3375_, v___x_3376_, v_currNamespace_3377_, v_openDecls_3378_, v_n_3379_);
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
lean_ctor_set(v___x_3383_, 1, v___y_3381_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed(lean_object* v_env_3384_, lean_object* v___x_3385_, lean_object* v_currNamespace_3386_, lean_object* v_openDecls_3387_, lean_object* v_n_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(v_env_3384_, v___x_3385_, v_currNamespace_3386_, v_openDecls_3387_, v_n_3388_, v___y_3389_, v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec_ref(v___x_3385_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(lean_object* v_x_3392_, lean_object* v___y_3393_){
_start:
{
if (lean_obj_tag(v_x_3392_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3395_; 
v_a_3394_ = lean_ctor_get(v_x_3392_, 0);
lean_inc(v_a_3394_);
v___x_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3395_, 0, v_a_3394_);
lean_ctor_set(v___x_3395_, 1, v___y_3393_);
return v___x_3395_;
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3397_; 
v_a_3396_ = lean_ctor_get(v_x_3392_, 0);
lean_inc(v_a_3396_);
v___x_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3397_, 0, v_a_3396_);
lean_ctor_set(v___x_3397_, 1, v___y_3393_);
return v___x_3397_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg___boxed(lean_object* v_x_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(v_x_3398_, v___y_3399_);
lean_dec_ref(v_x_3398_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(lean_object* v_env_3401_, lean_object* v_stx_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_3401_, v_stx_3402_, v___y_3403_, v___y_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
if (lean_obj_tag(v_a_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3415_; 
v_a_3407_ = lean_ctor_get(v___x_3405_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v___x_3405_, 0);
lean_dec(v_unused_3416_);
v___x_3409_ = v___x_3405_;
v_isShared_3410_ = v_isSharedCheck_3415_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3405_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3415_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3413_; 
v___x_3411_ = lean_box(0);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3411_);
v___x_3413_ = v___x_3409_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_a_3407_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
else
{
lean_object* v_val_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3445_; 
v_val_3417_ = lean_ctor_get(v_a_3406_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_a_3406_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3419_ = v_a_3406_;
v_isShared_3420_ = v_isSharedCheck_3445_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_val_3417_);
lean_dec(v_a_3406_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3445_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_snd_3421_; 
v_snd_3421_ = lean_ctor_get(v_val_3417_, 1);
lean_inc(v_snd_3421_);
lean_dec(v_val_3417_);
if (lean_obj_tag(v_snd_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3431_; 
lean_del_object(v___x_3419_);
v_a_3422_ = lean_ctor_get(v___x_3405_, 1);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3405_, 2);
v_a_3423_ = lean_ctor_get(v_snd_3421_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_snd_3421_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3425_ = v_snd_3421_;
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v_snd_3421_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(v___x_3428_, v_a_3422_);
lean_dec_ref(v___x_3428_);
return v___x_3429_;
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3444_; 
v_a_3432_ = lean_ctor_get(v___x_3405_, 1);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3405_, 2);
v_a_3433_ = lean_ctor_get(v_snd_3421_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_snd_3421_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3435_ = v_snd_3421_;
v_isShared_3436_ = v_isSharedCheck_3444_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v_snd_3421_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3444_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v_a_3433_);
v___x_3438_ = v___x_3419_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3440_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3438_);
v___x_3440_ = v___x_3435_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(v___x_3440_, v_a_3432_);
lean_dec_ref(v___x_3440_);
return v___x_3441_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
v_a_3446_ = lean_ctor_get(v___x_3405_, 0);
v_a_3447_ = lean_ctor_get(v___x_3405_, 1);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3405_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_inc(v_a_3446_);
lean_dec(v___x_3405_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3446_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed(lean_object* v_env_3455_, lean_object* v_stx_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(v_env_3455_, v_stx_3456_, v___y_3457_, v___y_3458_);
lean_dec_ref(v___y_3457_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_x_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v___x_3470_; lean_object* v_toCold_3471_; lean_object* v_env_3472_; lean_object* v_currRecDepth_3473_; lean_object* v_ref_3474_; lean_object* v_maxRecDepth_3475_; lean_object* v_currNamespace_3476_; lean_object* v_openDecls_3477_; lean_object* v_quotContext_3478_; lean_object* v_currMacroScope_3479_; lean_object* v___f_3480_; lean_object* v___f_3481_; lean_object* v___x_3482_; lean_object* v___f_3483_; lean_object* v___f_3484_; lean_object* v___f_3485_; lean_object* v_methods_3486_; lean_object* v___x_3487_; lean_object* v_nextMacroScope_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3470_ = lean_st_ref_get(v___y_3468_);
v_toCold_3471_ = lean_ctor_get(v___y_3467_, 0);
v_env_3472_ = lean_ctor_get(v___x_3470_, 0);
lean_inc_ref_n(v_env_3472_, 4);
lean_dec(v___x_3470_);
v_currRecDepth_3473_ = lean_ctor_get(v___y_3467_, 1);
v_ref_3474_ = lean_ctor_get(v___y_3467_, 2);
v_maxRecDepth_3475_ = lean_ctor_get(v_toCold_3471_, 3);
v_currNamespace_3476_ = lean_ctor_get(v_toCold_3471_, 4);
v_openDecls_3477_ = lean_ctor_get(v_toCold_3471_, 5);
v_quotContext_3478_ = lean_ctor_get(v_toCold_3471_, 8);
v_currMacroScope_3479_ = lean_ctor_get(v_toCold_3471_, 9);
v___f_3480_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3480_, 0, v_env_3472_);
v___f_3481_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3481_, 0, v_env_3472_);
v___x_3482_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3467_);
lean_inc_n(v_currNamespace_3476_, 3);
v___f_3483_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3483_, 0, v_currNamespace_3476_);
lean_inc_n(v_openDecls_3477_, 2);
v___f_3484_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_3484_, 0, v_env_3472_);
lean_closure_set(v___f_3484_, 1, v___x_3482_);
lean_closure_set(v___f_3484_, 2, v_currNamespace_3476_);
lean_closure_set(v___f_3484_, 3, v_openDecls_3477_);
v___f_3485_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_3485_, 0, v_env_3472_);
lean_closure_set(v___f_3485_, 1, v_currNamespace_3476_);
lean_closure_set(v___f_3485_, 2, v_openDecls_3477_);
v_methods_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3486_, 0, v___f_3481_);
lean_ctor_set(v_methods_3486_, 1, v___f_3483_);
lean_ctor_set(v_methods_3486_, 2, v___f_3480_);
lean_ctor_set(v_methods_3486_, 3, v___f_3485_);
lean_ctor_set(v_methods_3486_, 4, v___f_3484_);
v___x_3487_ = lean_st_ref_get(v___y_3468_);
v_nextMacroScope_3488_ = lean_ctor_get(v___x_3487_, 1);
lean_inc(v_nextMacroScope_3488_);
lean_dec(v___x_3487_);
lean_inc(v_ref_3474_);
lean_inc(v_maxRecDepth_3475_);
lean_inc(v_currRecDepth_3473_);
lean_inc(v_currMacroScope_3479_);
lean_inc(v_quotContext_3478_);
v___x_3489_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3489_, 0, v_methods_3486_);
lean_ctor_set(v___x_3489_, 1, v_quotContext_3478_);
lean_ctor_set(v___x_3489_, 2, v_currMacroScope_3479_);
lean_ctor_set(v___x_3489_, 3, v_currRecDepth_3473_);
lean_ctor_set(v___x_3489_, 4, v_maxRecDepth_3475_);
lean_ctor_set(v___x_3489_, 5, v_ref_3474_);
v___x_3490_ = lean_box(0);
v___x_3491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3491_, 0, v_nextMacroScope_3488_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
lean_ctor_set(v___x_3491_, 2, v___x_3490_);
v___x_3492_ = lean_apply_2(v_x_3461_, v___x_3489_, v___x_3491_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v_a_3494_; lean_object* v_macroScope_3495_; lean_object* v_traceMsgs_3496_; lean_object* v_expandedMacroDecls_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 1);
lean_inc(v_a_3493_);
v_a_3494_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3492_, 2);
v_macroScope_3495_ = lean_ctor_get(v_a_3493_, 0);
lean_inc(v_macroScope_3495_);
v_traceMsgs_3496_ = lean_ctor_get(v_a_3493_, 1);
lean_inc(v_traceMsgs_3496_);
v_expandedMacroDecls_3497_ = lean_ctor_get(v_a_3493_, 2);
lean_inc(v_expandedMacroDecls_3497_);
lean_dec(v_a_3493_);
v___x_3498_ = lean_box(0);
v___x_3499_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg(v_expandedMacroDecls_3497_, v___x_3498_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v_expandedMacroDecls_3497_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v___x_3500_; lean_object* v_env_3501_; lean_object* v_ngen_3502_; lean_object* v_auxDeclNGen_3503_; lean_object* v_traceState_3504_; lean_object* v_cache_3505_; lean_object* v_recordedDeps_3506_; lean_object* v_messages_3507_; lean_object* v_infoState_3508_; lean_object* v_snapshotTasks_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3535_; 
lean_dec_ref_known(v___x_3499_, 1);
v___x_3500_ = lean_st_ref_take(v___y_3468_);
v_env_3501_ = lean_ctor_get(v___x_3500_, 0);
v_ngen_3502_ = lean_ctor_get(v___x_3500_, 2);
v_auxDeclNGen_3503_ = lean_ctor_get(v___x_3500_, 3);
v_traceState_3504_ = lean_ctor_get(v___x_3500_, 4);
v_cache_3505_ = lean_ctor_get(v___x_3500_, 5);
v_recordedDeps_3506_ = lean_ctor_get(v___x_3500_, 6);
v_messages_3507_ = lean_ctor_get(v___x_3500_, 7);
v_infoState_3508_ = lean_ctor_get(v___x_3500_, 8);
v_snapshotTasks_3509_ = lean_ctor_get(v___x_3500_, 9);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3535_ == 0)
{
lean_object* v_unused_3536_; 
v_unused_3536_ = lean_ctor_get(v___x_3500_, 1);
lean_dec(v_unused_3536_);
v___x_3511_ = v___x_3500_;
v_isShared_3512_ = v_isSharedCheck_3535_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_snapshotTasks_3509_);
lean_inc(v_infoState_3508_);
lean_inc(v_messages_3507_);
lean_inc(v_recordedDeps_3506_);
lean_inc(v_cache_3505_);
lean_inc(v_traceState_3504_);
lean_inc(v_auxDeclNGen_3503_);
lean_inc(v_ngen_3502_);
lean_inc(v_env_3501_);
lean_dec(v___x_3500_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3535_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v_macroScope_3495_);
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_env_3501_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_macroScope_3495_);
lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_ngen_3502_);
lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_auxDeclNGen_3503_);
lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_traceState_3504_);
lean_ctor_set(v_reuseFailAlloc_3534_, 5, v_cache_3505_);
lean_ctor_set(v_reuseFailAlloc_3534_, 6, v_recordedDeps_3506_);
lean_ctor_set(v_reuseFailAlloc_3534_, 7, v_messages_3507_);
lean_ctor_set(v_reuseFailAlloc_3534_, 8, v_infoState_3508_);
lean_ctor_set(v_reuseFailAlloc_3534_, 9, v_snapshotTasks_3509_);
v___x_3514_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_st_ref_put(v___y_3468_, v___x_3514_);
v___x_3516_ = l_List_reverse___redArg(v_traceMsgs_3496_);
v___x_3517_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(v___x_3516_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3524_ == 0)
{
lean_object* v_unused_3525_; 
v_unused_3525_ = lean_ctor_get(v___x_3517_, 0);
lean_dec(v_unused_3525_);
v___x_3519_ = v___x_3517_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_dec(v___x_3517_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v_a_3494_);
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3494_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v_a_3494_);
v_a_3526_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3517_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3517_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec(v_traceMsgs_3496_);
lean_dec(v_macroScope_3495_);
lean_dec(v_a_3494_);
v_a_3537_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3499_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3499_);
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
lean_object* v_a_3545_; 
v_a_3545_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3492_, 2);
if (lean_obj_tag(v_a_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v_a_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v_a_3546_ = lean_ctor_get(v_a_3545_, 0);
lean_inc(v_a_3546_);
v_a_3547_ = lean_ctor_get(v_a_3545_, 1);
lean_inc_ref(v_a_3547_);
lean_dec_ref_known(v_a_3545_, 2);
v___x_3548_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___closed__0));
v___x_3549_ = lean_string_dec_eq(v_a_3547_, v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_a_3547_);
v___x_3551_ = l_Lean_MessageData_ofFormat(v___x_3550_);
v___x_3552_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_a_3546_, v___x_3551_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v_a_3546_);
return v___x_3552_;
}
else
{
lean_object* v___x_3553_; 
lean_dec_ref(v_a_3547_);
v___x_3553_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg(v_a_3546_);
return v___x_3553_;
}
}
else
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_x_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3556_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(lean_object* v___x_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v_toCold_3569_; lean_object* v_quotContext_3570_; lean_object* v_currMacroScope_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_toCold_3569_ = lean_ctor_get(v___y_3566_, 0);
lean_inc_ref(v_toCold_3569_);
lean_dec_ref(v___y_3566_);
v_quotContext_3570_ = lean_ctor_get(v_toCold_3569_, 8);
lean_inc(v_quotContext_3570_);
v_currMacroScope_3571_ = lean_ctor_get(v_toCold_3569_, 9);
lean_inc(v_currMacroScope_3571_);
lean_dec_ref(v_toCold_3569_);
v___x_3572_ = l_Lean_addMacroScope(v_quotContext_3570_, v___x_3565_, v_currMacroScope_3571_);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v___x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(v___x_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___f_3587_; lean_object* v___x_3588_; 
v___f_3587_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__2));
v___x_3588_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3587_, v___y_3584_, v___y_3585_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___boxed(lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_ref_3593_, uint8_t v_canonical_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3612_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3606_ = v___x_3603_;
v_isShared_3607_ = v_isSharedCheck_3612_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3603_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3612_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = l_Lean_mkIdentFrom(v_ref_3593_, v_a_3604_, v_canonical_3594_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v___x_3608_);
v___x_3610_ = v___x_3606_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
v_a_3613_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3603_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3603_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_ref_3621_, lean_object* v_canonical_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
uint8_t v_canonical_boxed_3631_; lean_object* v_res_3632_; 
v_canonical_boxed_3631_ = lean_unbox(v_canonical_3622_);
v_res_3632_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_ref_3621_, v_canonical_boxed_3631_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v_ref_3621_);
return v_res_3632_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__0));
v___x_3635_ = l_Lean_stringToMessageData(v___x_3634_);
return v___x_3635_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3642_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___closed__1));
v___x_3643_ = l_Lean_Name_append(v___x_3642_, v___x_3641_);
return v___x_3643_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3646_ = l_Lean_stringToMessageData(v___x_3645_);
return v___x_3646_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3649_ = l_Lean_stringToMessageData(v___x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3656_, lean_object* v_letOrReassign_3657_, lean_object* v_decl_3658_, lean_object* v_tk_3659_, lean_object* v_dec_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3656_, v_letOrReassign_3657_, v_decl_3658_, v_tk_3659_, v_dec_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
lean_dec(v_a_3667_);
lean_dec_ref(v_a_3666_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec_ref(v_a_3661_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3670_, lean_object* v_letOrReassign_3671_, lean_object* v_decl_3672_, lean_object* v_tk_3673_, lean_object* v_dec_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_config_3670_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v___x_3684_; 
lean_dec_ref_known(v___x_3683_, 1);
lean_inc(v_decl_3672_);
v___x_3684_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3672_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3686_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___x_3684_, 1);
v___x_3686_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3671_, v_a_3685_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v___x_3687_; 
lean_dec_ref_known(v___x_3686_, 1);
v___x_3687_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3674_, v_tk_3673_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___y_3690_; uint8_t v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; uint8_t v___y_3697_; lean_object* v___y_3698_; lean_object* v_rhs_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3718_; uint8_t v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; uint8_t v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; uint8_t v___y_3729_; lean_object* v___y_3730_; lean_object* v_xType_x3f_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; uint8_t v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; uint8_t v___y_3790_; uint8_t v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; uint8_t v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; uint8_t v___y_3805_; uint8_t v___y_3864_; lean_object* v___y_3865_; uint8_t v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; uint8_t v___y_3870_; uint8_t v___y_3871_; lean_object* v_id_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v_decl_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___x_3976_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___x_3976_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_3671_, v_a_3685_, v_a_3675_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3671_, v_decl_3672_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3978_) == 0)
{
uint8_t v___x_3979_; 
v___x_3979_ = lean_unbox(v_a_3977_);
lean_dec(v_a_3977_);
if (v___x_3979_ == 0)
{
lean_object* v_a_3980_; 
v_a_3980_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3978_, 1);
v_decl_3891_ = v_a_3980_;
v___y_3892_ = v_a_3675_;
v___y_3893_ = v_a_3676_;
v___y_3894_ = v_a_3677_;
v___y_3895_ = v_a_3678_;
v___y_3896_ = v_a_3679_;
v___y_3897_ = v_a_3680_;
v___y_3898_ = v_a_3681_;
goto v___jp_3890_;
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3982_; 
v_a_3981_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v___x_3978_, 1);
v___x_3982_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(v_a_3981_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref_known(v___x_3982_, 1);
v_decl_3891_ = v_a_3983_;
v___y_3892_ = v_a_3675_;
v___y_3893_ = v_a_3676_;
v___y_3894_ = v_a_3677_;
v___y_3895_ = v_a_3678_;
v___y_3896_ = v_a_3679_;
v___y_3897_ = v_a_3680_;
v___y_3898_ = v_a_3681_;
goto v___jp_3890_;
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_tk_3673_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v_a_3984_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3982_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3982_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec(v_a_3977_);
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_tk_3673_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v_a_3992_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3978_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3978_);
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
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_tk_3673_);
lean_dec(v_decl_3672_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v_a_4000_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3976_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3976_);
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
v___jp_3689_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___f_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3707_ = lean_box(v___y_3697_);
v___x_3708_ = lean_box(v___y_3691_);
lean_inc_ref(v___y_3692_);
lean_inc_ref(v___y_3690_);
lean_inc_ref(v___y_3695_);
v___f_3709_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 19, 10);
lean_closure_set(v___f_3709_, 0, v_rhs_3699_);
lean_closure_set(v___f_3709_, 1, v___x_3707_);
lean_closure_set(v___f_3709_, 2, v_config_3670_);
lean_closure_set(v___f_3709_, 3, v___y_3693_);
lean_closure_set(v___f_3709_, 4, v___x_3708_);
lean_closure_set(v___f_3709_, 5, v___y_3695_);
lean_closure_set(v___f_3709_, 6, v___y_3690_);
lean_closure_set(v___f_3709_, 7, v___y_3692_);
lean_closure_set(v___f_3709_, 8, v___y_3694_);
lean_closure_set(v___f_3709_, 9, v___y_3696_);
v___x_3710_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3710_, 0, v_a_3688_);
v___x_3711_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3711_, 0, v_letOrReassign_3671_);
lean_closure_set(v___x_3711_, 1, v_a_3685_);
lean_closure_set(v___x_3711_, 2, v___x_3710_);
v___x_3712_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1);
v___x_3713_ = l_Lean_MessageData_ofSyntax(v___y_3698_);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_box(0);
v___x_3716_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3714_, v___x_3711_, v___f_3709_, v___x_3715_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3716_;
}
v___jp_3717_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_unsigned_to_nat(4u);
v___x_3740_ = l_Lean_Syntax_getArg(v___y_3730_, v___x_3739_);
lean_dec(v___y_3730_);
if (lean_obj_tag(v_xType_x3f_3731_) == 0)
{
lean_inc(v___y_3724_);
v___y_3690_ = v___y_3718_;
v___y_3691_ = v___y_3719_;
v___y_3692_ = v___y_3721_;
v___y_3693_ = v___y_3720_;
v___y_3694_ = v___y_3722_;
v___y_3695_ = v___y_3723_;
v___y_3696_ = v___y_3724_;
v___y_3697_ = v___y_3725_;
v___y_3698_ = v___y_3724_;
v_rhs_3699_ = v___x_3740_;
v___y_3700_ = v___y_3732_;
v___y_3701_ = v___y_3733_;
v___y_3702_ = v___y_3734_;
v___y_3703_ = v___y_3735_;
v___y_3704_ = v___y_3736_;
v___y_3705_ = v___y_3737_;
v___y_3706_ = v___y_3738_;
goto v___jp_3689_;
}
else
{
lean_object* v_toCold_3741_; lean_object* v_val_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3785_; 
v_toCold_3741_ = lean_ctor_get(v___y_3737_, 0);
v_val_3742_ = lean_ctor_get(v_xType_x3f_3731_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_xType_x3f_3731_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3744_ = v_xType_x3f_3731_;
v_isShared_3745_ = v_isSharedCheck_3785_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_val_3742_);
lean_dec(v_xType_x3f_3731_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3785_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v_ref_3746_; lean_object* v_quotContext_3747_; lean_object* v_currMacroScope_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3764_; 
v_ref_3746_ = lean_ctor_get(v___y_3737_, 2);
v_quotContext_3747_ = lean_ctor_get(v_toCold_3741_, 8);
v_currMacroScope_3748_ = lean_ctor_get(v_toCold_3741_, 9);
v___x_3749_ = l_Lean_SourceInfo_fromRef(v_ref_3746_, v___y_3729_);
v___x_3750_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__15));
lean_inc_ref_n(v___y_3727_, 2);
lean_inc_ref_n(v___y_3726_, 2);
lean_inc_ref_n(v___y_3728_, 3);
v___x_3751_ = l_Lean_Name_mkStr4(v___y_3728_, v___y_3726_, v___y_3727_, v___x_3750_);
v___x_3752_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__17));
v___x_3753_ = l_Lean_Name_mkStr4(v___y_3728_, v___y_3726_, v___y_3727_, v___x_3752_);
v___x_3754_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_3749_);
v___x_3755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3749_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3757_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3758_ = lean_box(0);
lean_inc(v_currMacroScope_3748_);
lean_inc(v_quotContext_3747_);
v___x_3759_ = l_Lean_addMacroScope(v_quotContext_3747_, v___x_3758_, v_currMacroScope_3748_);
v___x_3760_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24));
v___x_3761_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25));
v___x_3762_ = l_Lean_Name_mkStr3(v___y_3728_, v___x_3760_, v___x_3761_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set_tag(v___x_3744_, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3762_);
v___x_3764_ = v___x_3744_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3765_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__28));
lean_inc_ref_n(v___y_3728_, 2);
v___x_3766_ = l_Lean_Name_mkStr2(v___y_3728_, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
lean_inc_ref(v___y_3727_);
lean_inc_ref(v___y_3726_);
v___x_3768_ = l_Lean_Name_mkStr3(v___y_3728_, v___y_3726_, v___y_3727_);
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
v___x_3770_ = lean_box(0);
v___x_3771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3767_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3764_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
lean_inc_n(v___x_3749_, 6);
v___x_3774_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3749_);
lean_ctor_set(v___x_3774_, 1, v___x_3757_);
lean_ctor_set(v___x_3774_, 2, v___x_3759_);
lean_ctor_set(v___x_3774_, 3, v___x_3773_);
v___x_3775_ = l_Lean_Syntax_node1(v___x_3749_, v___x_3756_, v___x_3774_);
v___x_3776_ = l_Lean_Syntax_node2(v___x_3749_, v___x_3753_, v___x_3755_, v___x_3775_);
v___x_3777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3749_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3780_ = l_Lean_Syntax_node1(v___x_3749_, v___x_3779_, v_val_3742_);
v___x_3781_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3749_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = l_Lean_Syntax_node5(v___x_3749_, v___x_3751_, v___x_3776_, v___x_3740_, v___x_3778_, v___x_3780_, v___x_3782_);
lean_inc(v___y_3724_);
v___y_3690_ = v___y_3718_;
v___y_3691_ = v___y_3719_;
v___y_3692_ = v___y_3721_;
v___y_3693_ = v___y_3720_;
v___y_3694_ = v___y_3722_;
v___y_3695_ = v___y_3723_;
v___y_3696_ = v___y_3724_;
v___y_3697_ = v___y_3725_;
v___y_3698_ = v___y_3724_;
v_rhs_3699_ = v___x_3783_;
v___y_3700_ = v___y_3732_;
v___y_3701_ = v___y_3733_;
v___y_3702_ = v___y_3734_;
v___y_3703_ = v___y_3735_;
v___y_3704_ = v___y_3736_;
v___y_3705_ = v___y_3737_;
v___y_3706_ = v___y_3738_;
goto v___jp_3689_;
}
}
}
}
v___jp_3786_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___f_3809_; lean_object* v___x_3810_; 
v___x_3806_ = lean_box(v___y_3787_);
v___x_3807_ = lean_box(v___y_3790_);
v___x_3808_ = lean_box(v___y_3805_);
v___f_3809_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3809_, 0, v___y_3792_);
lean_closure_set(v___f_3809_, 1, v___y_3795_);
lean_closure_set(v___f_3809_, 2, v___x_3806_);
lean_closure_set(v___f_3809_, 3, v___x_3807_);
lean_closure_set(v___f_3809_, 4, v___y_3788_);
lean_closure_set(v___f_3809_, 5, v___x_3808_);
v___x_3810_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___y_3803_, v___f_3809_, v___y_3796_, v___y_3800_, v___y_3799_, v___y_3802_, v___y_3798_, v___y_3804_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v_toCold_3812_; lean_object* v_options_3813_; lean_object* v_fst_3814_; lean_object* v_snd_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3854_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3811_);
lean_dec_ref_known(v___x_3810_, 1);
v_toCold_3812_ = lean_ctor_get(v___y_3798_, 0);
v_options_3813_ = lean_ctor_get(v_toCold_3812_, 2);
v_fst_3814_ = lean_ctor_get(v_a_3811_, 0);
v_snd_3815_ = lean_ctor_get(v_a_3811_, 1);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_a_3811_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3817_ = v_a_3811_;
v_isShared_3818_ = v_isSharedCheck_3854_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_snd_3815_);
lean_inc(v_fst_3814_);
lean_dec(v_a_3811_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3854_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v_inheritedTraceOptions_3819_; uint8_t v_hasTrace_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___f_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v_inheritedTraceOptions_3819_ = lean_ctor_get(v_toCold_3812_, 11);
v_hasTrace_3820_ = lean_ctor_get_uint8(v_options_3813_, sizeof(void*)*1);
v___x_3821_ = lean_box(v___y_3791_);
v___x_3822_ = lean_box(v___y_3794_);
v___x_3823_ = lean_box(v___y_3805_);
v___x_3824_ = lean_box(v___y_3787_);
lean_inc(v_snd_3815_);
v___f_3825_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 19, 10);
lean_closure_set(v___f_3825_, 0, v___y_3789_);
lean_closure_set(v___f_3825_, 1, v___y_3793_);
lean_closure_set(v___f_3825_, 2, v_a_3688_);
lean_closure_set(v___f_3825_, 3, v_letOrReassign_3671_);
lean_closure_set(v___f_3825_, 4, v_a_3685_);
lean_closure_set(v___f_3825_, 5, v___x_3821_);
lean_closure_set(v___f_3825_, 6, v___x_3822_);
lean_closure_set(v___f_3825_, 7, v_snd_3815_);
lean_closure_set(v___f_3825_, 8, v___x_3823_);
lean_closure_set(v___f_3825_, 9, v___x_3824_);
v___x_3826_ = l_Lean_Syntax_getId(v___y_3797_);
lean_dec(v___y_3797_);
v___x_3827_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3826_);
if (v_hasTrace_3820_ == 0)
{
lean_object* v___x_3828_; 
lean_del_object(v___x_3817_);
v___x_3828_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3826_, v_fst_3814_, v_snd_3815_, v___f_3825_, v___y_3805_, v___x_3827_, v___y_3801_, v___y_3796_, v___y_3800_, v___y_3799_, v___y_3802_, v___y_3798_, v___y_3804_);
return v___x_3828_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v___x_3829_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3830_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3831_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3819_, v_options_3813_, v___x_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; 
lean_del_object(v___x_3817_);
v___x_3832_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3826_, v_fst_3814_, v_snd_3815_, v___f_3825_, v___y_3805_, v___x_3827_, v___y_3801_, v___y_3796_, v___y_3800_, v___y_3799_, v___y_3802_, v___y_3798_, v___y_3804_);
return v___x_3832_;
}
else
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3836_; 
lean_inc(v___x_3826_);
v___x_3833_ = l_Lean_MessageData_ofName(v___x_3826_);
v___x_3834_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3818_ == 0)
{
lean_ctor_set_tag(v___x_3817_, 7);
lean_ctor_set(v___x_3817_, 1, v___x_3834_);
lean_ctor_set(v___x_3817_, 0, v___x_3833_);
v___x_3836_ = v___x_3817_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_inc(v_fst_3814_);
v___x_3837_ = l_Lean_MessageData_ofExpr(v_fst_3814_);
v___x_3838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3836_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3838_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
lean_inc(v_snd_3815_);
v___x_3841_ = l_Lean_MessageData_ofExpr(v_snd_3815_);
v___x_3842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3829_, v___x_3842_, v___y_3799_, v___y_3802_, v___y_3798_, v___y_3804_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v___x_3844_; 
lean_dec_ref_known(v___x_3843_, 1);
v___x_3844_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3826_, v_fst_3814_, v_snd_3815_, v___f_3825_, v___y_3805_, v___x_3827_, v___y_3801_, v___y_3796_, v___y_3800_, v___y_3799_, v___y_3802_, v___y_3798_, v___y_3804_);
return v___x_3844_;
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v___x_3826_);
lean_dec_ref(v___f_3825_);
lean_dec(v_snd_3815_);
lean_dec(v_fst_3814_);
v_a_3845_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3843_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3843_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
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
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v___y_3797_);
lean_dec(v___y_3793_);
lean_dec(v___y_3789_);
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_letOrReassign_3671_);
v_a_3855_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3810_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3810_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
v___jp_3863_:
{
uint8_t v_nondep_3880_; 
v_nondep_3880_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1);
if (v_nondep_3880_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3671_) == 1)
{
uint8_t v_usedOnly_3881_; uint8_t v_zeta_3882_; lean_object* v_eq_x3f_3883_; 
v_usedOnly_3881_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1 + 1);
v_zeta_3882_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1 + 2);
v_eq_x3f_3883_ = lean_ctor_get(v_config_3670_, 0);
lean_inc(v_eq_x3f_3883_);
lean_dec_ref(v_config_3670_);
lean_inc(v_id_3872_);
v___y_3787_ = v___y_3864_;
v___y_3788_ = v___y_3865_;
v___y_3789_ = v_id_3872_;
v___y_3790_ = v___y_3866_;
v___y_3791_ = v_zeta_3882_;
v___y_3792_ = v___y_3867_;
v___y_3793_ = v_eq_x3f_3883_;
v___y_3794_ = v_usedOnly_3881_;
v___y_3795_ = v___y_3869_;
v___y_3796_ = v___y_3874_;
v___y_3797_ = v_id_3872_;
v___y_3798_ = v___y_3878_;
v___y_3799_ = v___y_3876_;
v___y_3800_ = v___y_3875_;
v___y_3801_ = v___y_3873_;
v___y_3802_ = v___y_3877_;
v___y_3803_ = v___y_3868_;
v___y_3804_ = v___y_3879_;
v___y_3805_ = v___y_3870_;
goto v___jp_3786_;
}
else
{
uint8_t v_usedOnly_3884_; uint8_t v_zeta_3885_; lean_object* v_eq_x3f_3886_; 
v_usedOnly_3884_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1 + 1);
v_zeta_3885_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1 + 2);
v_eq_x3f_3886_ = lean_ctor_get(v_config_3670_, 0);
lean_inc(v_eq_x3f_3886_);
lean_dec_ref(v_config_3670_);
lean_inc(v_id_3872_);
v___y_3787_ = v___y_3864_;
v___y_3788_ = v___y_3865_;
v___y_3789_ = v_id_3872_;
v___y_3790_ = v___y_3866_;
v___y_3791_ = v_zeta_3885_;
v___y_3792_ = v___y_3867_;
v___y_3793_ = v_eq_x3f_3886_;
v___y_3794_ = v_usedOnly_3884_;
v___y_3795_ = v___y_3869_;
v___y_3796_ = v___y_3874_;
v___y_3797_ = v_id_3872_;
v___y_3798_ = v___y_3878_;
v___y_3799_ = v___y_3876_;
v___y_3800_ = v___y_3875_;
v___y_3801_ = v___y_3873_;
v___y_3802_ = v___y_3877_;
v___y_3803_ = v___y_3868_;
v___y_3804_ = v___y_3879_;
v___y_3805_ = v___y_3871_;
goto v___jp_3786_;
}
}
else
{
uint8_t v_usedOnly_3887_; uint8_t v_zeta_3888_; lean_object* v_eq_x3f_3889_; 
v_usedOnly_3887_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1 + 1);
v_zeta_3888_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1 + 2);
v_eq_x3f_3889_ = lean_ctor_get(v_config_3670_, 0);
lean_inc(v_eq_x3f_3889_);
lean_dec_ref(v_config_3670_);
lean_inc(v_id_3872_);
v___y_3787_ = v___y_3864_;
v___y_3788_ = v___y_3865_;
v___y_3789_ = v_id_3872_;
v___y_3790_ = v___y_3866_;
v___y_3791_ = v_zeta_3888_;
v___y_3792_ = v___y_3867_;
v___y_3793_ = v_eq_x3f_3889_;
v___y_3794_ = v_usedOnly_3887_;
v___y_3795_ = v___y_3869_;
v___y_3796_ = v___y_3874_;
v___y_3797_ = v_id_3872_;
v___y_3798_ = v___y_3878_;
v___y_3799_ = v___y_3876_;
v___y_3800_ = v___y_3875_;
v___y_3801_ = v___y_3873_;
v___y_3802_ = v___y_3877_;
v___y_3803_ = v___y_3868_;
v___y_3804_ = v___y_3879_;
v___y_3805_ = v___y_3870_;
goto v___jp_3786_;
}
}
v___jp_3890_:
{
lean_object* v_doBlockResultType_3899_; lean_object* v___x_3900_; 
v_doBlockResultType_3899_ = lean_ctor_get(v___y_3892_, 3);
lean_inc_ref(v_doBlockResultType_3899_);
v___x_3900_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3899_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3975_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3903_ = v___x_3900_;
v_isShared_3904_ = v_isSharedCheck_3975_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3975_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3906_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3907_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3908_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_3891_);
v___x_3909_ = l_Lean_Syntax_isOfKind(v_decl_3891_, v___x_3908_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_del_object(v___x_3903_);
lean_dec(v_a_3901_);
lean_dec(v_decl_3891_);
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_tk_3673_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v___x_3910_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3910_;
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v___x_3911_ = lean_unsigned_to_nat(0u);
v___x_3912_ = l_Lean_Syntax_getArg(v_decl_3891_, v___x_3911_);
lean_dec(v_decl_3891_);
v___x_3913_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__10));
lean_inc(v___x_3912_);
v___x_3914_ = l_Lean_Syntax_isOfKind(v___x_3912_, v___x_3913_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; uint8_t v___x_3916_; 
lean_dec(v_tk_3673_);
v___x_3915_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3912_);
v___x_3916_ = l_Lean_Syntax_isOfKind(v___x_3912_, v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; uint8_t v___x_3918_; 
lean_del_object(v___x_3903_);
lean_dec(v_a_3901_);
v___x_3917_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3912_);
v___x_3918_ = l_Lean_Syntax_isOfKind(v___x_3912_, v___x_3917_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; 
lean_dec(v___x_3912_);
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v___x_3919_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3919_;
}
else
{
lean_object* v___x_3920_; lean_object* v_id_3921_; lean_object* v_binders_3922_; lean_object* v_type_3923_; lean_object* v_value_3924_; uint8_t v___x_3925_; 
v___x_3920_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3912_);
lean_dec(v___x_3912_);
v_id_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_id_3921_);
v_binders_3922_ = lean_ctor_get(v___x_3920_, 1);
lean_inc_ref(v_binders_3922_);
v_type_3923_ = lean_ctor_get(v___x_3920_, 2);
lean_inc(v_type_3923_);
v_value_3924_ = lean_ctor_get(v___x_3920_, 3);
lean_inc(v_value_3924_);
lean_dec_ref(v___x_3920_);
v___x_3925_ = l_Lean_Syntax_isIdent(v_id_3921_);
if (v___x_3925_ == 0)
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_id_3921_, v___x_3909_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v_id_3921_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref_known(v___x_3926_, 1);
v___y_3864_ = v___x_3909_;
v___y_3865_ = v___x_3911_;
v___y_3866_ = v___x_3916_;
v___y_3867_ = v_type_3923_;
v___y_3868_ = v_binders_3922_;
v___y_3869_ = v_value_3924_;
v___y_3870_ = v___x_3909_;
v___y_3871_ = v___x_3916_;
v_id_3872_ = v_a_3927_;
v___y_3873_ = v___y_3892_;
v___y_3874_ = v___y_3893_;
v___y_3875_ = v___y_3894_;
v___y_3876_ = v___y_3895_;
v___y_3877_ = v___y_3896_;
v___y_3878_ = v___y_3897_;
v___y_3879_ = v___y_3898_;
goto v___jp_3863_;
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec(v_value_3924_);
lean_dec(v_type_3923_);
lean_dec_ref(v_binders_3922_);
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v_a_3928_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3926_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3926_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
else
{
v___y_3864_ = v___x_3909_;
v___y_3865_ = v___x_3911_;
v___y_3866_ = v___x_3916_;
v___y_3867_ = v_type_3923_;
v___y_3868_ = v_binders_3922_;
v___y_3869_ = v_value_3924_;
v___y_3870_ = v___x_3909_;
v___y_3871_ = v___x_3916_;
v_id_3872_ = v_id_3921_;
v___y_3873_ = v___y_3892_;
v___y_3874_ = v___y_3893_;
v___y_3875_ = v___y_3894_;
v___y_3876_ = v___y_3895_;
v___y_3877_ = v___y_3896_;
v___y_3878_ = v___y_3897_;
v___y_3879_ = v___y_3898_;
goto v___jp_3863_;
}
}
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3937_; uint8_t v___x_3938_; 
v___x_3936_ = lean_unsigned_to_nat(1u);
v___x_3937_ = l_Lean_Syntax_getArg(v___x_3912_, v___x_3936_);
v___x_3938_ = l_Lean_Syntax_matchesNull(v___x_3937_, v___x_3911_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; 
lean_dec(v___x_3912_);
lean_del_object(v___x_3903_);
lean_dec(v_a_3901_);
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v___x_3939_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3939_;
}
else
{
lean_object* v___x_3940_; lean_object* v___f_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3940_ = lean_box(v___x_3914_);
v___f_3941_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 10, 1);
lean_closure_set(v___f_3941_, 0, v___x_3940_);
v___x_3942_ = l_Lean_Syntax_getArg(v___x_3912_, v___x_3911_);
v___x_3943_ = lean_unsigned_to_nat(2u);
v___x_3944_ = l_Lean_Syntax_getArg(v___x_3912_, v___x_3943_);
v___x_3945_ = l_Lean_Syntax_isNone(v___x_3944_);
if (v___x_3945_ == 0)
{
uint8_t v___x_3946_; 
lean_inc(v___x_3944_);
v___x_3946_ = l_Lean_Syntax_matchesNull(v___x_3944_, v___x_3936_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
lean_dec(v___x_3944_);
lean_dec(v___x_3942_);
lean_dec_ref(v___f_3941_);
lean_dec(v___x_3912_);
lean_del_object(v___x_3903_);
lean_dec(v_a_3901_);
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v___x_3947_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3947_;
}
else
{
lean_object* v___x_3948_; lean_object* v___x_3949_; uint8_t v___x_3950_; 
v___x_3948_ = l_Lean_Syntax_getArg(v___x_3944_, v___x_3911_);
lean_dec(v___x_3944_);
v___x_3949_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3948_);
v___x_3950_ = l_Lean_Syntax_isOfKind(v___x_3948_, v___x_3949_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; 
lean_dec(v___x_3948_);
lean_dec(v___x_3942_);
lean_dec_ref(v___f_3941_);
lean_dec(v___x_3912_);
lean_del_object(v___x_3903_);
lean_dec(v_a_3901_);
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v___x_3951_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3951_;
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3954_; 
v___x_3952_ = l_Lean_Syntax_getArg(v___x_3948_, v___x_3936_);
lean_dec(v___x_3948_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set_tag(v___x_3903_, 1);
lean_ctor_set(v___x_3903_, 0, v___x_3952_);
v___x_3954_ = v___x_3903_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
v___y_3718_ = v___x_3906_;
v___y_3719_ = v___x_3909_;
v___y_3720_ = v_a_3901_;
v___y_3721_ = v___x_3907_;
v___y_3722_ = v___f_3941_;
v___y_3723_ = v___x_3905_;
v___y_3724_ = v___x_3942_;
v___y_3725_ = v___x_3914_;
v___y_3726_ = v___x_3906_;
v___y_3727_ = v___x_3907_;
v___y_3728_ = v___x_3905_;
v___y_3729_ = v___x_3914_;
v___y_3730_ = v___x_3912_;
v_xType_x3f_3731_ = v___x_3954_;
v___y_3732_ = v___y_3892_;
v___y_3733_ = v___y_3893_;
v___y_3734_ = v___y_3894_;
v___y_3735_ = v___y_3895_;
v___y_3736_ = v___y_3896_;
v___y_3737_ = v___y_3897_;
v___y_3738_ = v___y_3898_;
goto v___jp_3717_;
}
}
}
}
else
{
lean_object* v___x_3956_; 
lean_dec(v___x_3944_);
lean_del_object(v___x_3903_);
v___x_3956_ = lean_box(0);
v___y_3718_ = v___x_3906_;
v___y_3719_ = v___x_3909_;
v___y_3720_ = v_a_3901_;
v___y_3721_ = v___x_3907_;
v___y_3722_ = v___f_3941_;
v___y_3723_ = v___x_3905_;
v___y_3724_ = v___x_3942_;
v___y_3725_ = v___x_3914_;
v___y_3726_ = v___x_3906_;
v___y_3727_ = v___x_3907_;
v___y_3728_ = v___x_3905_;
v___y_3729_ = v___x_3914_;
v___y_3730_ = v___x_3912_;
v_xType_x3f_3731_ = v___x_3956_;
v___y_3732_ = v___y_3892_;
v___y_3733_ = v___y_3893_;
v___y_3734_ = v___y_3894_;
v___y_3735_ = v___y_3895_;
v___y_3736_ = v___y_3896_;
v___y_3737_ = v___y_3897_;
v___y_3738_ = v___y_3898_;
goto v___jp_3717_;
}
}
}
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_del_object(v___x_3903_);
lean_dec(v_a_3901_);
lean_dec(v_a_3685_);
v___x_3957_ = lean_box(v___x_3909_);
lean_inc(v___x_3912_);
v___x_3958_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3958_, 0, v___x_3912_);
lean_closure_set(v___x_3958_, 1, v___x_3957_);
v___x_3959_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3958_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v_ref_3961_; uint8_t v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v___x_3959_, 1);
v_ref_3961_ = lean_ctor_get(v___y_3897_, 2);
v___x_3962_ = 0;
v___x_3963_ = l_Lean_SourceInfo_fromRef(v_ref_3961_, v___x_3962_);
v___x_3964_ = l_Lean_Syntax_node1(v___x_3963_, v___x_3908_, v_a_3960_);
lean_inc(v___x_3964_);
v___x_3965_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3965_, 0, v_config_3670_);
lean_closure_set(v___x_3965_, 1, v_letOrReassign_3671_);
lean_closure_set(v___x_3965_, 2, v___x_3964_);
lean_closure_set(v___x_3965_, 3, v_tk_3673_);
lean_closure_set(v___x_3965_, 4, v_a_3688_);
v___x_3966_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v___x_3912_, v___x_3964_, v___x_3965_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
return v___x_3966_;
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec(v___x_3912_);
lean_dec(v_a_3688_);
lean_dec(v_tk_3673_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v_a_3967_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3959_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3959_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
}
}
}
else
{
lean_dec(v_decl_3891_);
lean_dec(v_a_3688_);
lean_dec(v_a_3685_);
lean_dec(v_tk_3673_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
return v___x_3900_;
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v_a_3685_);
lean_dec(v_tk_3673_);
lean_dec(v_decl_3672_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v_a_4008_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3687_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3687_);
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
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v_a_3685_);
lean_dec_ref(v_dec_3674_);
lean_dec(v_tk_3673_);
lean_dec(v_decl_3672_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v_a_4016_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3686_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3686_);
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
lean_dec_ref(v_dec_3674_);
lean_dec(v_tk_3673_);
lean_dec(v_decl_3672_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v_a_4024_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_3684_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_3684_);
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
lean_dec_ref(v_dec_3674_);
lean_dec(v_tk_3673_);
lean_dec(v_decl_3672_);
lean_dec(v_letOrReassign_3671_);
lean_dec_ref(v_config_3670_);
v_a_4032_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_3683_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_3683_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_4040_, lean_object* v_x_4041_, lean_object* v_x_4042_, lean_object* v_x_4043_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_4041_, v_x_4042_, v_x_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_cls_4045_, lean_object* v_msg_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_4045_, v_msg_4046_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_cls_4056_, lean_object* v_msg_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_cls_4056_, v_msg_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_4072_, v___y_4073_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___boxed(lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec_ref(v___y_4076_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_00_u03b1_4085_, lean_object* v_beforeStx_4086_, lean_object* v_afterStx_4087_, lean_object* v_x_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_beforeStx_4086_, v_afterStx_4087_, v_x_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_00_u03b1_4098_, lean_object* v_beforeStx_4099_, lean_object* v_afterStx_4100_, lean_object* v_x_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_00_u03b1_4098_, v_beforeStx_4099_, v_afterStx_4100_, v_x_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec_ref(v___y_4102_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(lean_object* v_00_u03b1_4111_, lean_object* v_x_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___redArg(v_x_4112_, v___y_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___boxed(lean_object* v_00_u03b1_4116_, lean_object* v_x_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(v_00_u03b1_4116_, v_x_4117_, v___y_4118_, v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec_ref(v_x_4117_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16(lean_object* v_00_u03b1_4121_, lean_object* v_ref_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___redArg(v_ref_4122_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16___boxed(lean_object* v_00_u03b1_4132_, lean_object* v_ref_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__16(v_00_u03b1_4132_, v_ref_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec_ref(v___y_4134_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_4143_, lean_object* v_x_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_4154_, lean_object* v_x_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_4154_, v_x_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec_ref(v___y_4156_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_4165_, lean_object* v_x_4166_, size_t v_x_4167_, size_t v_x_4168_, lean_object* v_x_4169_, lean_object* v_x_4170_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_4166_, v_x_4167_, v_x_4168_, v_x_4169_, v_x_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4172_, lean_object* v_x_4173_, lean_object* v_x_4174_, lean_object* v_x_4175_, lean_object* v_x_4176_, lean_object* v_x_4177_){
_start:
{
size_t v_x_92499__boxed_4178_; size_t v_x_92500__boxed_4179_; lean_object* v_res_4180_; 
v_x_92499__boxed_4178_ = lean_unbox_usize(v_x_4174_);
lean_dec(v_x_4174_);
v_x_92500__boxed_4179_ = lean_unbox_usize(v_x_4175_);
lean_dec(v_x_4175_);
v_res_4180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_4172_, v_x_4173_, v_x_92499__boxed_4178_, v_x_92500__boxed_4179_, v_x_4176_, v_x_4177_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10(lean_object* v_00_u03b1_4181_, lean_object* v_stx_4182_, lean_object* v_output_4183_, lean_object* v_x_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___redArg(v_stx_4182_, v_output_4183_, v_x_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10___boxed(lean_object* v_00_u03b1_4193_, lean_object* v_stx_4194_, lean_object* v_output_4195_, lean_object* v_x_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10(v_00_u03b1_4193_, v_stx_4194_, v_output_4195_, v_x_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(lean_object* v_as_4205_, lean_object* v_as_x27_4206_, lean_object* v_b_4207_, lean_object* v_a_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___redArg(v_as_x27_4206_, v_b_4207_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___boxed(lean_object* v_as_4218_, lean_object* v_as_x27_4219_, lean_object* v_b_4220_, lean_object* v_a_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(v_as_4218_, v_as_x27_4219_, v_b_4220_, v_a_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v_as_x27_4219_);
lean_dec(v_as_4218_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4231_, lean_object* v_n_4232_, lean_object* v_k_4233_, lean_object* v_v_4234_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(v_n_4232_, v_k_4233_, v_v_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_4236_, size_t v_depth_4237_, lean_object* v_keys_4238_, lean_object* v_vals_4239_, lean_object* v_heq_4240_, lean_object* v_i_4241_, lean_object* v_entries_4242_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_depth_4237_, v_keys_4238_, v_vals_4239_, v_i_4241_, v_entries_4242_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_4244_, lean_object* v_depth_4245_, lean_object* v_keys_4246_, lean_object* v_vals_4247_, lean_object* v_heq_4248_, lean_object* v_i_4249_, lean_object* v_entries_4250_){
_start:
{
size_t v_depth_boxed_4251_; lean_object* v_res_4252_; 
v_depth_boxed_4251_ = lean_unbox_usize(v_depth_4245_);
lean_dec(v_depth_4245_);
v_res_4252_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(v_00_u03b2_4244_, v_depth_boxed_4251_, v_keys_4246_, v_vals_4247_, v_heq_4248_, v_i_4249_, v_entries_4250_);
lean_dec_ref(v_vals_4247_);
lean_dec_ref(v_keys_4246_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18(lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___redArg(v___y_4258_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18___boxed(lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13_spec__18(v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13(lean_object* v_00_u03b1_4269_, lean_object* v_x_4270_, lean_object* v_mkInfoTree_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___redArg(v_x_4270_, v_mkInfoTree_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b1_4280_, lean_object* v_x_4281_, lean_object* v_mkInfoTree_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__10_spec__13(v_00_u03b1_4280_, v_x_4281_, v_mkInfoTree_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19(lean_object* v_00_u03b2_4291_, lean_object* v_m_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___redArg(v_m_4292_, v_a_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19___boxed(lean_object* v_00_u03b2_4295_, lean_object* v_m_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19(v_00_u03b2_4295_, v_m_4296_, v_a_4297_);
lean_dec(v_a_4297_);
lean_dec_ref(v_m_4296_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14(lean_object* v_00_u03b2_4299_, lean_object* v_x_4300_, lean_object* v_x_4301_, lean_object* v_x_4302_, lean_object* v_x_4303_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__14___redArg(v_x_4300_, v_x_4301_, v_x_4302_, v_x_4303_);
return v___x_4304_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_4305_, lean_object* v_x_4306_, lean_object* v_x_4307_){
_start:
{
uint8_t v___x_4308_; 
v___x_4308_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___redArg(v_x_4306_, v_x_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_4309_, lean_object* v_x_4310_, lean_object* v_x_4311_){
_start:
{
uint8_t v_res_4312_; lean_object* v_r_4313_; 
v_res_4312_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21(v_00_u03b2_4309_, v_x_4310_, v_x_4311_);
lean_dec_ref(v_x_4311_);
lean_dec_ref(v_x_4310_);
v_r_4313_ = lean_box(v_res_4312_);
return v_r_4313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24(lean_object* v_00_u03b2_4314_, lean_object* v_a_4315_, lean_object* v_x_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24___redArg(v_a_4315_, v_x_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24___boxed(lean_object* v_00_u03b2_4318_, lean_object* v_a_4319_, lean_object* v_x_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__19_spec__24(v_00_u03b2_4318_, v_a_4319_, v_x_4320_);
lean_dec(v_x_4320_);
lean_dec(v_a_4319_);
return v_res_4321_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24(lean_object* v_00_u03b2_4322_, lean_object* v_x_4323_, size_t v_x_4324_, lean_object* v_x_4325_){
_start:
{
uint8_t v___x_4326_; 
v___x_4326_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___redArg(v_x_4323_, v_x_4324_, v_x_4325_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24___boxed(lean_object* v_00_u03b2_4327_, lean_object* v_x_4328_, lean_object* v_x_4329_, lean_object* v_x_4330_){
_start:
{
size_t v_x_92643__boxed_4331_; uint8_t v_res_4332_; lean_object* v_r_4333_; 
v_x_92643__boxed_4331_ = lean_unbox_usize(v_x_4329_);
lean_dec(v_x_4329_);
v_res_4332_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24(v_00_u03b2_4327_, v_x_4328_, v_x_92643__boxed_4331_, v_x_4330_);
lean_dec_ref(v_x_4330_);
lean_dec_ref(v_x_4328_);
v_r_4333_ = lean_box(v_res_4332_);
return v_r_4333_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27(lean_object* v_00_u03b2_4334_, lean_object* v_keys_4335_, lean_object* v_vals_4336_, lean_object* v_heq_4337_, lean_object* v_i_4338_, lean_object* v_k_4339_){
_start:
{
uint8_t v___x_4340_; 
v___x_4340_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___redArg(v_keys_4335_, v_i_4338_, v_k_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27___boxed(lean_object* v_00_u03b2_4341_, lean_object* v_keys_4342_, lean_object* v_vals_4343_, lean_object* v_heq_4344_, lean_object* v_i_4345_, lean_object* v_k_4346_){
_start:
{
uint8_t v_res_4347_; lean_object* v_r_4348_; 
v_res_4347_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13_spec__17_spec__21_spec__24_spec__27(v_00_u03b2_4341_, v_keys_4342_, v_vals_4343_, v_heq_4344_, v_i_4345_, v_k_4346_);
lean_dec_ref(v_k_4346_);
lean_dec_ref(v_vals_4343_);
lean_dec_ref(v_keys_4342_);
v_r_4348_ = lean_box(v_res_4347_);
return v_r_4348_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1(void){
_start:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4350_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__0));
v___x_4351_ = l_Lean_stringToMessageData(v___x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4352_, lean_object* v_mutTk_x3f_4353_, lean_object* v_initConfig_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4353_) == 0)
{
lean_object* v___x_4363_; 
v___x_4363_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4352_, v_initConfig_4354_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_);
return v___x_4363_;
}
else
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; 
v___x_4364_ = lean_unsigned_to_nat(0u);
v___x_4365_ = l_Lean_Syntax_getArg(v_letConfigStx_4352_, v___x_4364_);
v___x_4366_ = l_Lean_Syntax_getArgs(v___x_4365_);
lean_dec(v___x_4365_);
v___x_4367_ = lean_array_get_size(v___x_4366_);
lean_dec_ref(v___x_4366_);
v___x_4368_ = lean_nat_dec_eq(v___x_4367_, v___x_4364_);
if (v___x_4368_ == 0)
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec_ref(v_initConfig_4354_);
v___x_4369_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1);
v___x_4370_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_letConfigStx_4352_, v___x_4369_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_);
lean_dec(v_letConfigStx_4352_);
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4370_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4370_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
else
{
lean_object* v___x_4379_; 
v___x_4379_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4352_, v_initConfig_4354_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_);
return v___x_4379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4380_, lean_object* v_mutTk_x3f_4381_, lean_object* v_initConfig_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4380_, v_mutTk_x3f_4381_, v_initConfig_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
lean_dec_ref(v_a_4383_);
lean_dec(v_mutTk_x3f_4381_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4407_, lean_object* v_dec_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v___x_4417_; uint8_t v___x_4418_; 
v___x_4417_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_stx_4407_);
v___x_4418_ = l_Lean_Syntax_isOfKind(v_stx_4407_, v___x_4417_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4419_; 
lean_dec_ref(v_dec_4408_);
lean_dec(v_stx_4407_);
v___x_4419_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4419_;
}
else
{
lean_object* v___x_4420_; lean_object* v_tk_4421_; lean_object* v_mutTk_x3f_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___x_4455_; lean_object* v___x_4456_; uint8_t v___x_4457_; 
v___x_4420_ = lean_unsigned_to_nat(0u);
v_tk_4421_ = l_Lean_Syntax_getArg(v_stx_4407_, v___x_4420_);
v___x_4455_ = lean_unsigned_to_nat(1u);
v___x_4456_ = l_Lean_Syntax_getArg(v_stx_4407_, v___x_4455_);
v___x_4457_ = l_Lean_Syntax_isNone(v___x_4456_);
if (v___x_4457_ == 0)
{
uint8_t v___x_4458_; 
lean_inc(v___x_4456_);
v___x_4458_ = l_Lean_Syntax_matchesNull(v___x_4456_, v___x_4455_);
if (v___x_4458_ == 0)
{
lean_object* v___x_4459_; 
lean_dec(v___x_4456_);
lean_dec(v_tk_4421_);
lean_dec_ref(v_dec_4408_);
lean_dec(v_stx_4407_);
v___x_4459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4459_;
}
else
{
lean_object* v_mutTk_x3f_4460_; lean_object* v___x_4461_; 
v_mutTk_x3f_4460_ = l_Lean_Syntax_getArg(v___x_4456_, v___x_4420_);
lean_dec(v___x_4456_);
v___x_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4461_, 0, v_mutTk_x3f_4460_);
v_mutTk_x3f_4423_ = v___x_4461_;
v___y_4424_ = v_a_4409_;
v___y_4425_ = v_a_4410_;
v___y_4426_ = v_a_4411_;
v___y_4427_ = v_a_4412_;
v___y_4428_ = v_a_4413_;
v___y_4429_ = v_a_4414_;
v___y_4430_ = v_a_4415_;
goto v___jp_4422_;
}
}
else
{
lean_object* v___x_4462_; 
lean_dec(v___x_4456_);
v___x_4462_ = lean_box(0);
v_mutTk_x3f_4423_ = v___x_4462_;
v___y_4424_ = v_a_4409_;
v___y_4425_ = v_a_4410_;
v___y_4426_ = v_a_4411_;
v___y_4427_ = v_a_4412_;
v___y_4428_ = v_a_4413_;
v___y_4429_ = v_a_4414_;
v___y_4430_ = v_a_4415_;
goto v___jp_4422_;
}
v___jp_4422_:
{
lean_object* v___x_4431_; lean_object* v_config_4432_; lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4431_ = lean_unsigned_to_nat(2u);
v_config_4432_ = l_Lean_Syntax_getArg(v_stx_4407_, v___x_4431_);
v___x_4433_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_config_4432_);
v___x_4434_ = l_Lean_Syntax_isOfKind(v_config_4432_, v___x_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; 
lean_dec(v_config_4432_);
lean_dec(v_mutTk_x3f_4423_);
lean_dec(v_tk_4421_);
lean_dec_ref(v_dec_4408_);
lean_dec(v_stx_4407_);
v___x_4435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4435_;
}
else
{
lean_object* v___x_4436_; lean_object* v_decl_4437_; lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4436_ = lean_unsigned_to_nat(3u);
v_decl_4437_ = l_Lean_Syntax_getArg(v_stx_4407_, v___x_4436_);
lean_dec(v_stx_4407_);
v___x_4438_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4437_);
v___x_4439_ = l_Lean_Syntax_isOfKind(v_decl_4437_, v___x_4438_);
if (v___x_4439_ == 0)
{
lean_object* v___x_4440_; 
lean_dec(v_decl_4437_);
lean_dec(v_config_4432_);
lean_dec(v_mutTk_x3f_4423_);
lean_dec(v_tk_4421_);
lean_dec_ref(v_dec_4408_);
v___x_4440_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4440_;
}
else
{
uint8_t v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4441_ = 0;
v___x_4442_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_4443_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_config_4432_, v_mutTk_x3f_4423_, v___x_4442_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_a_4444_);
lean_dec_ref_known(v___x_4443_, 1);
v___x_4445_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4445_, 0, v_mutTk_x3f_4423_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*1, v___x_4441_);
v___x_4446_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4444_, v___x_4445_, v_decl_4437_, v_tk_4421_, v_dec_4408_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
return v___x_4446_;
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec(v_decl_4437_);
lean_dec(v_mutTk_x3f_4423_);
lean_dec(v_tk_4421_);
lean_dec_ref(v_dec_4408_);
v_a_4447_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4443_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4443_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4463_, lean_object* v_dec_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_Elab_Do_elabDoLet(v_stx_4463_, v_dec_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_);
lean_dec(v_a_4471_);
lean_dec_ref(v_a_4470_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec_ref(v_a_4465_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4481_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4482_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_4483_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4484_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4485_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4481_, v___x_4482_, v___x_4483_, v___x_4484_);
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased(lean_object* v_stx_4502_, lean_object* v_dec_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4512_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
lean_inc(v_stx_4502_);
v___x_4513_ = l_Lean_Syntax_isOfKind(v_stx_4502_, v___x_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; 
lean_dec_ref(v_dec_4503_);
lean_dec(v_stx_4502_);
v___x_4514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4514_;
}
else
{
lean_object* v___x_4515_; lean_object* v_tk_4516_; uint8_t v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v_t_x3f_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___x_4577_; lean_object* v_mutTk_x3f_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___x_4614_; uint8_t v___x_4615_; 
v___x_4515_ = lean_unsigned_to_nat(0u);
v_tk_4516_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4515_);
v___x_4577_ = lean_unsigned_to_nat(1u);
v___x_4614_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4577_);
v___x_4615_ = l_Lean_Syntax_isNone(v___x_4614_);
if (v___x_4615_ == 0)
{
uint8_t v___x_4616_; 
lean_inc(v___x_4614_);
v___x_4616_ = l_Lean_Syntax_matchesNull(v___x_4614_, v___x_4577_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; 
lean_dec(v___x_4614_);
lean_dec(v_tk_4516_);
lean_dec_ref(v_dec_4503_);
lean_dec(v_stx_4502_);
v___x_4617_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4617_;
}
else
{
lean_object* v_mutTk_x3f_4618_; lean_object* v___x_4619_; 
v_mutTk_x3f_4618_ = l_Lean_Syntax_getArg(v___x_4614_, v___x_4515_);
lean_dec(v___x_4614_);
v___x_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4619_, 0, v_mutTk_x3f_4618_);
v_mutTk_x3f_4579_ = v___x_4619_;
v___y_4580_ = v_a_4504_;
v___y_4581_ = v_a_4505_;
v___y_4582_ = v_a_4506_;
v___y_4583_ = v_a_4507_;
v___y_4584_ = v_a_4508_;
v___y_4585_ = v_a_4509_;
v___y_4586_ = v_a_4510_;
goto v___jp_4578_;
}
}
else
{
lean_object* v___x_4620_; 
lean_dec(v___x_4614_);
v___x_4620_ = lean_box(0);
v_mutTk_x3f_4579_ = v___x_4620_;
v___y_4580_ = v_a_4504_;
v___y_4581_ = v_a_4505_;
v___y_4582_ = v_a_4506_;
v___y_4583_ = v_a_4507_;
v___y_4584_ = v_a_4508_;
v___y_4585_ = v_a_4509_;
v___y_4586_ = v_a_4510_;
goto v___jp_4578_;
}
v___jp_4517_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
lean_inc_ref(v___y_4521_);
v___x_4536_ = l_Array_append___redArg(v___y_4521_, v___y_4535_);
lean_dec_ref(v___y_4535_);
lean_inc(v___y_4529_);
lean_inc_n(v___y_4526_, 3);
v___x_4537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4537_, 0, v___y_4526_);
lean_ctor_set(v___x_4537_, 1, v___y_4529_);
lean_ctor_set(v___x_4537_, 2, v___x_4536_);
v___x_4538_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___y_4526_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
lean_inc(v___y_4520_);
v___x_4540_ = l_Lean_Syntax_node5(v___y_4526_, v___y_4520_, v___y_4534_, v___y_4522_, v___x_4537_, v___x_4539_, v___y_4524_);
lean_inc(v___y_4533_);
v___x_4541_ = l_Lean_Syntax_node1(v___y_4526_, v___y_4533_, v___x_4540_);
v___x_4542_ = lean_box(0);
v___x_4543_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
lean_ctor_set_uint8(v___x_4543_, sizeof(void*)*1, v___y_4518_);
lean_ctor_set_uint8(v___x_4543_, sizeof(void*)*1 + 1, v___y_4518_);
lean_ctor_set_uint8(v___x_4543_, sizeof(void*)*1 + 2, v___y_4518_);
lean_ctor_set_uint8(v___x_4543_, sizeof(void*)*1 + 3, v___y_4518_);
lean_ctor_set_uint8(v___x_4543_, sizeof(void*)*1 + 4, v___y_4518_);
v___x_4544_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4544_, 0, v___y_4532_);
lean_ctor_set_uint8(v___x_4544_, sizeof(void*)*1, v___x_4513_);
v___x_4545_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4543_, v___x_4544_, v___x_4541_, v_tk_4516_, v_dec_4503_, v___y_4519_, v___y_4531_, v___y_4523_, v___y_4528_, v___y_4525_, v___y_4530_, v___y_4527_);
return v___x_4545_;
}
v___jp_4546_:
{
lean_object* v_ref_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; uint8_t v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_ref_4559_ = lean_ctor_get(v___y_4557_, 2);
v___x_4560_ = lean_unsigned_to_nat(4u);
v___x_4561_ = l_Lean_Syntax_getArg(v___y_4548_, v___x_4560_);
lean_dec(v___y_4548_);
v___x_4562_ = 0;
v___x_4563_ = l_Lean_SourceInfo_fromRef(v_ref_4559_, v___x_4562_);
v___x_4564_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4565_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___y_4550_);
lean_inc_n(v___x_4563_, 2);
v___x_4566_ = l_Lean_Syntax_node1(v___x_4563_, v___y_4550_, v___y_4547_);
v___x_4567_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4568_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4563_);
lean_ctor_set(v___x_4569_, 1, v___x_4567_);
lean_ctor_set(v___x_4569_, 2, v___x_4568_);
if (lean_obj_tag(v_t_x3f_4551_) == 1)
{
lean_object* v_val_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v_val_4570_ = lean_ctor_get(v_t_x3f_4551_, 0);
lean_inc(v_val_4570_);
lean_dec_ref_known(v_t_x3f_4551_, 1);
v___x_4571_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4572_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_4563_, 2);
v___x_4573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4563_);
lean_ctor_set(v___x_4573_, 1, v___x_4572_);
v___x_4574_ = l_Lean_Syntax_node2(v___x_4563_, v___x_4571_, v___x_4573_, v_val_4570_);
v___x_4575_ = l_Array_mkArray1___redArg(v___x_4574_);
v___y_4518_ = v___x_4562_;
v___y_4519_ = v___y_4552_;
v___y_4520_ = v___x_4565_;
v___y_4521_ = v___x_4568_;
v___y_4522_ = v___x_4569_;
v___y_4523_ = v___y_4554_;
v___y_4524_ = v___x_4561_;
v___y_4525_ = v___y_4556_;
v___y_4526_ = v___x_4563_;
v___y_4527_ = v___y_4558_;
v___y_4528_ = v___y_4555_;
v___y_4529_ = v___x_4567_;
v___y_4530_ = v___y_4557_;
v___y_4531_ = v___y_4553_;
v___y_4532_ = v___y_4549_;
v___y_4533_ = v___x_4564_;
v___y_4534_ = v___x_4566_;
v___y_4535_ = v___x_4575_;
goto v___jp_4517_;
}
else
{
lean_object* v___x_4576_; 
lean_dec(v_t_x3f_4551_);
v___x_4576_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4518_ = v___x_4562_;
v___y_4519_ = v___y_4552_;
v___y_4520_ = v___x_4565_;
v___y_4521_ = v___x_4568_;
v___y_4522_ = v___x_4569_;
v___y_4523_ = v___y_4554_;
v___y_4524_ = v___x_4561_;
v___y_4525_ = v___y_4556_;
v___y_4526_ = v___x_4563_;
v___y_4527_ = v___y_4558_;
v___y_4528_ = v___y_4555_;
v___y_4529_ = v___x_4567_;
v___y_4530_ = v___y_4557_;
v___y_4531_ = v___y_4553_;
v___y_4532_ = v___y_4549_;
v___y_4533_ = v___x_4564_;
v___y_4534_ = v___x_4566_;
v___y_4535_ = v___x_4576_;
goto v___jp_4517_;
}
}
v___jp_4578_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; 
v___x_4587_ = lean_unsigned_to_nat(2u);
v___x_4588_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4587_);
lean_dec(v_stx_4502_);
v___x_4589_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_4588_);
v___x_4590_ = l_Lean_Syntax_isOfKind(v___x_4588_, v___x_4589_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; 
lean_dec(v___x_4588_);
lean_dec(v_mutTk_x3f_4579_);
lean_dec(v_tk_4516_);
lean_dec_ref(v_dec_4503_);
v___x_4591_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4591_;
}
else
{
lean_object* v___x_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; 
v___x_4592_ = l_Lean_Syntax_getArg(v___x_4588_, v___x_4515_);
v___x_4593_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_4592_);
v___x_4594_ = l_Lean_Syntax_isOfKind(v___x_4592_, v___x_4593_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; 
lean_dec(v___x_4592_);
lean_dec(v___x_4588_);
lean_dec(v_mutTk_x3f_4579_);
lean_dec(v_tk_4516_);
lean_dec_ref(v_dec_4503_);
v___x_4595_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4595_;
}
else
{
lean_object* v___x_4596_; lean_object* v___x_4597_; uint8_t v___x_4598_; 
v___x_4596_ = l_Lean_Syntax_getArg(v___x_4592_, v___x_4515_);
lean_dec(v___x_4592_);
v___x_4597_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4596_);
v___x_4598_ = l_Lean_Syntax_isOfKind(v___x_4596_, v___x_4597_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; 
lean_dec(v___x_4596_);
lean_dec(v___x_4588_);
lean_dec(v_mutTk_x3f_4579_);
lean_dec(v_tk_4516_);
lean_dec_ref(v_dec_4503_);
v___x_4599_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4599_;
}
else
{
lean_object* v___x_4600_; uint8_t v___x_4601_; 
v___x_4600_ = l_Lean_Syntax_getArg(v___x_4588_, v___x_4577_);
v___x_4601_ = l_Lean_Syntax_matchesNull(v___x_4600_, v___x_4515_);
if (v___x_4601_ == 0)
{
lean_object* v___x_4602_; 
lean_dec(v___x_4596_);
lean_dec(v___x_4588_);
lean_dec(v_mutTk_x3f_4579_);
lean_dec(v_tk_4516_);
lean_dec_ref(v_dec_4503_);
v___x_4602_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4602_;
}
else
{
lean_object* v___x_4603_; uint8_t v___x_4604_; 
v___x_4603_ = l_Lean_Syntax_getArg(v___x_4588_, v___x_4587_);
v___x_4604_ = l_Lean_Syntax_isNone(v___x_4603_);
if (v___x_4604_ == 0)
{
uint8_t v___x_4605_; 
lean_inc(v___x_4603_);
v___x_4605_ = l_Lean_Syntax_matchesNull(v___x_4603_, v___x_4577_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; 
lean_dec(v___x_4603_);
lean_dec(v___x_4596_);
lean_dec(v___x_4588_);
lean_dec(v_mutTk_x3f_4579_);
lean_dec(v_tk_4516_);
lean_dec_ref(v_dec_4503_);
v___x_4606_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4606_;
}
else
{
lean_object* v___x_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; 
v___x_4607_ = l_Lean_Syntax_getArg(v___x_4603_, v___x_4515_);
lean_dec(v___x_4603_);
v___x_4608_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4607_);
v___x_4609_ = l_Lean_Syntax_isOfKind(v___x_4607_, v___x_4608_);
if (v___x_4609_ == 0)
{
lean_object* v___x_4610_; 
lean_dec(v___x_4607_);
lean_dec(v___x_4596_);
lean_dec(v___x_4588_);
lean_dec(v_mutTk_x3f_4579_);
lean_dec(v_tk_4516_);
lean_dec_ref(v_dec_4503_);
v___x_4610_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4610_;
}
else
{
lean_object* v_t_x3f_4611_; lean_object* v___x_4612_; 
v_t_x3f_4611_ = l_Lean_Syntax_getArg(v___x_4607_, v___x_4577_);
lean_dec(v___x_4607_);
v___x_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4612_, 0, v_t_x3f_4611_);
v___y_4547_ = v___x_4596_;
v___y_4548_ = v___x_4588_;
v___y_4549_ = v_mutTk_x3f_4579_;
v___y_4550_ = v___x_4593_;
v_t_x3f_4551_ = v___x_4612_;
v___y_4552_ = v___y_4580_;
v___y_4553_ = v___y_4581_;
v___y_4554_ = v___y_4582_;
v___y_4555_ = v___y_4583_;
v___y_4556_ = v___y_4584_;
v___y_4557_ = v___y_4585_;
v___y_4558_ = v___y_4586_;
goto v___jp_4546_;
}
}
}
else
{
lean_object* v___x_4613_; 
lean_dec(v___x_4603_);
v___x_4613_ = lean_box(0);
v___y_4547_ = v___x_4596_;
v___y_4548_ = v___x_4588_;
v___y_4549_ = v_mutTk_x3f_4579_;
v___y_4550_ = v___x_4593_;
v_t_x3f_4551_ = v___x_4613_;
v___y_4552_ = v___y_4580_;
v___y_4553_ = v___y_4581_;
v___y_4554_ = v___y_4582_;
v___y_4555_ = v___y_4583_;
v___y_4556_ = v___y_4584_;
v___y_4557_ = v___y_4585_;
v___y_4558_ = v___y_4586_;
goto v___jp_4546_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased___boxed(lean_object* v_stx_4621_, lean_object* v_dec_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_Lean_Elab_Do_elabDoErased(v_stx_4621_, v_dec_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec_ref(v_a_4623_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1(){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4639_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4640_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4641_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1));
v___x_4642_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoErased___boxed), 10, 0);
v___x_4643_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4639_, v___x_4640_, v___x_4641_, v___x_4642_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___boxed(lean_object* v_a_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1();
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0(lean_object* v_____do__lift_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
uint8_t v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4649_ = 0;
v___x_4650_ = l_Lean_SourceInfo_fromRef(v_____do__lift_4646_, v___x_4649_);
v___x_4651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4650_);
lean_ctor_set(v___x_4651_, 1, v___y_4648_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0___boxed(lean_object* v_____do__lift_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_____do__lift_4652_, v___y_4653_, v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v_____do__lift_4652_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow(lean_object* v_stx_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_){
_start:
{
lean_object* v___y_4703_; lean_object* v___y_4704_; lean_object* v___y_4705_; lean_object* v___y_4706_; lean_object* v___y_4707_; lean_object* v___y_4708_; uint8_t v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; lean_object* v___y_4714_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4741_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
lean_inc(v_stx_4699_);
v___x_4742_ = l_Lean_Syntax_isOfKind(v_stx_4699_, v___x_4741_);
if (v___x_4742_ == 0)
{
lean_object* v___x_4743_; 
lean_dec(v_stx_4699_);
v___x_4743_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4701_);
return v___x_4743_;
}
else
{
lean_object* v___x_4744_; lean_object* v_tk_4745_; lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; uint8_t v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v___y_4761_; lean_object* v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v_t_x3f_4794_; lean_object* v___y_4795_; lean_object* v___y_4796_; lean_object* v___x_4830_; lean_object* v_mutTk_x3f_4832_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___x_4855_; uint8_t v___x_4856_; 
v___x_4744_ = lean_unsigned_to_nat(0u);
v_tk_4745_ = l_Lean_Syntax_getArg(v_stx_4699_, v___x_4744_);
v___x_4830_ = lean_unsigned_to_nat(1u);
v___x_4855_ = l_Lean_Syntax_getArg(v_stx_4699_, v___x_4830_);
v___x_4856_ = l_Lean_Syntax_isNone(v___x_4855_);
if (v___x_4856_ == 0)
{
uint8_t v___x_4857_; 
lean_inc(v___x_4855_);
v___x_4857_ = l_Lean_Syntax_matchesNull(v___x_4855_, v___x_4830_);
if (v___x_4857_ == 0)
{
lean_object* v___x_4858_; 
lean_dec(v___x_4855_);
lean_dec(v_tk_4745_);
lean_dec(v_stx_4699_);
v___x_4858_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4701_);
return v___x_4858_;
}
else
{
lean_object* v_mutTk_x3f_4859_; lean_object* v___x_4860_; 
v_mutTk_x3f_4859_ = l_Lean_Syntax_getArg(v___x_4855_, v___x_4744_);
lean_dec(v___x_4855_);
v___x_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4860_, 0, v_mutTk_x3f_4859_);
v_mutTk_x3f_4832_ = v___x_4860_;
v___y_4833_ = v_a_4700_;
v___y_4834_ = v_a_4701_;
goto v___jp_4831_;
}
}
else
{
lean_object* v___x_4861_; 
lean_dec(v___x_4855_);
v___x_4861_ = lean_box(0);
v_mutTk_x3f_4832_ = v___x_4861_;
v___y_4833_ = v_a_4700_;
v___y_4834_ = v_a_4701_;
goto v___jp_4831_;
}
v___jp_4746_:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v_a_4767_; lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4788_; 
lean_inc_ref(v___y_4760_);
v___x_4764_ = l_Array_append___redArg(v___y_4760_, v___y_4763_);
lean_dec_ref(v___y_4763_);
lean_inc(v___y_4755_);
lean_inc(v___y_4750_);
v___x_4765_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4765_, 0, v___y_4750_);
lean_ctor_set(v___x_4765_, 1, v___y_4755_);
lean_ctor_set(v___x_4765_, 2, v___x_4764_);
v___x_4766_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v___y_4761_, v___y_4758_, v___y_4751_);
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
v_a_4768_ = lean_ctor_get(v___x_4766_, 1);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4770_ = v___x_4766_;
v_isShared_4771_ = v_isSharedCheck_4788_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_inc(v_a_4767_);
lean_dec(v___x_4766_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4788_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4772_; lean_object* v___x_4774_; 
v___x_4772_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__9));
lean_inc(v___y_4750_);
if (v_isShared_4771_ == 0)
{
lean_ctor_set_tag(v___x_4770_, 2);
lean_ctor_set(v___x_4770_, 1, v___x_4772_);
lean_ctor_set(v___x_4770_, 0, v___y_4750_);
v___x_4774_ = v___x_4770_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___y_4750_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
lean_inc(v___y_4756_);
lean_inc(v___y_4759_);
lean_inc(v___y_4750_);
v___x_4775_ = l_Lean_Syntax_node4(v___y_4750_, v___y_4759_, v___y_4756_, v___x_4765_, v___x_4774_, v___y_4747_);
lean_inc(v___y_4752_);
v___x_4776_ = l_Lean_Syntax_node4(v___y_4750_, v___y_4752_, v___y_4762_, v___y_4748_, v___y_4749_, v___x_4775_);
v___x_4777_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4778_ = l_Lean_SourceInfo_fromRef(v_tk_4745_, v___x_4742_);
lean_dec(v_tk_4745_);
v___x_4779_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__10));
v___x_4780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4778_);
lean_ctor_set(v___x_4780_, 1, v___x_4779_);
if (lean_obj_tag(v___y_4753_) == 1)
{
lean_object* v_val_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v_val_4781_ = lean_ctor_get(v___y_4753_, 0);
lean_inc(v_val_4781_);
lean_dec_ref_known(v___y_4753_, 1);
v___x_4782_ = l_Lean_SourceInfo_fromRef(v_val_4781_, v___x_4742_);
lean_dec(v_val_4781_);
v___x_4783_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_4784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4782_);
lean_ctor_set(v___x_4784_, 1, v___x_4783_);
v___x_4785_ = l_Array_mkArray1___redArg(v___x_4784_);
v___y_4703_ = v___y_4756_;
v___y_4704_ = v___y_4757_;
v___y_4705_ = v_a_4767_;
v___y_4706_ = v___y_4760_;
v___y_4707_ = v___x_4776_;
v___y_4708_ = v___x_4780_;
v___y_4709_ = v___y_4754_;
v___y_4710_ = v___y_4761_;
v___y_4711_ = v___y_4755_;
v___y_4712_ = v_a_4768_;
v___y_4713_ = v___x_4777_;
v___y_4714_ = v___x_4785_;
goto v___jp_4702_;
}
else
{
lean_object* v___x_4786_; 
lean_dec(v___y_4753_);
v___x_4786_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4703_ = v___y_4756_;
v___y_4704_ = v___y_4757_;
v___y_4705_ = v_a_4767_;
v___y_4706_ = v___y_4760_;
v___y_4707_ = v___x_4776_;
v___y_4708_ = v___x_4780_;
v___y_4709_ = v___y_4754_;
v___y_4710_ = v___y_4761_;
v___y_4711_ = v___y_4755_;
v___y_4712_ = v_a_4768_;
v___y_4713_ = v___x_4777_;
v___y_4714_ = v___x_4786_;
goto v___jp_4702_;
}
}
}
}
v___jp_4789_:
{
lean_object* v_quotContext_4797_; lean_object* v_currMacroScope_4798_; lean_object* v_ref_4799_; lean_object* v___x_4800_; lean_object* v_a_4801_; lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4829_; 
v_quotContext_4797_ = lean_ctor_get(v___y_4795_, 1);
v_currMacroScope_4798_ = lean_ctor_get(v___y_4795_, 2);
v_ref_4799_ = lean_ctor_get(v___y_4795_, 5);
v___x_4800_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_ref_4799_, v___y_4795_, v___y_4796_);
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
v_a_4802_ = lean_ctor_get(v___x_4800_, 1);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4804_ = v___x_4800_;
v_isShared_4805_ = v_isSharedCheck_4829_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_inc(v_a_4801_);
lean_dec(v___x_4800_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4829_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4815_; 
v___x_4806_ = lean_unsigned_to_nat(3u);
v___x_4807_ = l_Lean_Syntax_getArg(v___y_4792_, v___x_4806_);
lean_dec(v___y_4792_);
v___x_4808_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
lean_inc(v_currMacroScope_4798_);
lean_inc(v_quotContext_4797_);
v___x_4809_ = l_Lean_addMacroScope(v_quotContext_4797_, v___x_4808_, v_currMacroScope_4798_);
v___x_4810_ = 0;
v___x_4811_ = l_Lean_mkIdentFrom(v___y_4790_, v___x_4809_, v___x_4810_);
v___x_4812_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_4813_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v_a_4801_);
if (v_isShared_4805_ == 0)
{
lean_ctor_set_tag(v___x_4804_, 2);
lean_ctor_set(v___x_4804_, 1, v___x_4813_);
v___x_4815_ = v___x_4804_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4801_);
lean_ctor_set(v_reuseFailAlloc_4828_, 1, v___x_4813_);
v___x_4815_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4816_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4817_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v_a_4801_, 2);
v___x_4818_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4818_, 0, v_a_4801_);
lean_ctor_set(v___x_4818_, 1, v___x_4816_);
lean_ctor_set(v___x_4818_, 2, v___x_4817_);
v___x_4819_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc_ref(v___x_4818_);
v___x_4820_ = l_Lean_Syntax_node1(v_a_4801_, v___x_4819_, v___x_4818_);
if (lean_obj_tag(v_t_x3f_4794_) == 1)
{
lean_object* v_val_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v_val_4821_ = lean_ctor_get(v_t_x3f_4794_, 0);
lean_inc(v_val_4821_);
lean_dec_ref_known(v_t_x3f_4794_, 1);
v___x_4822_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4823_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v_a_4801_, 2);
v___x_4824_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4824_, 0, v_a_4801_);
lean_ctor_set(v___x_4824_, 1, v___x_4823_);
v___x_4825_ = l_Lean_Syntax_node2(v_a_4801_, v___x_4822_, v___x_4824_, v_val_4821_);
v___x_4826_ = l_Array_mkArray1___redArg(v___x_4825_);
v___y_4747_ = v___x_4807_;
v___y_4748_ = v___x_4818_;
v___y_4749_ = v___x_4820_;
v___y_4750_ = v_a_4801_;
v___y_4751_ = v_a_4802_;
v___y_4752_ = v___x_4812_;
v___y_4753_ = v___y_4793_;
v___y_4754_ = v___x_4810_;
v___y_4755_ = v___x_4816_;
v___y_4756_ = v___x_4811_;
v___y_4757_ = v___y_4790_;
v___y_4758_ = v___y_4795_;
v___y_4759_ = v___y_4791_;
v___y_4760_ = v___x_4817_;
v___y_4761_ = v_ref_4799_;
v___y_4762_ = v___x_4815_;
v___y_4763_ = v___x_4826_;
goto v___jp_4746_;
}
else
{
lean_object* v___x_4827_; 
lean_dec(v_t_x3f_4794_);
v___x_4827_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4747_ = v___x_4807_;
v___y_4748_ = v___x_4818_;
v___y_4749_ = v___x_4820_;
v___y_4750_ = v_a_4801_;
v___y_4751_ = v_a_4802_;
v___y_4752_ = v___x_4812_;
v___y_4753_ = v___y_4793_;
v___y_4754_ = v___x_4810_;
v___y_4755_ = v___x_4816_;
v___y_4756_ = v___x_4811_;
v___y_4757_ = v___y_4790_;
v___y_4758_ = v___y_4795_;
v___y_4759_ = v___y_4791_;
v___y_4760_ = v___x_4817_;
v___y_4761_ = v_ref_4799_;
v___y_4762_ = v___x_4815_;
v___y_4763_ = v___x_4827_;
goto v___jp_4746_;
}
}
}
}
v___jp_4831_:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; uint8_t v___x_4838_; 
v___x_4835_ = lean_unsigned_to_nat(2u);
v___x_4836_ = l_Lean_Syntax_getArg(v_stx_4699_, v___x_4835_);
lean_dec(v_stx_4699_);
v___x_4837_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_4836_);
v___x_4838_ = l_Lean_Syntax_isOfKind(v___x_4836_, v___x_4837_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; 
lean_dec(v___x_4836_);
lean_dec(v_mutTk_x3f_4832_);
lean_dec(v_tk_4745_);
v___x_4839_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4834_);
return v___x_4839_;
}
else
{
lean_object* v___x_4840_; lean_object* v___x_4841_; uint8_t v___x_4842_; 
v___x_4840_ = l_Lean_Syntax_getArg(v___x_4836_, v___x_4744_);
v___x_4841_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4840_);
v___x_4842_ = l_Lean_Syntax_isOfKind(v___x_4840_, v___x_4841_);
if (v___x_4842_ == 0)
{
lean_object* v___x_4843_; 
lean_dec(v___x_4840_);
lean_dec(v___x_4836_);
lean_dec(v_mutTk_x3f_4832_);
lean_dec(v_tk_4745_);
v___x_4843_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4834_);
return v___x_4843_;
}
else
{
lean_object* v___x_4844_; uint8_t v___x_4845_; 
v___x_4844_ = l_Lean_Syntax_getArg(v___x_4836_, v___x_4830_);
v___x_4845_ = l_Lean_Syntax_isNone(v___x_4844_);
if (v___x_4845_ == 0)
{
uint8_t v___x_4846_; 
lean_inc(v___x_4844_);
v___x_4846_ = l_Lean_Syntax_matchesNull(v___x_4844_, v___x_4830_);
if (v___x_4846_ == 0)
{
lean_object* v___x_4847_; 
lean_dec(v___x_4844_);
lean_dec(v___x_4840_);
lean_dec(v___x_4836_);
lean_dec(v_mutTk_x3f_4832_);
lean_dec(v_tk_4745_);
v___x_4847_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4834_);
return v___x_4847_;
}
else
{
lean_object* v___x_4848_; lean_object* v___x_4849_; uint8_t v___x_4850_; 
v___x_4848_ = l_Lean_Syntax_getArg(v___x_4844_, v___x_4744_);
lean_dec(v___x_4844_);
v___x_4849_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4848_);
v___x_4850_ = l_Lean_Syntax_isOfKind(v___x_4848_, v___x_4849_);
if (v___x_4850_ == 0)
{
lean_object* v___x_4851_; 
lean_dec(v___x_4848_);
lean_dec(v___x_4840_);
lean_dec(v___x_4836_);
lean_dec(v_mutTk_x3f_4832_);
lean_dec(v_tk_4745_);
v___x_4851_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4834_);
return v___x_4851_;
}
else
{
lean_object* v_t_x3f_4852_; lean_object* v___x_4853_; 
v_t_x3f_4852_ = l_Lean_Syntax_getArg(v___x_4848_, v___x_4830_);
lean_dec(v___x_4848_);
v___x_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4853_, 0, v_t_x3f_4852_);
v___y_4790_ = v___x_4840_;
v___y_4791_ = v___x_4837_;
v___y_4792_ = v___x_4836_;
v___y_4793_ = v_mutTk_x3f_4832_;
v_t_x3f_4794_ = v___x_4853_;
v___y_4795_ = v___y_4833_;
v___y_4796_ = v___y_4834_;
goto v___jp_4789_;
}
}
}
else
{
lean_object* v___x_4854_; 
lean_dec(v___x_4844_);
v___x_4854_ = lean_box(0);
v___y_4790_ = v___x_4840_;
v___y_4791_ = v___x_4837_;
v___y_4792_ = v___x_4836_;
v___y_4793_ = v_mutTk_x3f_4832_;
v_t_x3f_4794_ = v___x_4854_;
v___y_4795_ = v___y_4833_;
v___y_4796_ = v___y_4834_;
goto v___jp_4789_;
}
}
}
}
}
v___jp_4702_:
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
lean_inc_ref_n(v___y_4706_, 3);
v___x_4715_ = l_Array_append___redArg(v___y_4706_, v___y_4714_);
lean_dec_ref(v___y_4714_);
lean_inc_n(v___y_4711_, 5);
lean_inc_n(v___y_4705_, 5);
v___x_4716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4716_, 0, v___y_4705_);
lean_ctor_set(v___x_4716_, 1, v___y_4711_);
lean_ctor_set(v___x_4716_, 2, v___x_4715_);
v___x_4717_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_4718_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
v___x_4719_ = l_Lean_Syntax_node1(v___y_4705_, v___x_4718_, v___y_4704_);
v___x_4720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4720_, 0, v___y_4705_);
lean_ctor_set(v___x_4720_, 1, v___y_4711_);
lean_ctor_set(v___x_4720_, 2, v___y_4706_);
v___x_4721_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___y_4705_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
lean_inc_ref(v___x_4720_);
v___x_4723_ = l_Lean_Syntax_node5(v___y_4705_, v___x_4717_, v___x_4719_, v___x_4720_, v___x_4720_, v___x_4722_, v___y_4703_);
lean_inc(v___y_4713_);
v___x_4724_ = l_Lean_Syntax_node3(v___y_4705_, v___y_4713_, v___y_4708_, v___x_4716_, v___x_4723_);
v___x_4725_ = l_Lean_SourceInfo_fromRef(v___y_4710_, v___y_4709_);
v___x_4726_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_4727_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
lean_inc_n(v___x_4725_, 8);
v___x_4728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4725_);
lean_ctor_set(v___x_4728_, 1, v___x_4727_);
v___x_4729_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_4730_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_4731_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4725_);
lean_ctor_set(v___x_4732_, 1, v___x_4731_);
v___x_4733_ = l_Lean_Syntax_node1(v___x_4725_, v___y_4711_, v___x_4732_);
v___x_4734_ = l_Lean_Syntax_node2(v___x_4725_, v___x_4730_, v___y_4707_, v___x_4733_);
v___x_4735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4725_);
lean_ctor_set(v___x_4735_, 1, v___y_4711_);
lean_ctor_set(v___x_4735_, 2, v___y_4706_);
v___x_4736_ = l_Lean_Syntax_node2(v___x_4725_, v___x_4730_, v___x_4724_, v___x_4735_);
v___x_4737_ = l_Lean_Syntax_node2(v___x_4725_, v___y_4711_, v___x_4734_, v___x_4736_);
v___x_4738_ = l_Lean_Syntax_node1(v___x_4725_, v___x_4729_, v___x_4737_);
v___x_4739_ = l_Lean_Syntax_node2(v___x_4725_, v___x_4726_, v___x_4728_, v___x_4738_);
v___x_4740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
lean_ctor_set(v___x_4740_, 1, v___y_4712_);
return v___x_4740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___boxed(lean_object* v_stx_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Lean_Elab_Do_expandDoErasedArrow(v_stx_4862_, v_a_4863_, v_a_4864_);
lean_dec_ref(v_a_4863_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1(){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4873_ = l_Lean_Elab_macroAttribute;
v___x_4874_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
v___x_4875_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1));
v___x_4876_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoErasedArrow___boxed), 3, 0);
v___x_4877_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4873_, v___x_4874_, v___x_4875_, v___x_4876_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___boxed(lean_object* v_a_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1();
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4886_, lean_object* v_dec_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v___x_4896_; uint8_t v___x_4897_; 
v___x_4896_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
lean_inc(v_stx_4886_);
v___x_4897_ = l_Lean_Syntax_isOfKind(v_stx_4886_, v___x_4896_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4898_; 
lean_dec_ref(v_dec_4887_);
lean_dec(v_stx_4886_);
v___x_4898_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4898_;
}
else
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; uint8_t v___x_4902_; 
v___x_4899_ = lean_unsigned_to_nat(1u);
v___x_4900_ = l_Lean_Syntax_getArg(v_stx_4886_, v___x_4899_);
v___x_4901_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v___x_4900_);
v___x_4902_ = l_Lean_Syntax_isOfKind(v___x_4900_, v___x_4901_);
if (v___x_4902_ == 0)
{
lean_object* v___x_4903_; 
lean_dec(v___x_4900_);
lean_dec_ref(v_dec_4887_);
lean_dec(v_stx_4886_);
v___x_4903_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4903_;
}
else
{
lean_object* v___x_4904_; lean_object* v_decl_4905_; lean_object* v___x_4906_; uint8_t v___x_4907_; 
v___x_4904_ = lean_unsigned_to_nat(2u);
v_decl_4905_ = l_Lean_Syntax_getArg(v_stx_4886_, v___x_4904_);
v___x_4906_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4905_);
v___x_4907_ = l_Lean_Syntax_isOfKind(v_decl_4905_, v___x_4906_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; 
lean_dec(v_decl_4905_);
lean_dec(v___x_4900_);
lean_dec_ref(v_dec_4887_);
lean_dec(v_stx_4886_);
v___x_4908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4908_;
}
else
{
lean_object* v___x_4909_; lean_object* v_tk_4910_; uint8_t v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
v___x_4909_ = lean_unsigned_to_nat(0u);
v_tk_4910_ = l_Lean_Syntax_getArg(v_stx_4886_, v___x_4909_);
lean_dec(v_stx_4886_);
v___x_4911_ = 0;
v___x_4912_ = lean_box(0);
v___x_4913_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4913_, 0, v___x_4912_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*1, v___x_4907_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*1 + 1, v___x_4911_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*1 + 2, v___x_4911_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*1 + 3, v___x_4911_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*1 + 4, v___x_4911_);
v___x_4914_ = l_Lean_Elab_Term_mkLetConfig(v___x_4900_, v___x_4913_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4914_, 1);
v___x_4916_ = lean_box(1);
v___x_4917_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4915_, v___x_4916_, v_decl_4905_, v_tk_4910_, v_dec_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
return v___x_4917_;
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
lean_dec(v_tk_4910_);
lean_dec(v_decl_4905_);
lean_dec_ref(v_dec_4887_);
v_a_4918_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4914_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4914_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4926_, lean_object* v_dec_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Lean_Elab_Do_elabDoHave(v_stx_4926_, v_dec_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4944_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4945_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
v___x_4946_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4947_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4948_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4944_, v___x_4945_, v___x_4946_, v___x_4947_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4953_, lean_object* v___x_4954_, lean_object* v___x_4955_, lean_object* v___x_4956_, lean_object* v_decls_4957_, lean_object* v_a_4958_, uint8_t v___x_4959_, lean_object* v_body_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v_ref_4969_; uint8_t v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v_ref_4969_ = lean_ctor_get(v___y_4966_, 2);
v___x_4970_ = 0;
v___x_4971_ = l_Lean_SourceInfo_fromRef(v_ref_4969_, v___x_4970_);
v___x_4972_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4973_ = l_Lean_Name_mkStr4(v___x_4953_, v___x_4954_, v___x_4955_, v___x_4972_);
v___x_4974_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4971_, 4);
v___x_4975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4971_);
lean_ctor_set(v___x_4975_, 1, v___x_4974_);
v___x_4976_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4971_);
lean_ctor_set(v___x_4977_, 1, v___x_4976_);
v___x_4978_ = l_Lean_Syntax_node2(v___x_4971_, v___x_4956_, v___x_4975_, v___x_4977_);
v___x_4979_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4971_);
lean_ctor_set(v___x_4980_, 1, v___x_4979_);
v___x_4981_ = l_Lean_Syntax_node4(v___x_4971_, v___x_4973_, v___x_4978_, v_decls_4957_, v___x_4980_, v_body_4960_);
v___x_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4982_, 0, v_a_4958_);
v___x_4983_ = l_Lean_Elab_Term_elabTerm(v___x_4981_, v___x_4982_, v___x_4959_, v___x_4959_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4984_, lean_object* v___x_4985_, lean_object* v___x_4986_, lean_object* v___x_4987_, lean_object* v_decls_4988_, lean_object* v_a_4989_, lean_object* v___x_4990_, lean_object* v_body_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
uint8_t v___x_4418__boxed_5000_; lean_object* v_res_5001_; 
v___x_4418__boxed_5000_ = lean_unbox(v___x_4990_);
v_res_5001_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4984_, v___x_4985_, v___x_4986_, v___x_4987_, v_decls_4988_, v_a_4989_, v___x_4418__boxed_5000_, v_body_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec_ref(v___y_4992_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_5002_, lean_object* v_a_5003_){
_start:
{
if (lean_obj_tag(v_a_5002_) == 0)
{
lean_object* v___x_5004_; 
v___x_5004_ = l_List_reverse___redArg(v_a_5003_);
return v___x_5004_;
}
else
{
lean_object* v_head_5005_; lean_object* v_tail_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5015_; 
v_head_5005_ = lean_ctor_get(v_a_5002_, 0);
v_tail_5006_ = lean_ctor_get(v_a_5002_, 1);
v_isSharedCheck_5015_ = !lean_is_exclusive(v_a_5002_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5008_ = v_a_5002_;
v_isShared_5009_ = v_isSharedCheck_5015_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_tail_5006_);
lean_inc(v_head_5005_);
lean_dec(v_a_5002_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5015_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5010_ = l_Lean_MessageData_ofSyntax(v_head_5005_);
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 1, v_a_5003_);
lean_ctor_set(v___x_5008_, 0, v___x_5010_);
v___x_5012_ = v___x_5008_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5010_);
lean_ctor_set(v_reuseFailAlloc_5014_, 1, v_a_5003_);
v___x_5012_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
v_a_5002_ = v_tail_5006_;
v_a_5003_ = v___x_5012_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5032_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_5033_ = l_Lean_stringToMessageData(v___x_5032_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_5034_, lean_object* v_dec_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_){
_start:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; uint8_t v___x_5048_; 
v___x_5044_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_5045_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_5046_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_5047_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_5034_);
v___x_5048_ = l_Lean_Syntax_isOfKind(v_stx_5034_, v___x_5047_);
if (v___x_5048_ == 0)
{
lean_object* v___x_5049_; 
lean_dec_ref(v_dec_5035_);
lean_dec(v_stx_5034_);
v___x_5049_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5049_;
}
else
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; uint8_t v___x_5053_; 
v___x_5050_ = lean_unsigned_to_nat(0u);
v___x_5051_ = l_Lean_Syntax_getArg(v_stx_5034_, v___x_5050_);
v___x_5052_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_5051_);
v___x_5053_ = l_Lean_Syntax_isOfKind(v___x_5051_, v___x_5052_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; 
lean_dec(v___x_5051_);
lean_dec_ref(v_dec_5035_);
lean_dec(v_stx_5034_);
v___x_5054_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5054_;
}
else
{
lean_object* v___x_5055_; lean_object* v_decls_5056_; lean_object* v___x_5057_; uint8_t v___x_5058_; 
v___x_5055_ = lean_unsigned_to_nat(1u);
v_decls_5056_ = l_Lean_Syntax_getArg(v_stx_5034_, v___x_5055_);
lean_dec(v_stx_5034_);
v___x_5057_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_5056_);
v___x_5058_ = l_Lean_Syntax_isOfKind(v_decls_5056_, v___x_5057_);
if (v___x_5058_ == 0)
{
lean_object* v___x_5059_; 
lean_dec(v_decls_5056_);
lean_dec(v___x_5051_);
lean_dec_ref(v_dec_5035_);
v___x_5059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5059_;
}
else
{
lean_object* v_tk_5060_; lean_object* v___x_5061_; 
v_tk_5060_ = l_Lean_Syntax_getArg(v___x_5051_, v___x_5050_);
lean_dec(v___x_5051_);
v___x_5061_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_5035_, v_tk_5060_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
lean_dec(v_tk_5060_);
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v_a_5062_; lean_object* v___x_5063_; 
v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
lean_inc(v_a_5062_);
lean_dec_ref_known(v___x_5061_, 1);
lean_inc(v_decls_5056_);
v___x_5063_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_5056_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v_a_5064_; lean_object* v_doBlockResultType_5065_; lean_object* v___x_5066_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5063_, 1);
v_doBlockResultType_5065_ = lean_ctor_get(v_a_5036_, 3);
lean_inc_ref(v_doBlockResultType_5065_);
v___x_5066_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_5065_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v_a_5067_; lean_object* v___x_5068_; lean_object* v___f_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_5066_, 1);
v___x_5068_ = lean_box(v___x_5058_);
v___f_5069_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_5069_, 0, v___x_5044_);
lean_closure_set(v___f_5069_, 1, v___x_5045_);
lean_closure_set(v___f_5069_, 2, v___x_5046_);
lean_closure_set(v___f_5069_, 3, v___x_5052_);
lean_closure_set(v___f_5069_, 4, v_decls_5056_);
lean_closure_set(v___f_5069_, 5, v_a_5067_);
lean_closure_set(v___f_5069_, 6, v___x_5068_);
v___x_5070_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_5071_ = lean_array_to_list(v_a_5064_);
v___x_5072_ = lean_box(0);
v___x_5073_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_5071_, v___x_5072_);
v___x_5074_ = l_Lean_MessageData_ofList(v___x_5073_);
v___x_5075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5075_, 0, v___x_5070_);
lean_ctor_set(v___x_5075_, 1, v___x_5074_);
v___x_5076_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_5076_, 0, v_a_5062_);
v___x_5077_ = lean_box(0);
v___x_5078_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_5075_, v___x_5076_, v___f_5069_, v___x_5077_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
return v___x_5078_;
}
else
{
lean_dec(v_a_5064_);
lean_dec(v_a_5062_);
lean_dec(v_decls_5056_);
return v___x_5066_;
}
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
lean_dec(v_a_5062_);
lean_dec(v_decls_5056_);
v_a_5079_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_5063_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5063_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
lean_dec(v_decls_5056_);
v_a_5087_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5061_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5061_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_5095_, lean_object* v_dec_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_5095_, v_dec_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_);
lean_dec(v_a_5103_);
lean_dec_ref(v_a_5102_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec_ref(v_a_5097_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
v___x_5113_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5114_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_5115_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_5116_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_5117_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5113_, v___x_5114_, v___x_5115_, v___x_5116_);
return v___x_5117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_5126_, lean_object* v_dec_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_){
_start:
{
lean_object* v___y_5137_; lean_object* v___y_5138_; lean_object* v___y_5139_; lean_object* v___y_5140_; lean_object* v___y_5141_; lean_object* v___y_5142_; lean_object* v___y_5143_; uint8_t v___y_5144_; lean_object* v___y_5145_; lean_object* v___y_5146_; lean_object* v___y_5147_; lean_object* v___y_5148_; lean_object* v___y_5149_; lean_object* v___y_5150_; lean_object* v___y_5151_; lean_object* v___y_5152_; lean_object* v___y_5153_; lean_object* v___x_5169_; uint8_t v___x_5170_; 
v___x_5169_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
lean_inc(v_stx_5126_);
v___x_5170_ = l_Lean_Syntax_isOfKind(v_stx_5126_, v___x_5169_);
if (v___x_5170_ == 0)
{
lean_object* v___x_5171_; 
lean_dec_ref(v_dec_5127_);
lean_dec(v_stx_5126_);
v___x_5171_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5171_;
}
else
{
lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; uint8_t v___x_5175_; 
v___x_5172_ = lean_unsigned_to_nat(0u);
v___x_5173_ = l_Lean_Syntax_getArg(v_stx_5126_, v___x_5172_);
lean_dec(v_stx_5126_);
v___x_5174_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_5173_);
v___x_5175_ = l_Lean_Syntax_isOfKind(v___x_5173_, v___x_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; uint8_t v___x_5177_; 
v___x_5176_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5173_);
v___x_5177_ = l_Lean_Syntax_isOfKind(v___x_5173_, v___x_5176_);
if (v___x_5177_ == 0)
{
lean_object* v___x_5178_; 
lean_dec(v___x_5173_);
lean_dec_ref(v_dec_5127_);
v___x_5178_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5178_;
}
else
{
lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v_decl_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v___x_5179_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5180_ = lean_unsigned_to_nat(1u);
v___x_5181_ = lean_mk_empty_array_with_capacity(v___x_5180_);
v___x_5182_ = lean_array_push(v___x_5181_, v___x_5173_);
v___x_5183_ = lean_box(2);
v_decl_5184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5184_, 0, v___x_5183_);
lean_ctor_set(v_decl_5184_, 1, v___x_5179_);
lean_ctor_set(v_decl_5184_, 2, v___x_5182_);
v___x_5185_ = lean_box(0);
v___x_5186_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5186_, 0, v___x_5185_);
lean_ctor_set_uint8(v___x_5186_, sizeof(void*)*1, v___x_5175_);
lean_ctor_set_uint8(v___x_5186_, sizeof(void*)*1 + 1, v___x_5175_);
lean_ctor_set_uint8(v___x_5186_, sizeof(void*)*1 + 2, v___x_5175_);
lean_ctor_set_uint8(v___x_5186_, sizeof(void*)*1 + 3, v___x_5175_);
lean_ctor_set_uint8(v___x_5186_, sizeof(void*)*1 + 4, v___x_5175_);
v___x_5187_ = lean_box(2);
lean_inc_ref(v_decl_5184_);
v___x_5188_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5186_, v___x_5187_, v_decl_5184_, v_decl_5184_, v_dec_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_);
return v___x_5188_;
}
}
else
{
lean_object* v___x_5189_; lean_object* v___x_5190_; uint8_t v___x_5191_; 
v___x_5189_ = l_Lean_Syntax_getArg(v___x_5173_, v___x_5172_);
v___x_5190_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5189_);
v___x_5191_ = l_Lean_Syntax_isOfKind(v___x_5189_, v___x_5190_);
if (v___x_5191_ == 0)
{
lean_object* v___x_5192_; 
lean_dec(v___x_5189_);
lean_dec(v___x_5173_);
lean_dec_ref(v_dec_5127_);
v___x_5192_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5192_;
}
else
{
lean_object* v___x_5193_; lean_object* v_xType_x3f_5195_; lean_object* v___y_5196_; lean_object* v___y_5197_; lean_object* v___y_5198_; lean_object* v___y_5199_; lean_object* v___y_5200_; lean_object* v___y_5201_; lean_object* v___y_5202_; lean_object* v___x_5222_; uint8_t v___x_5223_; 
v___x_5193_ = l_Lean_Syntax_getArg(v___x_5189_, v___x_5172_);
lean_dec(v___x_5189_);
v___x_5222_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5193_);
v___x_5223_ = l_Lean_Syntax_isOfKind(v___x_5193_, v___x_5222_);
if (v___x_5223_ == 0)
{
lean_object* v___x_5224_; 
lean_dec(v___x_5193_);
lean_dec(v___x_5173_);
lean_dec_ref(v_dec_5127_);
v___x_5224_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5224_;
}
else
{
lean_object* v___x_5225_; lean_object* v___x_5226_; uint8_t v___x_5227_; 
v___x_5225_ = lean_unsigned_to_nat(1u);
v___x_5226_ = l_Lean_Syntax_getArg(v___x_5173_, v___x_5225_);
v___x_5227_ = l_Lean_Syntax_matchesNull(v___x_5226_, v___x_5172_);
if (v___x_5227_ == 0)
{
lean_object* v___x_5228_; 
lean_dec(v___x_5193_);
lean_dec(v___x_5173_);
lean_dec_ref(v_dec_5127_);
v___x_5228_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5228_;
}
else
{
lean_object* v___x_5229_; lean_object* v___x_5230_; uint8_t v___x_5231_; 
v___x_5229_ = lean_unsigned_to_nat(2u);
v___x_5230_ = l_Lean_Syntax_getArg(v___x_5173_, v___x_5229_);
v___x_5231_ = l_Lean_Syntax_isNone(v___x_5230_);
if (v___x_5231_ == 0)
{
uint8_t v___x_5232_; 
lean_inc(v___x_5230_);
v___x_5232_ = l_Lean_Syntax_matchesNull(v___x_5230_, v___x_5225_);
if (v___x_5232_ == 0)
{
lean_object* v___x_5233_; 
lean_dec(v___x_5230_);
lean_dec(v___x_5193_);
lean_dec(v___x_5173_);
lean_dec_ref(v_dec_5127_);
v___x_5233_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5233_;
}
else
{
lean_object* v___x_5234_; lean_object* v___x_5235_; uint8_t v___x_5236_; 
v___x_5234_ = l_Lean_Syntax_getArg(v___x_5230_, v___x_5172_);
lean_dec(v___x_5230_);
v___x_5235_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5234_);
v___x_5236_ = l_Lean_Syntax_isOfKind(v___x_5234_, v___x_5235_);
if (v___x_5236_ == 0)
{
lean_object* v___x_5237_; 
lean_dec(v___x_5234_);
lean_dec(v___x_5193_);
lean_dec(v___x_5173_);
lean_dec_ref(v_dec_5127_);
v___x_5237_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5237_;
}
else
{
lean_object* v_xType_x3f_5238_; lean_object* v___x_5239_; 
v_xType_x3f_5238_ = l_Lean_Syntax_getArg(v___x_5234_, v___x_5225_);
lean_dec(v___x_5234_);
v___x_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5239_, 0, v_xType_x3f_5238_);
v_xType_x3f_5195_ = v___x_5239_;
v___y_5196_ = v_a_5128_;
v___y_5197_ = v_a_5129_;
v___y_5198_ = v_a_5130_;
v___y_5199_ = v_a_5131_;
v___y_5200_ = v_a_5132_;
v___y_5201_ = v_a_5133_;
v___y_5202_ = v_a_5134_;
goto v___jp_5194_;
}
}
}
else
{
lean_object* v___x_5240_; 
lean_dec(v___x_5230_);
v___x_5240_ = lean_box(0);
v_xType_x3f_5195_ = v___x_5240_;
v___y_5196_ = v_a_5128_;
v___y_5197_ = v_a_5129_;
v___y_5198_ = v_a_5130_;
v___y_5199_ = v_a_5131_;
v___y_5200_ = v_a_5132_;
v___y_5201_ = v_a_5133_;
v___y_5202_ = v_a_5134_;
goto v___jp_5194_;
}
}
}
v___jp_5194_:
{
lean_object* v_ref_5203_; lean_object* v___x_5204_; lean_object* v_tk_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; uint8_t v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; 
v_ref_5203_ = lean_ctor_get(v___y_5201_, 2);
v___x_5204_ = lean_unsigned_to_nat(3u);
v_tk_5205_ = l_Lean_Syntax_getArg(v___x_5173_, v___x_5204_);
v___x_5206_ = lean_unsigned_to_nat(4u);
v___x_5207_ = l_Lean_Syntax_getArg(v___x_5173_, v___x_5206_);
lean_dec(v___x_5173_);
v___x_5208_ = 0;
v___x_5209_ = l_Lean_SourceInfo_fromRef(v_ref_5203_, v___x_5208_);
v___x_5210_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5209_, 2);
v___x_5211_ = l_Lean_Syntax_node1(v___x_5209_, v___x_5190_, v___x_5193_);
v___x_5212_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5213_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5214_, 0, v___x_5209_);
lean_ctor_set(v___x_5214_, 1, v___x_5212_);
lean_ctor_set(v___x_5214_, 2, v___x_5213_);
if (lean_obj_tag(v_xType_x3f_5195_) == 1)
{
lean_object* v_val_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; 
v_val_5215_ = lean_ctor_get(v_xType_x3f_5195_, 0);
lean_inc(v_val_5215_);
lean_dec_ref_known(v_xType_x3f_5195_, 1);
v___x_5216_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5217_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5209_, 2);
v___x_5218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5218_, 0, v___x_5209_);
lean_ctor_set(v___x_5218_, 1, v___x_5217_);
v___x_5219_ = l_Lean_Syntax_node2(v___x_5209_, v___x_5216_, v___x_5218_, v_val_5215_);
v___x_5220_ = l_Array_mkArray1___redArg(v___x_5219_);
v___y_5137_ = v___y_5201_;
v___y_5138_ = v___x_5207_;
v___y_5139_ = v___y_5196_;
v___y_5140_ = v___x_5214_;
v___y_5141_ = v___y_5200_;
v___y_5142_ = v___x_5211_;
v___y_5143_ = v___y_5197_;
v___y_5144_ = v___x_5208_;
v___y_5145_ = v___x_5213_;
v___y_5146_ = v_tk_5205_;
v___y_5147_ = v___y_5199_;
v___y_5148_ = v___x_5212_;
v___y_5149_ = v___x_5209_;
v___y_5150_ = v___x_5210_;
v___y_5151_ = v___y_5202_;
v___y_5152_ = v___y_5198_;
v___y_5153_ = v___x_5220_;
goto v___jp_5136_;
}
else
{
lean_object* v___x_5221_; 
lean_dec(v_xType_x3f_5195_);
v___x_5221_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_5137_ = v___y_5201_;
v___y_5138_ = v___x_5207_;
v___y_5139_ = v___y_5196_;
v___y_5140_ = v___x_5214_;
v___y_5141_ = v___y_5200_;
v___y_5142_ = v___x_5211_;
v___y_5143_ = v___y_5197_;
v___y_5144_ = v___x_5208_;
v___y_5145_ = v___x_5213_;
v___y_5146_ = v_tk_5205_;
v___y_5147_ = v___y_5199_;
v___y_5148_ = v___x_5212_;
v___y_5149_ = v___x_5209_;
v___y_5150_ = v___x_5210_;
v___y_5151_ = v___y_5202_;
v___y_5152_ = v___y_5198_;
v___y_5153_ = v___x_5221_;
goto v___jp_5136_;
}
}
}
}
}
v___jp_5136_:
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; 
lean_inc_ref(v___y_5145_);
v___x_5154_ = l_Array_append___redArg(v___y_5145_, v___y_5153_);
lean_dec_ref(v___y_5153_);
lean_inc(v___y_5148_);
lean_inc_n(v___y_5149_, 2);
v___x_5155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5155_, 0, v___y_5149_);
lean_ctor_set(v___x_5155_, 1, v___y_5148_);
lean_ctor_set(v___x_5155_, 2, v___x_5154_);
v___x_5156_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5157_, 0, v___y_5149_);
lean_ctor_set(v___x_5157_, 1, v___x_5156_);
lean_inc(v___y_5150_);
v___x_5158_ = l_Lean_Syntax_node5(v___y_5149_, v___y_5150_, v___y_5142_, v___y_5140_, v___x_5155_, v___x_5157_, v___y_5138_);
v___x_5159_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5160_ = lean_unsigned_to_nat(1u);
v___x_5161_ = lean_mk_empty_array_with_capacity(v___x_5160_);
v___x_5162_ = lean_array_push(v___x_5161_, v___x_5158_);
v___x_5163_ = lean_box(2);
v___x_5164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5163_);
lean_ctor_set(v___x_5164_, 1, v___x_5159_);
lean_ctor_set(v___x_5164_, 2, v___x_5162_);
v___x_5165_ = lean_box(0);
v___x_5166_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5166_, 0, v___x_5165_);
lean_ctor_set_uint8(v___x_5166_, sizeof(void*)*1, v___y_5144_);
lean_ctor_set_uint8(v___x_5166_, sizeof(void*)*1 + 1, v___y_5144_);
lean_ctor_set_uint8(v___x_5166_, sizeof(void*)*1 + 2, v___y_5144_);
lean_ctor_set_uint8(v___x_5166_, sizeof(void*)*1 + 3, v___y_5144_);
lean_ctor_set_uint8(v___x_5166_, sizeof(void*)*1 + 4, v___y_5144_);
v___x_5167_ = lean_box(2);
v___x_5168_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5166_, v___x_5167_, v___x_5164_, v___y_5146_, v_dec_5127_, v___y_5139_, v___y_5143_, v___y_5152_, v___y_5147_, v___y_5141_, v___y_5137_, v___y_5151_);
return v___x_5168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5241_, lean_object* v_dec_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5241_, v_dec_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_);
lean_dec(v_a_5249_);
lean_dec_ref(v_a_5248_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec_ref(v_a_5243_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; 
v___x_5259_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5260_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_5261_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5262_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5263_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5259_, v___x_5260_, v___x_5261_, v___x_5262_);
return v___x_5263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
uint8_t v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5275_ = 0;
v___x_5276_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5266_, v___x_5275_);
v___x_5277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5276_);
return v___x_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec(v_____do__lift_5278_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5288_, size_t v_sz_5289_, size_t v_i_5290_, lean_object* v_b_5291_, lean_object* v___y_5292_){
_start:
{
uint8_t v___x_5294_; 
v___x_5294_ = lean_usize_dec_lt(v_i_5290_, v_sz_5289_);
if (v___x_5294_ == 0)
{
lean_object* v___x_5295_; 
v___x_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5295_, 0, v_b_5291_);
return v___x_5295_;
}
else
{
lean_object* v_ref_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v_a_5299_; uint8_t v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; size_t v___x_5333_; size_t v___x_5334_; 
v_ref_5296_ = lean_ctor_get(v___y_5292_, 2);
v___x_5297_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5298_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5299_ = lean_array_uget_borrowed(v_as_5288_, v_i_5290_);
v___x_5300_ = 0;
v___x_5301_ = l_Lean_SourceInfo_fromRef(v_ref_5296_, v___x_5300_);
v___x_5302_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5303_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5304_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5305_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5301_, 17);
v___x_5306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5301_);
lean_ctor_set(v___x_5306_, 1, v___x_5305_);
v___x_5307_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5301_);
lean_ctor_set(v___x_5308_, 1, v___x_5307_);
v___x_5309_ = l_Lean_Syntax_node1(v___x_5301_, v___x_5302_, v___x_5308_);
v___x_5310_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5301_);
lean_ctor_set(v___x_5311_, 1, v___x_5302_);
lean_ctor_set(v___x_5311_, 2, v___x_5310_);
lean_inc_ref_n(v___x_5311_, 3);
v___x_5312_ = l_Lean_Syntax_node1(v___x_5301_, v___x_5297_, v___x_5311_);
v___x_5313_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5314_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5315_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5299_, 2);
v___x_5316_ = l_Lean_Syntax_node1(v___x_5301_, v___x_5315_, v_a_5299_);
v___x_5317_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5301_);
lean_ctor_set(v___x_5318_, 1, v___x_5317_);
v___x_5319_ = l_Lean_Syntax_node5(v___x_5301_, v___x_5314_, v___x_5316_, v___x_5311_, v___x_5311_, v___x_5318_, v_a_5299_);
v___x_5320_ = l_Lean_Syntax_node1(v___x_5301_, v___x_5313_, v___x_5319_);
v___x_5321_ = l_Lean_Syntax_node4(v___x_5301_, v___x_5304_, v___x_5306_, v___x_5309_, v___x_5312_, v___x_5320_);
v___x_5322_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5323_, 0, v___x_5301_);
lean_ctor_set(v___x_5323_, 1, v___x_5322_);
v___x_5324_ = l_Lean_Syntax_node1(v___x_5301_, v___x_5302_, v___x_5323_);
v___x_5325_ = l_Lean_Syntax_node2(v___x_5301_, v___x_5303_, v___x_5321_, v___x_5324_);
v___x_5326_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5327_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5301_);
lean_ctor_set(v___x_5328_, 1, v___x_5327_);
v___x_5329_ = l_Lean_Syntax_node2(v___x_5301_, v___x_5326_, v___x_5328_, v_b_5291_);
v___x_5330_ = l_Lean_Syntax_node2(v___x_5301_, v___x_5303_, v___x_5329_, v___x_5311_);
v___x_5331_ = l_Lean_Syntax_node2(v___x_5301_, v___x_5302_, v___x_5325_, v___x_5330_);
v___x_5332_ = l_Lean_Syntax_node1(v___x_5301_, v___x_5298_, v___x_5331_);
v___x_5333_ = ((size_t)1ULL);
v___x_5334_ = lean_usize_add(v_i_5290_, v___x_5333_);
v_i_5290_ = v___x_5334_;
v_b_5291_ = v___x_5332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5336_, lean_object* v_sz_5337_, lean_object* v_i_5338_, lean_object* v_b_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
size_t v_sz_boxed_5342_; size_t v_i_boxed_5343_; lean_object* v_res_5344_; 
v_sz_boxed_5342_ = lean_unbox_usize(v_sz_5337_);
lean_dec(v_sz_5337_);
v_i_boxed_5343_ = lean_unbox_usize(v_i_5338_);
lean_dec(v_i_5338_);
v_res_5344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5336_, v_sz_boxed_5342_, v_i_boxed_5343_, v_b_5339_, v___y_5340_);
lean_dec_ref(v___y_5340_);
lean_dec_ref(v_as_5336_);
return v_res_5344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5345_, size_t v_sz_5346_, size_t v_i_5347_, lean_object* v_b_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
uint8_t v___x_5357_; 
v___x_5357_ = lean_usize_dec_lt(v_i_5347_, v_sz_5346_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5358_; 
v___x_5358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5358_, 0, v_b_5348_);
return v___x_5358_;
}
else
{
lean_object* v_ref_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v_a_5362_; uint8_t v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; size_t v___x_5396_; size_t v___x_5397_; lean_object* v___x_5398_; 
v_ref_5359_ = lean_ctor_get(v___y_5354_, 2);
v___x_5360_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5361_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5362_ = lean_array_uget_borrowed(v_as_5345_, v_i_5347_);
v___x_5363_ = 0;
v___x_5364_ = l_Lean_SourceInfo_fromRef(v_ref_5359_, v___x_5363_);
v___x_5365_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5366_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5367_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5368_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5364_, 17);
v___x_5369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5369_, 0, v___x_5364_);
lean_ctor_set(v___x_5369_, 1, v___x_5368_);
v___x_5370_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5371_, 0, v___x_5364_);
lean_ctor_set(v___x_5371_, 1, v___x_5370_);
v___x_5372_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5365_, v___x_5371_);
v___x_5373_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5374_, 0, v___x_5364_);
lean_ctor_set(v___x_5374_, 1, v___x_5365_);
lean_ctor_set(v___x_5374_, 2, v___x_5373_);
lean_inc_ref_n(v___x_5374_, 3);
v___x_5375_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5360_, v___x_5374_);
v___x_5376_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5377_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5378_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5362_, 2);
v___x_5379_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5378_, v_a_5362_);
v___x_5380_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5364_);
lean_ctor_set(v___x_5381_, 1, v___x_5380_);
v___x_5382_ = l_Lean_Syntax_node5(v___x_5364_, v___x_5377_, v___x_5379_, v___x_5374_, v___x_5374_, v___x_5381_, v_a_5362_);
v___x_5383_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5376_, v___x_5382_);
v___x_5384_ = l_Lean_Syntax_node4(v___x_5364_, v___x_5367_, v___x_5369_, v___x_5372_, v___x_5375_, v___x_5383_);
v___x_5385_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5364_);
lean_ctor_set(v___x_5386_, 1, v___x_5385_);
v___x_5387_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5365_, v___x_5386_);
v___x_5388_ = l_Lean_Syntax_node2(v___x_5364_, v___x_5366_, v___x_5384_, v___x_5387_);
v___x_5389_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5390_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5391_, 0, v___x_5364_);
lean_ctor_set(v___x_5391_, 1, v___x_5390_);
v___x_5392_ = l_Lean_Syntax_node2(v___x_5364_, v___x_5389_, v___x_5391_, v_b_5348_);
v___x_5393_ = l_Lean_Syntax_node2(v___x_5364_, v___x_5366_, v___x_5392_, v___x_5374_);
v___x_5394_ = l_Lean_Syntax_node2(v___x_5364_, v___x_5365_, v___x_5388_, v___x_5393_);
v___x_5395_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5361_, v___x_5394_);
v___x_5396_ = ((size_t)1ULL);
v___x_5397_ = lean_usize_add(v_i_5347_, v___x_5396_);
v___x_5398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5345_, v_sz_5346_, v___x_5397_, v___x_5395_, v___y_5354_);
return v___x_5398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5399_, lean_object* v_sz_5400_, lean_object* v_i_5401_, lean_object* v_b_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
size_t v_sz_boxed_5411_; size_t v_i_boxed_5412_; lean_object* v_res_5413_; 
v_sz_boxed_5411_ = lean_unbox_usize(v_sz_5400_);
lean_dec(v_sz_5400_);
v_i_boxed_5412_ = lean_unbox_usize(v_i_5401_);
lean_dec(v_i_5401_);
v_res_5413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5399_, v_sz_boxed_5411_, v_i_boxed_5412_, v_b_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_);
lean_dec(v___y_5409_);
lean_dec_ref(v___y_5408_);
lean_dec(v___y_5407_);
lean_dec_ref(v___y_5406_);
lean_dec(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec_ref(v___y_5403_);
lean_dec_ref(v_as_5399_);
return v_res_5413_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5453_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5454_ = l_String_toRawSubstring_x27(v___x_5453_);
return v___x_5454_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5468_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5469_ = l_String_toRawSubstring_x27(v___x_5468_);
return v___x_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5486_, lean_object* v_dec_5487_, lean_object* v_a_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_){
_start:
{
lean_object* v___x_5496_; uint8_t v___x_5497_; 
v___x_5496_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
lean_inc(v_stx_5486_);
v___x_5497_ = l_Lean_Syntax_isOfKind(v_stx_5486_, v___x_5496_);
if (v___x_5497_ == 0)
{
lean_object* v___x_5498_; 
lean_dec_ref(v_dec_5487_);
lean_dec(v_stx_5486_);
v___x_5498_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5498_;
}
else
{
lean_object* v___y_5500_; uint8_t v___y_5501_; lean_object* v___y_5502_; lean_object* v___y_5503_; lean_object* v___y_5504_; lean_object* v_body_5505_; lean_object* v___y_5506_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___y_5510_; lean_object* v___y_5511_; lean_object* v___y_5512_; lean_object* v___y_5586_; lean_object* v___y_5587_; uint8_t v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5591_; lean_object* v___y_5592_; lean_object* v___y_5593_; lean_object* v___y_5594_; lean_object* v___y_5595_; lean_object* v___y_5596_; lean_object* v___y_5597_; lean_object* v___y_5598_; lean_object* v___y_5599_; lean_object* v_a_5600_; lean_object* v___y_5614_; lean_object* v___y_5615_; lean_object* v___y_5616_; lean_object* v___y_5617_; lean_object* v___y_5618_; lean_object* v___y_5619_; lean_object* v___y_5620_; lean_object* v___y_5621_; lean_object* v___y_5622_; lean_object* v___y_5623_; lean_object* v___y_5624_; lean_object* v___y_5625_; lean_object* v___y_5626_; lean_object* v_mutTk_x3f_5699_; lean_object* v___y_5700_; lean_object* v___y_5701_; lean_object* v___y_5702_; lean_object* v___y_5703_; lean_object* v___y_5704_; lean_object* v___y_5705_; lean_object* v___y_5706_; lean_object* v___x_5730_; lean_object* v___x_5731_; uint8_t v___x_5732_; 
v___x_5730_ = lean_unsigned_to_nat(1u);
v___x_5731_ = l_Lean_Syntax_getArg(v_stx_5486_, v___x_5730_);
v___x_5732_ = l_Lean_Syntax_isNone(v___x_5731_);
if (v___x_5732_ == 0)
{
uint8_t v___x_5733_; 
lean_inc(v___x_5731_);
v___x_5733_ = l_Lean_Syntax_matchesNull(v___x_5731_, v___x_5730_);
if (v___x_5733_ == 0)
{
lean_object* v___x_5734_; 
lean_dec(v___x_5731_);
lean_dec_ref(v_dec_5487_);
lean_dec(v_stx_5486_);
v___x_5734_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5734_;
}
else
{
lean_object* v___x_5735_; lean_object* v_mutTk_x3f_5736_; lean_object* v___x_5737_; 
v___x_5735_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5736_ = l_Lean_Syntax_getArg(v___x_5731_, v___x_5735_);
lean_dec(v___x_5731_);
v___x_5737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5737_, 0, v_mutTk_x3f_5736_);
v_mutTk_x3f_5699_ = v___x_5737_;
v___y_5700_ = v_a_5488_;
v___y_5701_ = v_a_5489_;
v___y_5702_ = v_a_5490_;
v___y_5703_ = v_a_5491_;
v___y_5704_ = v_a_5492_;
v___y_5705_ = v_a_5493_;
v___y_5706_ = v_a_5494_;
goto v___jp_5698_;
}
}
else
{
lean_object* v___x_5738_; 
lean_dec(v___x_5731_);
v___x_5738_ = lean_box(0);
v_mutTk_x3f_5699_ = v___x_5738_;
v___y_5700_ = v_a_5488_;
v___y_5701_ = v_a_5489_;
v___y_5702_ = v_a_5490_;
v___y_5703_ = v_a_5491_;
v___y_5704_ = v_a_5492_;
v___y_5705_ = v_a_5493_;
v___y_5706_ = v_a_5494_;
goto v___jp_5698_;
}
v___jp_5499_:
{
lean_object* v_eq_x3f_5513_; 
v_eq_x3f_5513_ = lean_ctor_get(v___y_5503_, 0);
lean_inc(v_eq_x3f_5513_);
lean_dec_ref(v___y_5503_);
if (lean_obj_tag(v_eq_x3f_5513_) == 1)
{
lean_object* v_val_5514_; lean_object* v_ref_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; 
v_val_5514_ = lean_ctor_get(v_eq_x3f_5513_, 0);
lean_inc(v_val_5514_);
lean_dec_ref_known(v_eq_x3f_5513_, 1);
v_ref_5515_ = lean_ctor_get(v___y_5511_, 2);
v___x_5516_ = l_Lean_SourceInfo_fromRef(v_ref_5515_, v___y_5501_);
v___x_5517_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5518_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
lean_inc_n(v___x_5516_, 19);
v___x_5519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5519_, 0, v___x_5516_);
lean_ctor_set(v___x_5519_, 1, v___x_5518_);
v___x_5520_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5521_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5522_, 0, v___x_5516_);
lean_ctor_set(v___x_5522_, 1, v___x_5520_);
lean_ctor_set(v___x_5522_, 2, v___x_5521_);
v___x_5523_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5524_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5525_, 0, v___x_5516_);
lean_ctor_set(v___x_5525_, 1, v___x_5524_);
v___x_5526_ = l_Lean_Syntax_node2(v___x_5516_, v___x_5520_, v_val_5514_, v___x_5525_);
v___x_5527_ = l_Lean_Syntax_node2(v___x_5516_, v___x_5523_, v___x_5526_, v___y_5504_);
v___x_5528_ = l_Lean_Syntax_node1(v___x_5516_, v___x_5520_, v___x_5527_);
v___x_5529_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5530_, 0, v___x_5516_);
lean_ctor_set(v___x_5530_, 1, v___x_5529_);
v___x_5531_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5532_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5533_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5534_, 0, v___x_5516_);
lean_ctor_set(v___x_5534_, 1, v___x_5533_);
v___x_5535_ = l_Lean_Syntax_node1(v___x_5516_, v___x_5520_, v___y_5502_);
v___x_5536_ = l_Lean_Syntax_node1(v___x_5516_, v___x_5520_, v___x_5535_);
v___x_5537_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5538_, 0, v___x_5516_);
lean_ctor_set(v___x_5538_, 1, v___x_5537_);
lean_inc_ref(v___x_5538_);
lean_inc_ref(v___x_5534_);
v___x_5539_ = l_Lean_Syntax_node4(v___x_5516_, v___x_5532_, v___x_5534_, v___x_5536_, v___x_5538_, v_body_5505_);
v___x_5540_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5541_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5516_);
lean_ctor_set(v___x_5542_, 1, v___x_5541_);
v___x_5543_ = l_Lean_Syntax_node1(v___x_5516_, v___x_5540_, v___x_5542_);
v___x_5544_ = l_Lean_Syntax_node1(v___x_5516_, v___x_5520_, v___x_5543_);
v___x_5545_ = l_Lean_Syntax_node1(v___x_5516_, v___x_5520_, v___x_5544_);
v___x_5546_ = l_Lean_Syntax_node4(v___x_5516_, v___x_5532_, v___x_5534_, v___x_5545_, v___x_5538_, v___y_5500_);
v___x_5547_ = l_Lean_Syntax_node2(v___x_5516_, v___x_5520_, v___x_5539_, v___x_5546_);
v___x_5548_ = l_Lean_Syntax_node1(v___x_5516_, v___x_5531_, v___x_5547_);
lean_inc_ref_n(v___x_5522_, 2);
v___x_5549_ = l_Lean_Syntax_node7(v___x_5516_, v___x_5517_, v___x_5519_, v___x_5522_, v___x_5522_, v___x_5522_, v___x_5528_, v___x_5530_, v___x_5548_);
v___x_5550_ = l_Lean_Elab_Do_elabDoElem(v___x_5549_, v_dec_5487_, v___x_5497_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
return v___x_5550_;
}
else
{
lean_object* v_ref_5551_; lean_object* v___x_5552_; lean_object* v_a_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; 
lean_dec(v_eq_x3f_5513_);
v_ref_5551_ = lean_ctor_get(v___y_5511_, 2);
v___x_5552_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5551_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
v_a_5553_ = lean_ctor_get(v___x_5552_, 0);
lean_inc_n(v_a_5553_, 18);
lean_dec_ref(v___x_5552_);
v___x_5554_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5555_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_5556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5556_, 0, v_a_5553_);
lean_ctor_set(v___x_5556_, 1, v___x_5555_);
v___x_5557_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5558_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5559_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5559_, 0, v_a_5553_);
lean_ctor_set(v___x_5559_, 1, v___x_5557_);
lean_ctor_set(v___x_5559_, 2, v___x_5558_);
v___x_5560_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
lean_inc_ref_n(v___x_5559_, 3);
v___x_5561_ = l_Lean_Syntax_node2(v_a_5553_, v___x_5560_, v___x_5559_, v___y_5504_);
v___x_5562_ = l_Lean_Syntax_node1(v_a_5553_, v___x_5557_, v___x_5561_);
v___x_5563_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5564_, 0, v_a_5553_);
lean_ctor_set(v___x_5564_, 1, v___x_5563_);
v___x_5565_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5566_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5567_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5568_, 0, v_a_5553_);
lean_ctor_set(v___x_5568_, 1, v___x_5567_);
v___x_5569_ = l_Lean_Syntax_node1(v_a_5553_, v___x_5557_, v___y_5502_);
v___x_5570_ = l_Lean_Syntax_node1(v_a_5553_, v___x_5557_, v___x_5569_);
v___x_5571_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5572_, 0, v_a_5553_);
lean_ctor_set(v___x_5572_, 1, v___x_5571_);
lean_inc_ref(v___x_5572_);
lean_inc_ref(v___x_5568_);
v___x_5573_ = l_Lean_Syntax_node4(v_a_5553_, v___x_5566_, v___x_5568_, v___x_5570_, v___x_5572_, v_body_5505_);
v___x_5574_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5575_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5576_, 0, v_a_5553_);
lean_ctor_set(v___x_5576_, 1, v___x_5575_);
v___x_5577_ = l_Lean_Syntax_node1(v_a_5553_, v___x_5574_, v___x_5576_);
v___x_5578_ = l_Lean_Syntax_node1(v_a_5553_, v___x_5557_, v___x_5577_);
v___x_5579_ = l_Lean_Syntax_node1(v_a_5553_, v___x_5557_, v___x_5578_);
v___x_5580_ = l_Lean_Syntax_node4(v_a_5553_, v___x_5566_, v___x_5568_, v___x_5579_, v___x_5572_, v___y_5500_);
v___x_5581_ = l_Lean_Syntax_node2(v_a_5553_, v___x_5557_, v___x_5573_, v___x_5580_);
v___x_5582_ = l_Lean_Syntax_node1(v_a_5553_, v___x_5565_, v___x_5581_);
v___x_5583_ = l_Lean_Syntax_node7(v_a_5553_, v___x_5554_, v___x_5556_, v___x_5559_, v___x_5559_, v___x_5559_, v___x_5562_, v___x_5564_, v___x_5582_);
v___x_5584_ = l_Lean_Elab_Do_elabDoElem(v___x_5583_, v_dec_5487_, v___x_5497_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
return v___x_5584_;
}
}
v___jp_5585_:
{
if (lean_obj_tag(v___y_5591_) == 0)
{
lean_dec_ref(v___y_5586_);
v___y_5500_ = v___y_5587_;
v___y_5501_ = v___y_5588_;
v___y_5502_ = v___y_5589_;
v___y_5503_ = v___y_5590_;
v___y_5504_ = v___y_5594_;
v_body_5505_ = v_a_5600_;
v___y_5506_ = v___y_5596_;
v___y_5507_ = v___y_5593_;
v___y_5508_ = v___y_5599_;
v___y_5509_ = v___y_5592_;
v___y_5510_ = v___y_5595_;
v___y_5511_ = v___y_5597_;
v___y_5512_ = v___y_5598_;
goto v___jp_5499_;
}
else
{
size_t v_sz_5601_; size_t v___x_5602_; lean_object* v___x_5603_; 
lean_dec_ref_known(v___y_5591_, 1);
v_sz_5601_ = lean_array_size(v___y_5586_);
v___x_5602_ = ((size_t)0ULL);
v___x_5603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5586_, v_sz_5601_, v___x_5602_, v_a_5600_, v___y_5596_, v___y_5593_, v___y_5599_, v___y_5592_, v___y_5595_, v___y_5597_, v___y_5598_);
lean_dec_ref(v___y_5586_);
if (lean_obj_tag(v___x_5603_) == 0)
{
lean_object* v_a_5604_; 
v_a_5604_ = lean_ctor_get(v___x_5603_, 0);
lean_inc(v_a_5604_);
lean_dec_ref_known(v___x_5603_, 1);
v___y_5500_ = v___y_5587_;
v___y_5501_ = v___y_5588_;
v___y_5502_ = v___y_5589_;
v___y_5503_ = v___y_5590_;
v___y_5504_ = v___y_5594_;
v_body_5505_ = v_a_5604_;
v___y_5506_ = v___y_5596_;
v___y_5507_ = v___y_5593_;
v___y_5508_ = v___y_5599_;
v___y_5509_ = v___y_5592_;
v___y_5510_ = v___y_5595_;
v___y_5511_ = v___y_5597_;
v___y_5512_ = v___y_5598_;
goto v___jp_5499_;
}
else
{
lean_object* v_a_5605_; lean_object* v___x_5607_; uint8_t v_isShared_5608_; uint8_t v_isSharedCheck_5612_; 
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5590_);
lean_dec(v___y_5589_);
lean_dec(v___y_5587_);
lean_dec_ref(v_dec_5487_);
v_a_5605_ = lean_ctor_get(v___x_5603_, 0);
v_isSharedCheck_5612_ = !lean_is_exclusive(v___x_5603_);
if (v_isSharedCheck_5612_ == 0)
{
v___x_5607_ = v___x_5603_;
v_isShared_5608_ = v_isSharedCheck_5612_;
goto v_resetjp_5606_;
}
else
{
lean_inc(v_a_5605_);
lean_dec(v___x_5603_);
v___x_5607_ = lean_box(0);
v_isShared_5608_ = v_isSharedCheck_5612_;
goto v_resetjp_5606_;
}
v_resetjp_5606_:
{
lean_object* v___x_5610_; 
if (v_isShared_5608_ == 0)
{
v___x_5610_ = v___x_5607_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v_a_5605_);
v___x_5610_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
return v___x_5610_;
}
}
}
}
}
v___jp_5613_:
{
lean_object* v___x_5627_; uint8_t v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; 
v___x_5627_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_5628_ = 0;
v___x_5629_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_5630_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v___y_5625_, v___y_5616_, v___x_5629_, v___y_5621_, v___y_5618_, v___y_5624_, v___y_5617_, v___y_5620_, v___y_5622_, v___y_5623_);
if (lean_obj_tag(v___x_5630_) == 0)
{
lean_object* v_a_5631_; lean_object* v___x_5632_; 
v_a_5631_ = lean_ctor_get(v___x_5630_, 0);
lean_inc(v_a_5631_);
lean_dec_ref_known(v___x_5630_, 1);
v___x_5632_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_5631_, v___y_5617_, v___y_5620_, v___y_5622_, v___y_5623_);
if (lean_obj_tag(v___x_5632_) == 0)
{
lean_object* v___x_5633_; lean_object* v___x_5634_; 
lean_dec_ref_known(v___x_5632_, 1);
lean_inc(v___y_5616_);
v___x_5633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5633_, 0, v___y_5616_);
lean_ctor_set_uint8(v___x_5633_, sizeof(void*)*1, v___x_5628_);
lean_inc(v___y_5615_);
v___x_5634_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5615_, v___y_5618_, v___y_5624_, v___y_5617_, v___y_5620_, v___y_5622_, v___y_5623_);
if (lean_obj_tag(v___x_5634_) == 0)
{
lean_object* v_a_5635_; lean_object* v___x_5636_; 
v_a_5635_ = lean_ctor_get(v___x_5634_, 0);
lean_inc(v_a_5635_);
lean_dec_ref_known(v___x_5634_, 1);
v___x_5636_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5633_, v_a_5635_, v___y_5621_, v___y_5618_, v___y_5624_, v___y_5617_, v___y_5620_, v___y_5622_, v___y_5623_);
lean_dec_ref_known(v___x_5633_, 1);
if (lean_obj_tag(v___x_5636_) == 0)
{
lean_dec_ref_known(v___x_5636_, 1);
if (lean_obj_tag(v___y_5626_) == 0)
{
lean_object* v_toCold_5637_; lean_object* v_ref_5638_; lean_object* v___x_5639_; lean_object* v_a_5640_; lean_object* v_quotContext_5641_; lean_object* v_currMacroScope_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; 
v_toCold_5637_ = lean_ctor_get(v___y_5622_, 0);
v_ref_5638_ = lean_ctor_get(v___y_5622_, 2);
v___x_5639_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5638_, v___y_5621_, v___y_5618_, v___y_5624_, v___y_5617_, v___y_5620_, v___y_5622_, v___y_5623_);
v_a_5640_ = lean_ctor_get(v___x_5639_, 0);
lean_inc_n(v_a_5640_, 9);
lean_dec_ref(v___x_5639_);
v_quotContext_5641_ = lean_ctor_get(v_toCold_5637_, 8);
v_currMacroScope_5642_ = lean_ctor_get(v_toCold_5637_, 9);
v___x_5643_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5644_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5645_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5646_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1));
v___x_5647_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5648_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5642_, 2);
lean_inc_n(v_quotContext_5641_, 2);
v___x_5649_ = l_Lean_addMacroScope(v_quotContext_5641_, v___x_5648_, v_currMacroScope_5642_);
v___x_5650_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5651_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5651_, 0, v_a_5640_);
lean_ctor_set(v___x_5651_, 1, v___x_5647_);
lean_ctor_set(v___x_5651_, 2, v___x_5649_);
lean_ctor_set(v___x_5651_, 3, v___x_5650_);
v___x_5652_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5653_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5654_ = l_Lean_addMacroScope(v_quotContext_5641_, v___x_5653_, v_currMacroScope_5642_);
v___x_5655_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5656_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5656_, 0, v_a_5640_);
lean_ctor_set(v___x_5656_, 1, v___x_5652_);
lean_ctor_set(v___x_5656_, 2, v___x_5654_);
lean_ctor_set(v___x_5656_, 3, v___x_5655_);
v___x_5657_ = l_Lean_Syntax_node1(v_a_5640_, v___x_5643_, v___x_5656_);
v___x_5658_ = l_Lean_Syntax_node2(v_a_5640_, v___x_5646_, v___x_5651_, v___x_5657_);
v___x_5659_ = l_Lean_Syntax_node1(v_a_5640_, v___x_5645_, v___x_5658_);
v___x_5660_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5661_, 0, v_a_5640_);
lean_ctor_set(v___x_5661_, 1, v___x_5643_);
lean_ctor_set(v___x_5661_, 2, v___x_5660_);
v___x_5662_ = l_Lean_Syntax_node2(v_a_5640_, v___x_5644_, v___x_5659_, v___x_5661_);
v___x_5663_ = l_Lean_Syntax_node1(v_a_5640_, v___x_5643_, v___x_5662_);
v___x_5664_ = l_Lean_Syntax_node1(v_a_5640_, v___x_5627_, v___x_5663_);
v___y_5586_ = v_a_5635_;
v___y_5587_ = v___y_5614_;
v___y_5588_ = v___x_5628_;
v___y_5589_ = v___y_5615_;
v___y_5590_ = v_a_5631_;
v___y_5591_ = v___y_5616_;
v___y_5592_ = v___y_5617_;
v___y_5593_ = v___y_5618_;
v___y_5594_ = v___y_5619_;
v___y_5595_ = v___y_5620_;
v___y_5596_ = v___y_5621_;
v___y_5597_ = v___y_5622_;
v___y_5598_ = v___y_5623_;
v___y_5599_ = v___y_5624_;
v_a_5600_ = v___x_5664_;
goto v___jp_5585_;
}
else
{
lean_object* v_val_5665_; 
v_val_5665_ = lean_ctor_get(v___y_5626_, 0);
lean_inc(v_val_5665_);
lean_dec_ref_known(v___y_5626_, 1);
v___y_5586_ = v_a_5635_;
v___y_5587_ = v___y_5614_;
v___y_5588_ = v___x_5628_;
v___y_5589_ = v___y_5615_;
v___y_5590_ = v_a_5631_;
v___y_5591_ = v___y_5616_;
v___y_5592_ = v___y_5617_;
v___y_5593_ = v___y_5618_;
v___y_5594_ = v___y_5619_;
v___y_5595_ = v___y_5620_;
v___y_5596_ = v___y_5621_;
v___y_5597_ = v___y_5622_;
v___y_5598_ = v___y_5623_;
v___y_5599_ = v___y_5624_;
v_a_5600_ = v_val_5665_;
goto v___jp_5585_;
}
}
else
{
lean_object* v_a_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5673_; 
lean_dec(v_a_5635_);
lean_dec(v_a_5631_);
lean_dec(v___y_5626_);
lean_dec(v___y_5619_);
lean_dec(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v_dec_5487_);
v_a_5666_ = lean_ctor_get(v___x_5636_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5636_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5668_ = v___x_5636_;
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_a_5666_);
lean_dec(v___x_5636_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5666_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
else
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5681_; 
lean_dec_ref_known(v___x_5633_, 1);
lean_dec(v_a_5631_);
lean_dec(v___y_5626_);
lean_dec(v___y_5619_);
lean_dec(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v_dec_5487_);
v_a_5674_ = lean_ctor_get(v___x_5634_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5634_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5676_ = v___x_5634_;
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5634_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_a_5674_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
}
else
{
lean_object* v_a_5682_; lean_object* v___x_5684_; uint8_t v_isShared_5685_; uint8_t v_isSharedCheck_5689_; 
lean_dec(v_a_5631_);
lean_dec(v___y_5626_);
lean_dec(v___y_5619_);
lean_dec(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v_dec_5487_);
v_a_5682_ = lean_ctor_get(v___x_5632_, 0);
v_isSharedCheck_5689_ = !lean_is_exclusive(v___x_5632_);
if (v_isSharedCheck_5689_ == 0)
{
v___x_5684_ = v___x_5632_;
v_isShared_5685_ = v_isSharedCheck_5689_;
goto v_resetjp_5683_;
}
else
{
lean_inc(v_a_5682_);
lean_dec(v___x_5632_);
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
lean_dec(v___y_5626_);
lean_dec(v___y_5619_);
lean_dec(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v_dec_5487_);
v_a_5690_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5692_ = v___x_5630_;
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5630_);
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
v___jp_5698_:
{
lean_object* v___x_5707_; lean_object* v_cfg_5708_; lean_object* v___x_5709_; uint8_t v___x_5710_; 
v___x_5707_ = lean_unsigned_to_nat(2u);
v_cfg_5708_ = l_Lean_Syntax_getArg(v_stx_5486_, v___x_5707_);
v___x_5709_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_5708_);
v___x_5710_ = l_Lean_Syntax_isOfKind(v_cfg_5708_, v___x_5709_);
if (v___x_5710_ == 0)
{
lean_object* v___x_5711_; 
lean_dec(v_cfg_5708_);
lean_dec(v_mutTk_x3f_5699_);
lean_dec_ref(v_dec_5487_);
lean_dec(v_stx_5486_);
v___x_5711_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5711_;
}
else
{
lean_object* v___x_5712_; lean_object* v_pattern_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; 
v___x_5712_ = lean_unsigned_to_nat(3u);
v_pattern_5713_ = l_Lean_Syntax_getArg(v_stx_5486_, v___x_5712_);
v___x_5714_ = lean_unsigned_to_nat(5u);
v___x_5715_ = l_Lean_Syntax_getArg(v_stx_5486_, v___x_5714_);
v___x_5716_ = lean_unsigned_to_nat(7u);
v___x_5717_ = l_Lean_Syntax_getArg(v_stx_5486_, v___x_5716_);
v___x_5718_ = lean_unsigned_to_nat(8u);
v___x_5719_ = l_Lean_Syntax_getArg(v_stx_5486_, v___x_5718_);
lean_dec(v_stx_5486_);
v___x_5720_ = l_Lean_Syntax_getOptional_x3f(v___x_5719_);
lean_dec(v___x_5719_);
if (lean_obj_tag(v___x_5720_) == 0)
{
lean_object* v___x_5721_; 
v___x_5721_ = lean_box(0);
v___y_5614_ = v___x_5717_;
v___y_5615_ = v_pattern_5713_;
v___y_5616_ = v_mutTk_x3f_5699_;
v___y_5617_ = v___y_5703_;
v___y_5618_ = v___y_5701_;
v___y_5619_ = v___x_5715_;
v___y_5620_ = v___y_5704_;
v___y_5621_ = v___y_5700_;
v___y_5622_ = v___y_5705_;
v___y_5623_ = v___y_5706_;
v___y_5624_ = v___y_5702_;
v___y_5625_ = v_cfg_5708_;
v___y_5626_ = v___x_5721_;
goto v___jp_5613_;
}
else
{
lean_object* v_val_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5729_; 
v_val_5722_ = lean_ctor_get(v___x_5720_, 0);
v_isSharedCheck_5729_ = !lean_is_exclusive(v___x_5720_);
if (v_isSharedCheck_5729_ == 0)
{
v___x_5724_ = v___x_5720_;
v_isShared_5725_ = v_isSharedCheck_5729_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_val_5722_);
lean_dec(v___x_5720_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5729_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v___x_5727_; 
if (v_isShared_5725_ == 0)
{
v___x_5727_ = v___x_5724_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v_val_5722_);
v___x_5727_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
v___y_5614_ = v___x_5717_;
v___y_5615_ = v_pattern_5713_;
v___y_5616_ = v_mutTk_x3f_5699_;
v___y_5617_ = v___y_5703_;
v___y_5618_ = v___y_5701_;
v___y_5619_ = v___x_5715_;
v___y_5620_ = v___y_5704_;
v___y_5621_ = v___y_5700_;
v___y_5622_ = v___y_5705_;
v___y_5623_ = v___y_5706_;
v___y_5624_ = v___y_5702_;
v___y_5625_ = v_cfg_5708_;
v___y_5626_ = v___x_5727_;
goto v___jp_5613_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5739_, lean_object* v_dec_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_){
_start:
{
lean_object* v_res_5749_; 
v_res_5749_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5739_, v_dec_5740_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_);
lean_dec(v_a_5747_);
lean_dec_ref(v_a_5746_);
lean_dec(v_a_5745_);
lean_dec_ref(v_a_5744_);
lean_dec(v_a_5743_);
lean_dec_ref(v_a_5742_);
lean_dec_ref(v_a_5741_);
return v_res_5749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5750_, size_t v_sz_5751_, size_t v_i_5752_, lean_object* v_b_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
lean_object* v___x_5762_; 
v___x_5762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5750_, v_sz_5751_, v_i_5752_, v_b_5753_, v___y_5759_);
return v___x_5762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5763_, lean_object* v_sz_5764_, lean_object* v_i_5765_, lean_object* v_b_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_){
_start:
{
size_t v_sz_boxed_5775_; size_t v_i_boxed_5776_; lean_object* v_res_5777_; 
v_sz_boxed_5775_ = lean_unbox_usize(v_sz_5764_);
lean_dec(v_sz_5764_);
v_i_boxed_5776_ = lean_unbox_usize(v_i_5765_);
lean_dec(v_i_5765_);
v_res_5777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5763_, v_sz_boxed_5775_, v_i_boxed_5776_, v_b_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
lean_dec(v___y_5773_);
lean_dec_ref(v___y_5772_);
lean_dec(v___y_5771_);
lean_dec_ref(v___y_5770_);
lean_dec(v___y_5769_);
lean_dec_ref(v___y_5768_);
lean_dec_ref(v___y_5767_);
lean_dec_ref(v_as_5763_);
return v_res_5777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; 
v___x_5785_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5786_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
v___x_5787_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5788_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5789_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5785_, v___x_5786_, v___x_5787_, v___x_5788_);
return v___x_5789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5790_){
_start:
{
lean_object* v_res_5791_; 
v_res_5791_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0(lean_object* v_otherwise_x3f_5792_, uint8_t v___x_5793_, lean_object* v___x_5794_, lean_object* v___x_5795_, lean_object* v___x_5796_, lean_object* v___x_5797_, lean_object* v___x_5798_, lean_object* v___x_5799_, lean_object* v_dec_5800_, uint8_t v___x_5801_, lean_object* v_mutTk_x3f_5802_, lean_object* v___x_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5792_) == 0)
{
lean_object* v_ref_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___y_5822_; 
lean_dec(v___y_5804_);
v_ref_5813_ = lean_ctor_get(v___y_5810_, 2);
v___x_5814_ = l_Lean_SourceInfo_fromRef(v_ref_5813_, v___x_5793_);
v___x_5815_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5796_);
lean_inc_ref(v___x_5795_);
lean_inc_ref(v___x_5794_);
v___x_5816_ = l_Lean_Name_mkStr4(v___x_5794_, v___x_5795_, v___x_5796_, v___x_5815_);
v___x_5817_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5814_);
v___x_5818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5818_, 0, v___x_5814_);
lean_ctor_set(v___x_5818_, 1, v___x_5817_);
v___x_5819_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5820_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5802_) == 1)
{
lean_object* v_val_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; 
v_val_5837_ = lean_ctor_get(v_mutTk_x3f_5802_, 0);
v___x_5838_ = l_Lean_SourceInfo_fromRef(v_val_5837_, v___x_5801_);
v___x_5839_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5840_, 0, v___x_5838_);
lean_ctor_set(v___x_5840_, 1, v___x_5839_);
v___x_5841_ = l_Array_mkArray1___redArg(v___x_5840_);
v___y_5822_ = v___x_5841_;
goto v___jp_5821_;
}
else
{
lean_object* v___x_5842_; 
v___x_5842_ = lean_mk_empty_array_with_capacity(v___x_5803_);
v___y_5822_ = v___x_5842_;
goto v___jp_5821_;
}
v___jp_5821_:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; 
v___x_5823_ = l_Array_append___redArg(v___x_5820_, v___y_5822_);
lean_dec_ref(v___y_5822_);
lean_inc_n(v___x_5814_, 6);
v___x_5824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5824_, 0, v___x_5814_);
lean_ctor_set(v___x_5824_, 1, v___x_5819_);
lean_ctor_set(v___x_5824_, 2, v___x_5823_);
v___x_5825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5825_, 0, v___x_5814_);
lean_ctor_set(v___x_5825_, 1, v___x_5819_);
lean_ctor_set(v___x_5825_, 2, v___x_5820_);
lean_inc_ref_n(v___x_5825_, 2);
v___x_5826_ = l_Lean_Syntax_node1(v___x_5814_, v___x_5797_, v___x_5825_);
v___x_5827_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5796_);
lean_inc_ref(v___x_5795_);
lean_inc_ref(v___x_5794_);
v___x_5828_ = l_Lean_Name_mkStr4(v___x_5794_, v___x_5795_, v___x_5796_, v___x_5827_);
v___x_5829_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5830_ = l_Lean_Name_mkStr4(v___x_5794_, v___x_5795_, v___x_5796_, v___x_5829_);
v___x_5831_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5814_);
lean_ctor_set(v___x_5832_, 1, v___x_5831_);
v___x_5833_ = l_Lean_Syntax_node5(v___x_5814_, v___x_5830_, v___x_5798_, v___x_5825_, v___x_5825_, v___x_5832_, v___x_5799_);
v___x_5834_ = l_Lean_Syntax_node1(v___x_5814_, v___x_5828_, v___x_5833_);
v___x_5835_ = l_Lean_Syntax_node4(v___x_5814_, v___x_5816_, v___x_5818_, v___x_5824_, v___x_5826_, v___x_5834_);
v___x_5836_ = l_Lean_Elab_Do_elabDoElem(v___x_5835_, v_dec_5800_, v___x_5801_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
return v___x_5836_;
}
}
else
{
lean_object* v_val_5843_; lean_object* v_ref_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___y_5853_; lean_object* v___y_5854_; lean_object* v___y_5855_; lean_object* v___y_5856_; lean_object* v___y_5857_; lean_object* v___y_5874_; 
v_val_5843_ = lean_ctor_get(v_otherwise_x3f_5792_, 0);
lean_inc(v_val_5843_);
lean_dec_ref_known(v_otherwise_x3f_5792_, 1);
v_ref_5844_ = lean_ctor_get(v___y_5810_, 2);
v___x_5845_ = l_Lean_SourceInfo_fromRef(v_ref_5844_, v___x_5793_);
v___x_5846_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5847_ = l_Lean_Name_mkStr4(v___x_5794_, v___x_5795_, v___x_5796_, v___x_5846_);
v___x_5848_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5845_);
v___x_5849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5849_, 0, v___x_5845_);
lean_ctor_set(v___x_5849_, 1, v___x_5848_);
v___x_5850_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5851_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5802_) == 1)
{
lean_object* v_val_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
v_val_5887_ = lean_ctor_get(v_mutTk_x3f_5802_, 0);
v___x_5888_ = l_Lean_SourceInfo_fromRef(v_val_5887_, v___x_5801_);
v___x_5889_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5890_, 0, v___x_5888_);
lean_ctor_set(v___x_5890_, 1, v___x_5889_);
v___x_5891_ = l_Array_mkArray1___redArg(v___x_5890_);
v___y_5874_ = v___x_5891_;
goto v___jp_5873_;
}
else
{
lean_object* v___x_5892_; 
v___x_5892_ = lean_mk_empty_array_with_capacity(v___x_5803_);
v___y_5874_ = v___x_5892_;
goto v___jp_5873_;
}
v___jp_5852_:
{
lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5858_ = l_Array_append___redArg(v___x_5851_, v___y_5857_);
lean_dec_ref(v___y_5857_);
lean_inc(v___x_5845_);
v___x_5859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5859_, 0, v___x_5845_);
lean_ctor_set(v___x_5859_, 1, v___x_5850_);
lean_ctor_set(v___x_5859_, 2, v___x_5858_);
v___x_5860_ = lean_unsigned_to_nat(9u);
v___x_5861_ = lean_mk_empty_array_with_capacity(v___x_5860_);
v___x_5862_ = lean_array_push(v___x_5861_, v___x_5849_);
v___x_5863_ = lean_array_push(v___x_5862_, v___y_5854_);
v___x_5864_ = lean_array_push(v___x_5863_, v___y_5855_);
v___x_5865_ = lean_array_push(v___x_5864_, v___x_5798_);
v___x_5866_ = lean_array_push(v___x_5865_, v___y_5853_);
v___x_5867_ = lean_array_push(v___x_5866_, v___x_5799_);
v___x_5868_ = lean_array_push(v___x_5867_, v___y_5856_);
v___x_5869_ = lean_array_push(v___x_5868_, v_val_5843_);
v___x_5870_ = lean_array_push(v___x_5869_, v___x_5859_);
v___x_5871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5871_, 0, v___x_5845_);
lean_ctor_set(v___x_5871_, 1, v___x_5847_);
lean_ctor_set(v___x_5871_, 2, v___x_5870_);
v___x_5872_ = l_Lean_Elab_Do_elabDoElem(v___x_5871_, v_dec_5800_, v___x_5801_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
return v___x_5872_;
}
v___jp_5873_:
{
lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; 
v___x_5875_ = l_Array_append___redArg(v___x_5851_, v___y_5874_);
lean_dec_ref(v___y_5874_);
lean_inc_n(v___x_5845_, 5);
v___x_5876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5876_, 0, v___x_5845_);
lean_ctor_set(v___x_5876_, 1, v___x_5850_);
lean_ctor_set(v___x_5876_, 2, v___x_5875_);
v___x_5877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5877_, 0, v___x_5845_);
lean_ctor_set(v___x_5877_, 1, v___x_5850_);
lean_ctor_set(v___x_5877_, 2, v___x_5851_);
v___x_5878_ = l_Lean_Syntax_node1(v___x_5845_, v___x_5797_, v___x_5877_);
v___x_5879_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5880_, 0, v___x_5845_);
lean_ctor_set(v___x_5880_, 1, v___x_5879_);
v___x_5881_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5882_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5882_, 0, v___x_5845_);
lean_ctor_set(v___x_5882_, 1, v___x_5881_);
if (lean_obj_tag(v___y_5804_) == 0)
{
lean_object* v___x_5883_; 
v___x_5883_ = lean_mk_empty_array_with_capacity(v___x_5803_);
v___y_5853_ = v___x_5880_;
v___y_5854_ = v___x_5876_;
v___y_5855_ = v___x_5878_;
v___y_5856_ = v___x_5882_;
v___y_5857_ = v___x_5883_;
goto v___jp_5852_;
}
else
{
lean_object* v_val_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; 
v_val_5884_ = lean_ctor_get(v___y_5804_, 0);
lean_inc(v_val_5884_);
lean_dec_ref_known(v___y_5804_, 1);
v___x_5885_ = lean_mk_empty_array_with_capacity(v___x_5803_);
v___x_5886_ = lean_array_push(v___x_5885_, v_val_5884_);
v___y_5853_ = v___x_5880_;
v___y_5854_ = v___x_5876_;
v___y_5855_ = v___x_5878_;
v___y_5856_ = v___x_5882_;
v___y_5857_ = v___x_5886_;
goto v___jp_5852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_5893_ = _args[0];
lean_object* v___x_5894_ = _args[1];
lean_object* v___x_5895_ = _args[2];
lean_object* v___x_5896_ = _args[3];
lean_object* v___x_5897_ = _args[4];
lean_object* v___x_5898_ = _args[5];
lean_object* v___x_5899_ = _args[6];
lean_object* v___x_5900_ = _args[7];
lean_object* v_dec_5901_ = _args[8];
lean_object* v___x_5902_ = _args[9];
lean_object* v_mutTk_x3f_5903_ = _args[10];
lean_object* v___x_5904_ = _args[11];
lean_object* v___y_5905_ = _args[12];
lean_object* v___y_5906_ = _args[13];
lean_object* v___y_5907_ = _args[14];
lean_object* v___y_5908_ = _args[15];
lean_object* v___y_5909_ = _args[16];
lean_object* v___y_5910_ = _args[17];
lean_object* v___y_5911_ = _args[18];
lean_object* v___y_5912_ = _args[19];
lean_object* v___y_5913_ = _args[20];
_start:
{
uint8_t v___x_22521__boxed_5914_; uint8_t v___x_22528__boxed_5915_; lean_object* v_res_5916_; 
v___x_22521__boxed_5914_ = lean_unbox(v___x_5894_);
v___x_22528__boxed_5915_ = lean_unbox(v___x_5902_);
v_res_5916_ = l_Lean_Elab_Do_elabDoLetArrow___lam__0(v_otherwise_x3f_5893_, v___x_22521__boxed_5914_, v___x_5895_, v___x_5896_, v___x_5897_, v___x_5898_, v___x_5899_, v___x_5900_, v_dec_5901_, v___x_22528__boxed_5915_, v_mutTk_x3f_5903_, v___x_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_);
lean_dec(v___y_5912_);
lean_dec_ref(v___y_5911_);
lean_dec(v___y_5910_);
lean_dec_ref(v___y_5909_);
lean_dec(v___y_5908_);
lean_dec_ref(v___y_5907_);
lean_dec_ref(v___y_5906_);
lean_dec(v___x_5904_);
lean_dec(v_mutTk_x3f_5903_);
return v_res_5916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1(lean_object* v_otherwise_x3f_5917_, uint8_t v___x_5918_, lean_object* v___x_5919_, lean_object* v___x_5920_, lean_object* v___x_5921_, lean_object* v___x_5922_, lean_object* v___x_5923_, lean_object* v___x_5924_, lean_object* v_dec_5925_, uint8_t v___x_5926_, lean_object* v_mutTk_x3f_5927_, lean_object* v___x_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5917_) == 0)
{
lean_object* v_ref_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___y_5947_; 
lean_dec(v___y_5929_);
v_ref_5938_ = lean_ctor_get(v___y_5935_, 2);
v___x_5939_ = l_Lean_SourceInfo_fromRef(v_ref_5938_, v___x_5918_);
v___x_5940_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5921_);
lean_inc_ref(v___x_5920_);
lean_inc_ref(v___x_5919_);
v___x_5941_ = l_Lean_Name_mkStr4(v___x_5919_, v___x_5920_, v___x_5921_, v___x_5940_);
v___x_5942_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5939_);
v___x_5943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5939_);
lean_ctor_set(v___x_5943_, 1, v___x_5942_);
v___x_5944_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5945_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5927_) == 1)
{
lean_object* v_val_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; 
v_val_5962_ = lean_ctor_get(v_mutTk_x3f_5927_, 0);
v___x_5963_ = l_Lean_SourceInfo_fromRef(v_val_5962_, v___x_5926_);
v___x_5964_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5963_);
lean_ctor_set(v___x_5965_, 1, v___x_5964_);
v___x_5966_ = l_Array_mkArray1___redArg(v___x_5965_);
v___y_5947_ = v___x_5966_;
goto v___jp_5946_;
}
else
{
lean_object* v___x_5967_; 
v___x_5967_ = lean_mk_empty_array_with_capacity(v___x_5928_);
v___y_5947_ = v___x_5967_;
goto v___jp_5946_;
}
v___jp_5946_:
{
lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; 
v___x_5948_ = l_Array_append___redArg(v___x_5945_, v___y_5947_);
lean_dec_ref(v___y_5947_);
lean_inc_n(v___x_5939_, 6);
v___x_5949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5939_);
lean_ctor_set(v___x_5949_, 1, v___x_5944_);
lean_ctor_set(v___x_5949_, 2, v___x_5948_);
v___x_5950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5939_);
lean_ctor_set(v___x_5950_, 1, v___x_5944_);
lean_ctor_set(v___x_5950_, 2, v___x_5945_);
lean_inc_ref_n(v___x_5950_, 2);
v___x_5951_ = l_Lean_Syntax_node1(v___x_5939_, v___x_5922_, v___x_5950_);
v___x_5952_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5921_);
lean_inc_ref(v___x_5920_);
lean_inc_ref(v___x_5919_);
v___x_5953_ = l_Lean_Name_mkStr4(v___x_5919_, v___x_5920_, v___x_5921_, v___x_5952_);
v___x_5954_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5955_ = l_Lean_Name_mkStr4(v___x_5919_, v___x_5920_, v___x_5921_, v___x_5954_);
v___x_5956_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5939_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = l_Lean_Syntax_node5(v___x_5939_, v___x_5955_, v___x_5923_, v___x_5950_, v___x_5950_, v___x_5957_, v___x_5924_);
v___x_5959_ = l_Lean_Syntax_node1(v___x_5939_, v___x_5953_, v___x_5958_);
v___x_5960_ = l_Lean_Syntax_node4(v___x_5939_, v___x_5941_, v___x_5943_, v___x_5949_, v___x_5951_, v___x_5959_);
v___x_5961_ = l_Lean_Elab_Do_elabDoElem(v___x_5960_, v_dec_5925_, v___x_5926_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_);
return v___x_5961_;
}
}
else
{
lean_object* v_val_5968_; lean_object* v_ref_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___y_5978_; lean_object* v___y_5979_; lean_object* v___y_5980_; lean_object* v___y_5981_; lean_object* v___y_5982_; lean_object* v___y_5999_; 
v_val_5968_ = lean_ctor_get(v_otherwise_x3f_5917_, 0);
lean_inc(v_val_5968_);
lean_dec_ref_known(v_otherwise_x3f_5917_, 1);
v_ref_5969_ = lean_ctor_get(v___y_5935_, 2);
v___x_5970_ = l_Lean_SourceInfo_fromRef(v_ref_5969_, v___x_5918_);
v___x_5971_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5972_ = l_Lean_Name_mkStr4(v___x_5919_, v___x_5920_, v___x_5921_, v___x_5971_);
v___x_5973_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5970_);
v___x_5974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5970_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5976_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5927_) == 1)
{
lean_object* v_val_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; 
v_val_6012_ = lean_ctor_get(v_mutTk_x3f_5927_, 0);
v___x_6013_ = l_Lean_SourceInfo_fromRef(v_val_6012_, v___x_5926_);
v___x_6014_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_6015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6013_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = l_Array_mkArray1___redArg(v___x_6015_);
v___y_5999_ = v___x_6016_;
goto v___jp_5998_;
}
else
{
lean_object* v___x_6017_; 
v___x_6017_ = lean_mk_empty_array_with_capacity(v___x_5928_);
v___y_5999_ = v___x_6017_;
goto v___jp_5998_;
}
v___jp_5977_:
{
lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5983_ = l_Array_append___redArg(v___x_5976_, v___y_5982_);
lean_dec_ref(v___y_5982_);
lean_inc(v___x_5970_);
v___x_5984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5970_);
lean_ctor_set(v___x_5984_, 1, v___x_5975_);
lean_ctor_set(v___x_5984_, 2, v___x_5983_);
v___x_5985_ = lean_unsigned_to_nat(9u);
v___x_5986_ = lean_mk_empty_array_with_capacity(v___x_5985_);
v___x_5987_ = lean_array_push(v___x_5986_, v___x_5974_);
v___x_5988_ = lean_array_push(v___x_5987_, v___y_5980_);
v___x_5989_ = lean_array_push(v___x_5988_, v___y_5979_);
v___x_5990_ = lean_array_push(v___x_5989_, v___x_5923_);
v___x_5991_ = lean_array_push(v___x_5990_, v___y_5981_);
v___x_5992_ = lean_array_push(v___x_5991_, v___x_5924_);
v___x_5993_ = lean_array_push(v___x_5992_, v___y_5978_);
v___x_5994_ = lean_array_push(v___x_5993_, v_val_5968_);
v___x_5995_ = lean_array_push(v___x_5994_, v___x_5984_);
v___x_5996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5970_);
lean_ctor_set(v___x_5996_, 1, v___x_5972_);
lean_ctor_set(v___x_5996_, 2, v___x_5995_);
v___x_5997_ = l_Lean_Elab_Do_elabDoElem(v___x_5996_, v_dec_5925_, v___x_5926_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_);
return v___x_5997_;
}
v___jp_5998_:
{
lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6000_ = l_Array_append___redArg(v___x_5976_, v___y_5999_);
lean_dec_ref(v___y_5999_);
lean_inc_n(v___x_5970_, 5);
v___x_6001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6001_, 0, v___x_5970_);
lean_ctor_set(v___x_6001_, 1, v___x_5975_);
lean_ctor_set(v___x_6001_, 2, v___x_6000_);
v___x_6002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6002_, 0, v___x_5970_);
lean_ctor_set(v___x_6002_, 1, v___x_5975_);
lean_ctor_set(v___x_6002_, 2, v___x_5976_);
v___x_6003_ = l_Lean_Syntax_node1(v___x_5970_, v___x_5922_, v___x_6002_);
v___x_6004_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_5970_);
lean_ctor_set(v___x_6005_, 1, v___x_6004_);
v___x_6006_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_6007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_5970_);
lean_ctor_set(v___x_6007_, 1, v___x_6006_);
if (lean_obj_tag(v___y_5929_) == 0)
{
lean_object* v___x_6008_; 
v___x_6008_ = lean_mk_empty_array_with_capacity(v___x_5928_);
v___y_5978_ = v___x_6007_;
v___y_5979_ = v___x_6003_;
v___y_5980_ = v___x_6001_;
v___y_5981_ = v___x_6005_;
v___y_5982_ = v___x_6008_;
goto v___jp_5977_;
}
else
{
lean_object* v_val_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; 
v_val_6009_ = lean_ctor_get(v___y_5929_, 0);
lean_inc(v_val_6009_);
lean_dec_ref_known(v___y_5929_, 1);
v___x_6010_ = lean_mk_empty_array_with_capacity(v___x_5928_);
v___x_6011_ = lean_array_push(v___x_6010_, v_val_6009_);
v___y_5978_ = v___x_6007_;
v___y_5979_ = v___x_6003_;
v___y_5980_ = v___x_6001_;
v___y_5981_ = v___x_6005_;
v___y_5982_ = v___x_6011_;
goto v___jp_5977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_6018_ = _args[0];
lean_object* v___x_6019_ = _args[1];
lean_object* v___x_6020_ = _args[2];
lean_object* v___x_6021_ = _args[3];
lean_object* v___x_6022_ = _args[4];
lean_object* v___x_6023_ = _args[5];
lean_object* v___x_6024_ = _args[6];
lean_object* v___x_6025_ = _args[7];
lean_object* v_dec_6026_ = _args[8];
lean_object* v___x_6027_ = _args[9];
lean_object* v_mutTk_x3f_6028_ = _args[10];
lean_object* v___x_6029_ = _args[11];
lean_object* v___y_6030_ = _args[12];
lean_object* v___y_6031_ = _args[13];
lean_object* v___y_6032_ = _args[14];
lean_object* v___y_6033_ = _args[15];
lean_object* v___y_6034_ = _args[16];
lean_object* v___y_6035_ = _args[17];
lean_object* v___y_6036_ = _args[18];
lean_object* v___y_6037_ = _args[19];
lean_object* v___y_6038_ = _args[20];
_start:
{
uint8_t v___x_22752__boxed_6039_; uint8_t v___x_22759__boxed_6040_; lean_object* v_res_6041_; 
v___x_22752__boxed_6039_ = lean_unbox(v___x_6019_);
v___x_22759__boxed_6040_ = lean_unbox(v___x_6027_);
v_res_6041_ = l_Lean_Elab_Do_elabDoLetArrow___lam__1(v_otherwise_x3f_6018_, v___x_22752__boxed_6039_, v___x_6020_, v___x_6021_, v___x_6022_, v___x_6023_, v___x_6024_, v___x_6025_, v_dec_6026_, v___x_22759__boxed_6040_, v_mutTk_x3f_6028_, v___x_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_);
lean_dec(v___y_6037_);
lean_dec_ref(v___y_6036_);
lean_dec(v___y_6035_);
lean_dec_ref(v___y_6034_);
lean_dec(v___y_6033_);
lean_dec_ref(v___y_6032_);
lean_dec_ref(v___y_6031_);
lean_dec(v___x_6029_);
lean_dec(v_mutTk_x3f_6028_);
return v_res_6041_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1(void){
_start:
{
lean_object* v___x_6043_; lean_object* v___x_6044_; 
v___x_6043_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__0));
v___x_6044_ = l_Lean_stringToMessageData(v___x_6043_);
return v___x_6044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_6051_, lean_object* v_dec_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_, lean_object* v_a_6055_, lean_object* v_a_6056_, lean_object* v_a_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_){
_start:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; uint8_t v___x_6065_; 
v___x_6061_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_6062_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_6063_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_6064_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
lean_inc(v_stx_6051_);
v___x_6065_ = l_Lean_Syntax_isOfKind(v_stx_6051_, v___x_6064_);
if (v___x_6065_ == 0)
{
lean_object* v___x_6066_; 
lean_dec_ref(v_dec_6052_);
lean_dec(v_stx_6051_);
v___x_6066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6066_;
}
else
{
lean_object* v___x_6067_; uint8_t v___y_6069_; lean_object* v___y_6070_; lean_object* v___y_6071_; lean_object* v___y_6072_; lean_object* v___y_6073_; lean_object* v___y_6074_; uint8_t v___y_6075_; lean_object* v___y_6076_; lean_object* v___y_6077_; lean_object* v___y_6078_; lean_object* v___y_6079_; lean_object* v___y_6080_; lean_object* v___y_6081_; lean_object* v___y_6082_; lean_object* v___y_6083_; lean_object* v___y_6084_; lean_object* v___y_6085_; lean_object* v___y_6104_; uint8_t v___y_6105_; lean_object* v___y_6106_; lean_object* v___y_6107_; lean_object* v___y_6108_; lean_object* v___y_6109_; uint8_t v___y_6110_; lean_object* v___y_6111_; lean_object* v___y_6112_; lean_object* v___y_6113_; lean_object* v___y_6114_; lean_object* v___y_6115_; lean_object* v___y_6116_; lean_object* v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6119_; lean_object* v___y_6120_; lean_object* v___y_6123_; lean_object* v___y_6124_; lean_object* v___y_6125_; lean_object* v___y_6126_; lean_object* v___y_6127_; lean_object* v___y_6128_; lean_object* v___y_6129_; lean_object* v___y_6130_; uint8_t v___y_6131_; lean_object* v___y_6132_; uint8_t v___y_6133_; lean_object* v___y_6134_; lean_object* v___y_6135_; lean_object* v___y_6136_; lean_object* v___y_6137_; lean_object* v___y_6138_; lean_object* v___y_6139_; uint8_t v___y_6158_; lean_object* v___y_6159_; lean_object* v___y_6160_; lean_object* v___y_6161_; lean_object* v___y_6162_; lean_object* v___y_6163_; uint8_t v___y_6164_; lean_object* v___y_6165_; lean_object* v___y_6166_; lean_object* v___y_6167_; lean_object* v___y_6168_; lean_object* v___y_6169_; lean_object* v___y_6170_; lean_object* v___y_6171_; lean_object* v___y_6172_; lean_object* v___y_6173_; lean_object* v___y_6174_; lean_object* v_tk_6176_; lean_object* v___x_6177_; lean_object* v___y_6179_; lean_object* v___y_6180_; lean_object* v___y_6181_; uint8_t v___y_6182_; lean_object* v___y_6183_; lean_object* v___y_6184_; uint8_t v___y_6185_; lean_object* v___y_6186_; lean_object* v___y_6187_; lean_object* v___y_6188_; lean_object* v___y_6189_; lean_object* v_patType_x3f_6190_; lean_object* v___y_6191_; lean_object* v___y_6192_; lean_object* v___y_6193_; lean_object* v___y_6194_; lean_object* v___y_6195_; lean_object* v___y_6196_; lean_object* v___y_6197_; uint8_t v___y_6242_; lean_object* v___y_6243_; lean_object* v___y_6244_; lean_object* v___y_6245_; lean_object* v___y_6246_; uint8_t v___y_6247_; lean_object* v___y_6248_; lean_object* v___y_6249_; lean_object* v___y_6250_; lean_object* v___y_6251_; lean_object* v_patType_x3f_6252_; lean_object* v___y_6253_; lean_object* v___y_6254_; lean_object* v___y_6255_; lean_object* v___y_6256_; lean_object* v___y_6257_; lean_object* v___y_6258_; lean_object* v___y_6259_; lean_object* v___y_6278_; uint8_t v___y_6279_; lean_object* v___y_6280_; lean_object* v___y_6281_; lean_object* v___y_6282_; lean_object* v_xType_x3f_6283_; lean_object* v___y_6284_; lean_object* v___y_6285_; lean_object* v___y_6286_; lean_object* v___y_6287_; lean_object* v___y_6288_; lean_object* v___y_6289_; lean_object* v___y_6290_; lean_object* v___y_6319_; lean_object* v___y_6320_; lean_object* v___y_6321_; uint8_t v___y_6322_; lean_object* v___y_6323_; lean_object* v___y_6324_; lean_object* v___y_6325_; lean_object* v___y_6326_; lean_object* v___y_6327_; lean_object* v___y_6328_; lean_object* v___y_6329_; lean_object* v___y_6330_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6335_; lean_object* v___y_6378_; lean_object* v___y_6379_; lean_object* v___y_6380_; uint8_t v___y_6381_; lean_object* v___y_6382_; lean_object* v___y_6383_; lean_object* v___y_6384_; lean_object* v___y_6385_; lean_object* v___y_6386_; lean_object* v___y_6387_; lean_object* v___y_6388_; lean_object* v___y_6389_; lean_object* v___y_6390_; lean_object* v___y_6391_; lean_object* v___y_6392_; lean_object* v___y_6393_; lean_object* v___y_6394_; lean_object* v___y_6395_; lean_object* v_mutTk_x3f_6407_; lean_object* v___y_6408_; lean_object* v___y_6409_; lean_object* v___y_6410_; lean_object* v___y_6411_; lean_object* v___y_6412_; lean_object* v___y_6413_; lean_object* v___y_6414_; lean_object* v___x_6450_; uint8_t v___x_6451_; 
v___x_6067_ = lean_unsigned_to_nat(0u);
v_tk_6176_ = l_Lean_Syntax_getArg(v_stx_6051_, v___x_6067_);
v___x_6177_ = lean_unsigned_to_nat(1u);
v___x_6450_ = l_Lean_Syntax_getArg(v_stx_6051_, v___x_6177_);
v___x_6451_ = l_Lean_Syntax_isNone(v___x_6450_);
if (v___x_6451_ == 0)
{
uint8_t v___x_6452_; 
lean_inc(v___x_6450_);
v___x_6452_ = l_Lean_Syntax_matchesNull(v___x_6450_, v___x_6177_);
if (v___x_6452_ == 0)
{
lean_object* v___x_6453_; 
lean_dec(v___x_6450_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
lean_dec(v_stx_6051_);
v___x_6453_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6453_;
}
else
{
lean_object* v_mutTk_x3f_6454_; lean_object* v___x_6455_; 
v_mutTk_x3f_6454_ = l_Lean_Syntax_getArg(v___x_6450_, v___x_6067_);
lean_dec(v___x_6450_);
v___x_6455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6455_, 0, v_mutTk_x3f_6454_);
v_mutTk_x3f_6407_ = v___x_6455_;
v___y_6408_ = v_a_6053_;
v___y_6409_ = v_a_6054_;
v___y_6410_ = v_a_6055_;
v___y_6411_ = v_a_6056_;
v___y_6412_ = v_a_6057_;
v___y_6413_ = v_a_6058_;
v___y_6414_ = v_a_6059_;
goto v___jp_6406_;
}
}
else
{
lean_object* v___x_6456_; 
lean_dec(v___x_6450_);
v___x_6456_ = lean_box(0);
v_mutTk_x3f_6407_ = v___x_6456_;
v___y_6408_ = v_a_6053_;
v___y_6409_ = v_a_6054_;
v___y_6410_ = v_a_6055_;
v___y_6411_ = v_a_6056_;
v___y_6412_ = v_a_6057_;
v___y_6413_ = v_a_6058_;
v___y_6414_ = v_a_6059_;
goto v___jp_6406_;
}
v___jp_6068_:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; 
v___x_6086_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6087_ = l_Lean_Core_mkFreshUserName(v___x_6086_, v___y_6074_, v___y_6072_);
if (lean_obj_tag(v___x_6087_) == 0)
{
lean_object* v_a_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___y_6092_; uint8_t v___x_6093_; lean_object* v___x_6094_; 
v_a_6088_ = lean_ctor_get(v___x_6087_, 0);
lean_inc(v_a_6088_);
lean_dec_ref_known(v___x_6087_, 1);
v___x_6089_ = l_Lean_mkIdentFrom(v___y_6078_, v_a_6088_, v___y_6069_);
lean_dec(v___y_6078_);
v___x_6090_ = lean_box(v___y_6075_);
v___x_6091_ = lean_box(v___x_6065_);
lean_inc(v___x_6089_);
lean_inc(v___y_6083_);
v___y_6092_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_6092_, 0, v___y_6081_);
lean_closure_set(v___y_6092_, 1, v___x_6090_);
lean_closure_set(v___y_6092_, 2, v___x_6061_);
lean_closure_set(v___y_6092_, 3, v___x_6062_);
lean_closure_set(v___y_6092_, 4, v___x_6063_);
lean_closure_set(v___y_6092_, 5, v___y_6083_);
lean_closure_set(v___y_6092_, 6, v___y_6076_);
lean_closure_set(v___y_6092_, 7, v___x_6089_);
lean_closure_set(v___y_6092_, 8, v_dec_6052_);
lean_closure_set(v___y_6092_, 9, v___x_6091_);
lean_closure_set(v___y_6092_, 10, v___y_6077_);
lean_closure_set(v___y_6092_, 11, v___x_6067_);
lean_closure_set(v___y_6092_, 12, v___y_6085_);
v___x_6093_ = 0;
v___x_6094_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6089_, v___y_6082_, v___y_6079_, v___y_6092_, v___x_6093_, v___y_6070_, v___y_6071_, v___y_6080_, v___y_6073_, v___y_6084_, v___y_6074_, v___y_6072_);
return v___x_6094_;
}
else
{
lean_object* v_a_6095_; lean_object* v___x_6097_; uint8_t v_isShared_6098_; uint8_t v_isSharedCheck_6102_; 
lean_dec(v___y_6085_);
lean_dec(v___y_6082_);
lean_dec(v___y_6081_);
lean_dec(v___y_6079_);
lean_dec(v___y_6078_);
lean_dec(v___y_6077_);
lean_dec(v___y_6076_);
lean_dec_ref(v_dec_6052_);
v_a_6095_ = lean_ctor_get(v___x_6087_, 0);
v_isSharedCheck_6102_ = !lean_is_exclusive(v___x_6087_);
if (v_isSharedCheck_6102_ == 0)
{
v___x_6097_ = v___x_6087_;
v_isShared_6098_ = v_isSharedCheck_6102_;
goto v_resetjp_6096_;
}
else
{
lean_inc(v_a_6095_);
lean_dec(v___x_6087_);
v___x_6097_ = lean_box(0);
v_isShared_6098_ = v_isSharedCheck_6102_;
goto v_resetjp_6096_;
}
v_resetjp_6096_:
{
lean_object* v___x_6100_; 
if (v_isShared_6098_ == 0)
{
v___x_6100_ = v___x_6097_;
goto v_reusejp_6099_;
}
else
{
lean_object* v_reuseFailAlloc_6101_; 
v_reuseFailAlloc_6101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6101_, 0, v_a_6095_);
v___x_6100_ = v_reuseFailAlloc_6101_;
goto v_reusejp_6099_;
}
v_reusejp_6099_:
{
return v___x_6100_;
}
}
}
}
v___jp_6103_:
{
lean_object* v___x_6121_; 
v___x_6121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6121_, 0, v___y_6117_);
v___y_6069_ = v___y_6110_;
v___y_6070_ = v___y_6116_;
v___y_6071_ = v___y_6112_;
v___y_6072_ = v___y_6113_;
v___y_6073_ = v___y_6109_;
v___y_6074_ = v___y_6108_;
v___y_6075_ = v___y_6105_;
v___y_6076_ = v___y_6106_;
v___y_6077_ = v___y_6107_;
v___y_6078_ = v___y_6111_;
v___y_6079_ = v___y_6118_;
v___y_6080_ = v___y_6114_;
v___y_6081_ = v___x_6121_;
v___y_6082_ = v___y_6119_;
v___y_6083_ = v___y_6104_;
v___y_6084_ = v___y_6115_;
v___y_6085_ = v___y_6120_;
goto v___jp_6068_;
}
v___jp_6122_:
{
lean_object* v___x_6140_; lean_object* v___x_6141_; 
v___x_6140_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6141_ = l_Lean_Core_mkFreshUserName(v___x_6140_, v___y_6135_, v___y_6132_);
if (lean_obj_tag(v___x_6141_) == 0)
{
lean_object* v_a_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___y_6146_; uint8_t v___x_6147_; lean_object* v___x_6148_; 
v_a_6142_ = lean_ctor_get(v___x_6141_, 0);
lean_inc(v_a_6142_);
lean_dec_ref_known(v___x_6141_, 1);
v___x_6143_ = l_Lean_mkIdentFrom(v___y_6136_, v_a_6142_, v___y_6133_);
lean_dec(v___y_6136_);
v___x_6144_ = lean_box(v___y_6131_);
v___x_6145_ = lean_box(v___x_6065_);
lean_inc(v___x_6143_);
lean_inc(v___y_6134_);
v___y_6146_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed), 21, 13);
lean_closure_set(v___y_6146_, 0, v___y_6137_);
lean_closure_set(v___y_6146_, 1, v___x_6144_);
lean_closure_set(v___y_6146_, 2, v___x_6061_);
lean_closure_set(v___y_6146_, 3, v___x_6062_);
lean_closure_set(v___y_6146_, 4, v___x_6063_);
lean_closure_set(v___y_6146_, 5, v___y_6134_);
lean_closure_set(v___y_6146_, 6, v___y_6127_);
lean_closure_set(v___y_6146_, 7, v___x_6143_);
lean_closure_set(v___y_6146_, 8, v_dec_6052_);
lean_closure_set(v___y_6146_, 9, v___x_6145_);
lean_closure_set(v___y_6146_, 10, v___y_6128_);
lean_closure_set(v___y_6146_, 11, v___x_6067_);
lean_closure_set(v___y_6146_, 12, v___y_6139_);
v___x_6147_ = 0;
v___x_6148_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6143_, v___y_6129_, v___y_6124_, v___y_6146_, v___x_6147_, v___y_6126_, v___y_6123_, v___y_6125_, v___y_6130_, v___y_6138_, v___y_6135_, v___y_6132_);
return v___x_6148_;
}
else
{
lean_object* v_a_6149_; lean_object* v___x_6151_; uint8_t v_isShared_6152_; uint8_t v_isSharedCheck_6156_; 
lean_dec(v___y_6139_);
lean_dec(v___y_6137_);
lean_dec(v___y_6136_);
lean_dec(v___y_6129_);
lean_dec(v___y_6128_);
lean_dec(v___y_6127_);
lean_dec(v___y_6124_);
lean_dec_ref(v_dec_6052_);
v_a_6149_ = lean_ctor_get(v___x_6141_, 0);
v_isSharedCheck_6156_ = !lean_is_exclusive(v___x_6141_);
if (v_isSharedCheck_6156_ == 0)
{
v___x_6151_ = v___x_6141_;
v_isShared_6152_ = v_isSharedCheck_6156_;
goto v_resetjp_6150_;
}
else
{
lean_inc(v_a_6149_);
lean_dec(v___x_6141_);
v___x_6151_ = lean_box(0);
v_isShared_6152_ = v_isSharedCheck_6156_;
goto v_resetjp_6150_;
}
v_resetjp_6150_:
{
lean_object* v___x_6154_; 
if (v_isShared_6152_ == 0)
{
v___x_6154_ = v___x_6151_;
goto v_reusejp_6153_;
}
else
{
lean_object* v_reuseFailAlloc_6155_; 
v_reuseFailAlloc_6155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6155_, 0, v_a_6149_);
v___x_6154_ = v_reuseFailAlloc_6155_;
goto v_reusejp_6153_;
}
v_reusejp_6153_:
{
return v___x_6154_;
}
}
}
}
v___jp_6157_:
{
lean_object* v___x_6175_; 
v___x_6175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6175_, 0, v___y_6169_);
v___y_6123_ = v___y_6165_;
v___y_6124_ = v___y_6162_;
v___y_6125_ = v___y_6173_;
v___y_6126_ = v___y_6170_;
v___y_6127_ = v___y_6160_;
v___y_6128_ = v___y_6161_;
v___y_6129_ = v___y_6168_;
v___y_6130_ = v___y_6163_;
v___y_6131_ = v___y_6158_;
v___y_6132_ = v___y_6172_;
v___y_6133_ = v___y_6164_;
v___y_6134_ = v___y_6159_;
v___y_6135_ = v___y_6171_;
v___y_6136_ = v___y_6166_;
v___y_6137_ = v___x_6175_;
v___y_6138_ = v___y_6167_;
v___y_6139_ = v___y_6174_;
goto v___jp_6122_;
}
v___jp_6178_:
{
lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; uint8_t v___x_6201_; 
v___x_6198_ = l_Lean_Syntax_getArg(v___y_6187_, v___y_6184_);
v___x_6199_ = lean_unsigned_to_nat(4u);
v___x_6200_ = l_Lean_Syntax_getArg(v___y_6187_, v___x_6199_);
lean_dec(v___y_6187_);
lean_inc(v___x_6200_);
v___x_6201_ = l_Lean_Syntax_matchesNull(v___x_6200_, v___x_6067_);
if (v___x_6201_ == 0)
{
uint8_t v___x_6202_; 
lean_dec(v___y_6183_);
lean_dec(v_tk_6176_);
v___x_6202_ = l_Lean_Syntax_isNone(v___x_6200_);
if (v___x_6202_ == 0)
{
uint8_t v___x_6203_; 
lean_inc(v___x_6200_);
v___x_6203_ = l_Lean_Syntax_matchesNull(v___x_6200_, v___y_6184_);
if (v___x_6203_ == 0)
{
lean_object* v___x_6204_; 
lean_dec(v___x_6200_);
lean_dec(v___x_6198_);
lean_dec(v_patType_x3f_6190_);
lean_dec(v___y_6186_);
lean_dec(v___y_6181_);
lean_dec(v___y_6180_);
lean_dec_ref(v_dec_6052_);
v___x_6204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6204_;
}
else
{
lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; 
v___x_6205_ = l_Lean_Syntax_getArg(v___x_6200_, v___x_6177_);
v___x_6206_ = l_Lean_Syntax_getArg(v___x_6200_, v___y_6188_);
lean_dec(v___x_6200_);
v___x_6207_ = l_Lean_Syntax_getOptional_x3f(v___x_6206_);
lean_dec(v___x_6206_);
if (lean_obj_tag(v___x_6207_) == 0)
{
lean_inc(v___y_6189_);
v___y_6104_ = v___y_6179_;
v___y_6105_ = v___y_6182_;
v___y_6106_ = v___y_6181_;
v___y_6107_ = v___y_6180_;
v___y_6108_ = v___y_6196_;
v___y_6109_ = v___y_6194_;
v___y_6110_ = v___y_6185_;
v___y_6111_ = v___y_6186_;
v___y_6112_ = v___y_6192_;
v___y_6113_ = v___y_6197_;
v___y_6114_ = v___y_6193_;
v___y_6115_ = v___y_6195_;
v___y_6116_ = v___y_6191_;
v___y_6117_ = v___x_6205_;
v___y_6118_ = v___x_6198_;
v___y_6119_ = v_patType_x3f_6190_;
v___y_6120_ = v___y_6189_;
goto v___jp_6103_;
}
else
{
lean_object* v_val_6208_; lean_object* v___x_6210_; uint8_t v_isShared_6211_; uint8_t v_isSharedCheck_6215_; 
v_val_6208_ = lean_ctor_get(v___x_6207_, 0);
v_isSharedCheck_6215_ = !lean_is_exclusive(v___x_6207_);
if (v_isSharedCheck_6215_ == 0)
{
v___x_6210_ = v___x_6207_;
v_isShared_6211_ = v_isSharedCheck_6215_;
goto v_resetjp_6209_;
}
else
{
lean_inc(v_val_6208_);
lean_dec(v___x_6207_);
v___x_6210_ = lean_box(0);
v_isShared_6211_ = v_isSharedCheck_6215_;
goto v_resetjp_6209_;
}
v_resetjp_6209_:
{
lean_object* v___x_6213_; 
if (v_isShared_6211_ == 0)
{
v___x_6213_ = v___x_6210_;
goto v_reusejp_6212_;
}
else
{
lean_object* v_reuseFailAlloc_6214_; 
v_reuseFailAlloc_6214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6214_, 0, v_val_6208_);
v___x_6213_ = v_reuseFailAlloc_6214_;
goto v_reusejp_6212_;
}
v_reusejp_6212_:
{
v___y_6104_ = v___y_6179_;
v___y_6105_ = v___y_6182_;
v___y_6106_ = v___y_6181_;
v___y_6107_ = v___y_6180_;
v___y_6108_ = v___y_6196_;
v___y_6109_ = v___y_6194_;
v___y_6110_ = v___y_6185_;
v___y_6111_ = v___y_6186_;
v___y_6112_ = v___y_6192_;
v___y_6113_ = v___y_6197_;
v___y_6114_ = v___y_6193_;
v___y_6115_ = v___y_6195_;
v___y_6116_ = v___y_6191_;
v___y_6117_ = v___x_6205_;
v___y_6118_ = v___x_6198_;
v___y_6119_ = v_patType_x3f_6190_;
v___y_6120_ = v___x_6213_;
goto v___jp_6103_;
}
}
}
}
}
else
{
lean_dec(v___x_6200_);
lean_inc_n(v___y_6189_, 2);
v___y_6069_ = v___y_6185_;
v___y_6070_ = v___y_6191_;
v___y_6071_ = v___y_6192_;
v___y_6072_ = v___y_6197_;
v___y_6073_ = v___y_6194_;
v___y_6074_ = v___y_6196_;
v___y_6075_ = v___y_6182_;
v___y_6076_ = v___y_6181_;
v___y_6077_ = v___y_6180_;
v___y_6078_ = v___y_6186_;
v___y_6079_ = v___x_6198_;
v___y_6080_ = v___y_6193_;
v___y_6081_ = v___y_6189_;
v___y_6082_ = v_patType_x3f_6190_;
v___y_6083_ = v___y_6179_;
v___y_6084_ = v___y_6195_;
v___y_6085_ = v___y_6189_;
goto v___jp_6068_;
}
}
else
{
lean_object* v___x_6216_; lean_object* v___x_6217_; 
lean_dec(v___x_6200_);
lean_dec(v___y_6186_);
lean_dec(v___y_6181_);
lean_dec(v___y_6180_);
v___x_6216_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6217_ = l_Lean_Core_mkFreshUserName(v___x_6216_, v___y_6196_, v___y_6197_);
if (lean_obj_tag(v___x_6217_) == 0)
{
lean_object* v_a_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; 
v_a_6218_ = lean_ctor_get(v___x_6217_, 0);
lean_inc(v_a_6218_);
lean_dec_ref_known(v___x_6217_, 1);
v___x_6219_ = l_Lean_mkIdentFrom(v___y_6183_, v_a_6218_, v___y_6185_);
lean_dec(v___y_6183_);
v___x_6220_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_6052_, v_tk_6176_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_);
lean_dec(v_tk_6176_);
if (lean_obj_tag(v___x_6220_) == 0)
{
lean_object* v_a_6221_; uint8_t v_kind_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; 
v_a_6221_ = lean_ctor_get(v___x_6220_, 0);
lean_inc(v_a_6221_);
lean_dec_ref_known(v___x_6220_, 1);
v_kind_6222_ = lean_ctor_get_uint8(v_a_6221_, sizeof(void*)*3);
v___x_6223_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6223_, 0, v_a_6221_);
v___x_6224_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6219_, v_patType_x3f_6190_, v___x_6198_, v___x_6223_, v_kind_6222_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_);
return v___x_6224_;
}
else
{
lean_object* v_a_6225_; lean_object* v___x_6227_; uint8_t v_isShared_6228_; uint8_t v_isSharedCheck_6232_; 
lean_dec(v___x_6219_);
lean_dec(v___x_6198_);
lean_dec(v_patType_x3f_6190_);
v_a_6225_ = lean_ctor_get(v___x_6220_, 0);
v_isSharedCheck_6232_ = !lean_is_exclusive(v___x_6220_);
if (v_isSharedCheck_6232_ == 0)
{
v___x_6227_ = v___x_6220_;
v_isShared_6228_ = v_isSharedCheck_6232_;
goto v_resetjp_6226_;
}
else
{
lean_inc(v_a_6225_);
lean_dec(v___x_6220_);
v___x_6227_ = lean_box(0);
v_isShared_6228_ = v_isSharedCheck_6232_;
goto v_resetjp_6226_;
}
v_resetjp_6226_:
{
lean_object* v___x_6230_; 
if (v_isShared_6228_ == 0)
{
v___x_6230_ = v___x_6227_;
goto v_reusejp_6229_;
}
else
{
lean_object* v_reuseFailAlloc_6231_; 
v_reuseFailAlloc_6231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6231_, 0, v_a_6225_);
v___x_6230_ = v_reuseFailAlloc_6231_;
goto v_reusejp_6229_;
}
v_reusejp_6229_:
{
return v___x_6230_;
}
}
}
}
else
{
lean_object* v_a_6233_; lean_object* v___x_6235_; uint8_t v_isShared_6236_; uint8_t v_isSharedCheck_6240_; 
lean_dec(v___x_6198_);
lean_dec(v_patType_x3f_6190_);
lean_dec(v___y_6183_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v_a_6233_ = lean_ctor_get(v___x_6217_, 0);
v_isSharedCheck_6240_ = !lean_is_exclusive(v___x_6217_);
if (v_isSharedCheck_6240_ == 0)
{
v___x_6235_ = v___x_6217_;
v_isShared_6236_ = v_isSharedCheck_6240_;
goto v_resetjp_6234_;
}
else
{
lean_inc(v_a_6233_);
lean_dec(v___x_6217_);
v___x_6235_ = lean_box(0);
v_isShared_6236_ = v_isSharedCheck_6240_;
goto v_resetjp_6234_;
}
v_resetjp_6234_:
{
lean_object* v___x_6238_; 
if (v_isShared_6236_ == 0)
{
v___x_6238_ = v___x_6235_;
goto v_reusejp_6237_;
}
else
{
lean_object* v_reuseFailAlloc_6239_; 
v_reuseFailAlloc_6239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6239_, 0, v_a_6233_);
v___x_6238_ = v_reuseFailAlloc_6239_;
goto v_reusejp_6237_;
}
v_reusejp_6237_:
{
return v___x_6238_;
}
}
}
}
}
v___jp_6241_:
{
lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; uint8_t v___x_6263_; 
v___x_6260_ = l_Lean_Syntax_getArg(v___y_6249_, v___y_6246_);
v___x_6261_ = lean_unsigned_to_nat(4u);
v___x_6262_ = l_Lean_Syntax_getArg(v___y_6249_, v___x_6261_);
lean_dec(v___y_6249_);
v___x_6263_ = l_Lean_Syntax_isNone(v___x_6262_);
if (v___x_6263_ == 0)
{
uint8_t v___x_6264_; 
lean_inc(v___x_6262_);
v___x_6264_ = l_Lean_Syntax_matchesNull(v___x_6262_, v___y_6246_);
if (v___x_6264_ == 0)
{
lean_object* v___x_6265_; 
lean_dec(v___x_6262_);
lean_dec(v___x_6260_);
lean_dec(v_patType_x3f_6252_);
lean_dec(v___y_6248_);
lean_dec(v___y_6245_);
lean_dec(v___y_6244_);
lean_dec_ref(v_dec_6052_);
v___x_6265_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6265_;
}
else
{
lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; 
v___x_6266_ = l_Lean_Syntax_getArg(v___x_6262_, v___x_6177_);
v___x_6267_ = l_Lean_Syntax_getArg(v___x_6262_, v___y_6250_);
lean_dec(v___x_6262_);
v___x_6268_ = l_Lean_Syntax_getOptional_x3f(v___x_6267_);
lean_dec(v___x_6267_);
if (lean_obj_tag(v___x_6268_) == 0)
{
lean_inc(v___y_6251_);
v___y_6158_ = v___y_6242_;
v___y_6159_ = v___y_6243_;
v___y_6160_ = v___y_6245_;
v___y_6161_ = v___y_6244_;
v___y_6162_ = v___x_6260_;
v___y_6163_ = v___y_6256_;
v___y_6164_ = v___y_6247_;
v___y_6165_ = v___y_6254_;
v___y_6166_ = v___y_6248_;
v___y_6167_ = v___y_6257_;
v___y_6168_ = v_patType_x3f_6252_;
v___y_6169_ = v___x_6266_;
v___y_6170_ = v___y_6253_;
v___y_6171_ = v___y_6258_;
v___y_6172_ = v___y_6259_;
v___y_6173_ = v___y_6255_;
v___y_6174_ = v___y_6251_;
goto v___jp_6157_;
}
else
{
lean_object* v_val_6269_; lean_object* v___x_6271_; uint8_t v_isShared_6272_; uint8_t v_isSharedCheck_6276_; 
v_val_6269_ = lean_ctor_get(v___x_6268_, 0);
v_isSharedCheck_6276_ = !lean_is_exclusive(v___x_6268_);
if (v_isSharedCheck_6276_ == 0)
{
v___x_6271_ = v___x_6268_;
v_isShared_6272_ = v_isSharedCheck_6276_;
goto v_resetjp_6270_;
}
else
{
lean_inc(v_val_6269_);
lean_dec(v___x_6268_);
v___x_6271_ = lean_box(0);
v_isShared_6272_ = v_isSharedCheck_6276_;
goto v_resetjp_6270_;
}
v_resetjp_6270_:
{
lean_object* v___x_6274_; 
if (v_isShared_6272_ == 0)
{
v___x_6274_ = v___x_6271_;
goto v_reusejp_6273_;
}
else
{
lean_object* v_reuseFailAlloc_6275_; 
v_reuseFailAlloc_6275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6275_, 0, v_val_6269_);
v___x_6274_ = v_reuseFailAlloc_6275_;
goto v_reusejp_6273_;
}
v_reusejp_6273_:
{
v___y_6158_ = v___y_6242_;
v___y_6159_ = v___y_6243_;
v___y_6160_ = v___y_6245_;
v___y_6161_ = v___y_6244_;
v___y_6162_ = v___x_6260_;
v___y_6163_ = v___y_6256_;
v___y_6164_ = v___y_6247_;
v___y_6165_ = v___y_6254_;
v___y_6166_ = v___y_6248_;
v___y_6167_ = v___y_6257_;
v___y_6168_ = v_patType_x3f_6252_;
v___y_6169_ = v___x_6266_;
v___y_6170_ = v___y_6253_;
v___y_6171_ = v___y_6258_;
v___y_6172_ = v___y_6259_;
v___y_6173_ = v___y_6255_;
v___y_6174_ = v___x_6274_;
goto v___jp_6157_;
}
}
}
}
}
else
{
lean_dec(v___x_6262_);
lean_inc_n(v___y_6251_, 2);
v___y_6123_ = v___y_6254_;
v___y_6124_ = v___x_6260_;
v___y_6125_ = v___y_6255_;
v___y_6126_ = v___y_6253_;
v___y_6127_ = v___y_6245_;
v___y_6128_ = v___y_6244_;
v___y_6129_ = v_patType_x3f_6252_;
v___y_6130_ = v___y_6256_;
v___y_6131_ = v___y_6242_;
v___y_6132_ = v___y_6259_;
v___y_6133_ = v___y_6247_;
v___y_6134_ = v___y_6243_;
v___y_6135_ = v___y_6258_;
v___y_6136_ = v___y_6248_;
v___y_6137_ = v___y_6251_;
v___y_6138_ = v___y_6257_;
v___y_6139_ = v___y_6251_;
goto v___jp_6122_;
}
}
v___jp_6277_:
{
lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; 
v___x_6291_ = l_Lean_Syntax_getArg(v___y_6282_, v___y_6278_);
lean_dec(v___y_6282_);
v___x_6292_ = lean_mk_empty_array_with_capacity(v___x_6177_);
lean_inc(v___y_6280_);
v___x_6293_ = lean_array_push(v___x_6292_, v___y_6280_);
v___x_6294_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_6293_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_);
lean_dec_ref(v___x_6293_);
if (lean_obj_tag(v___x_6294_) == 0)
{
lean_object* v___x_6295_; 
lean_dec_ref_known(v___x_6294_, 1);
v___x_6295_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_6052_, v_tk_6176_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_);
lean_dec(v_tk_6176_);
if (lean_obj_tag(v___x_6295_) == 0)
{
lean_object* v_a_6296_; uint8_t v_kind_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; 
v_a_6296_ = lean_ctor_get(v___x_6295_, 0);
lean_inc(v_a_6296_);
lean_dec_ref_known(v___x_6295_, 1);
v_kind_6297_ = lean_ctor_get_uint8(v_a_6296_, sizeof(void*)*3);
v___x_6298_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6298_, 0, v_a_6296_);
v___x_6299_ = lean_box(v___y_6279_);
lean_inc(v___y_6280_);
v___x_6300_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 13, 5);
lean_closure_set(v___x_6300_, 0, lean_box(0));
lean_closure_set(v___x_6300_, 1, v___y_6281_);
lean_closure_set(v___x_6300_, 2, v___y_6280_);
lean_closure_set(v___x_6300_, 3, v___x_6299_);
lean_closure_set(v___x_6300_, 4, v___x_6298_);
v___x_6301_ = l_Lean_Elab_Do_elabDoIdDecl(v___y_6280_, v_xType_x3f_6283_, v___x_6291_, v___x_6300_, v_kind_6297_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_);
return v___x_6301_;
}
else
{
lean_object* v_a_6302_; lean_object* v___x_6304_; uint8_t v_isShared_6305_; uint8_t v_isSharedCheck_6309_; 
lean_dec(v___x_6291_);
lean_dec(v_xType_x3f_6283_);
lean_dec(v___y_6281_);
lean_dec(v___y_6280_);
v_a_6302_ = lean_ctor_get(v___x_6295_, 0);
v_isSharedCheck_6309_ = !lean_is_exclusive(v___x_6295_);
if (v_isSharedCheck_6309_ == 0)
{
v___x_6304_ = v___x_6295_;
v_isShared_6305_ = v_isSharedCheck_6309_;
goto v_resetjp_6303_;
}
else
{
lean_inc(v_a_6302_);
lean_dec(v___x_6295_);
v___x_6304_ = lean_box(0);
v_isShared_6305_ = v_isSharedCheck_6309_;
goto v_resetjp_6303_;
}
v_resetjp_6303_:
{
lean_object* v___x_6307_; 
if (v_isShared_6305_ == 0)
{
v___x_6307_ = v___x_6304_;
goto v_reusejp_6306_;
}
else
{
lean_object* v_reuseFailAlloc_6308_; 
v_reuseFailAlloc_6308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6308_, 0, v_a_6302_);
v___x_6307_ = v_reuseFailAlloc_6308_;
goto v_reusejp_6306_;
}
v_reusejp_6306_:
{
return v___x_6307_;
}
}
}
}
else
{
lean_object* v_a_6310_; lean_object* v___x_6312_; uint8_t v_isShared_6313_; uint8_t v_isSharedCheck_6317_; 
lean_dec(v___x_6291_);
lean_dec(v_xType_x3f_6283_);
lean_dec(v___y_6281_);
lean_dec(v___y_6280_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v_a_6310_ = lean_ctor_get(v___x_6294_, 0);
v_isSharedCheck_6317_ = !lean_is_exclusive(v___x_6294_);
if (v_isSharedCheck_6317_ == 0)
{
v___x_6312_ = v___x_6294_;
v_isShared_6313_ = v_isSharedCheck_6317_;
goto v_resetjp_6311_;
}
else
{
lean_inc(v_a_6310_);
lean_dec(v___x_6294_);
v___x_6312_ = lean_box(0);
v_isShared_6313_ = v_isSharedCheck_6317_;
goto v_resetjp_6311_;
}
v_resetjp_6311_:
{
lean_object* v___x_6315_; 
if (v_isShared_6313_ == 0)
{
v___x_6315_ = v___x_6312_;
goto v_reusejp_6314_;
}
else
{
lean_object* v_reuseFailAlloc_6316_; 
v_reuseFailAlloc_6316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6316_, 0, v_a_6310_);
v___x_6315_ = v_reuseFailAlloc_6316_;
goto v_reusejp_6314_;
}
v_reusejp_6314_:
{
return v___x_6315_;
}
}
}
}
v___jp_6318_:
{
uint8_t v___x_6336_; 
lean_inc(v___y_6326_);
v___x_6336_ = l_Lean_Syntax_isOfKind(v___y_6326_, v___y_6325_);
if (v___x_6336_ == 0)
{
uint8_t v___x_6337_; 
lean_dec(v___y_6324_);
lean_inc(v___y_6326_);
v___x_6337_ = l_Lean_Syntax_isOfKind(v___y_6326_, v___y_6323_);
if (v___x_6337_ == 0)
{
lean_object* v___x_6338_; 
lean_dec(v___y_6326_);
lean_dec(v___y_6320_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v___x_6338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6338_;
}
else
{
lean_object* v___x_6339_; lean_object* v___x_6340_; uint8_t v___x_6341_; 
v___x_6339_ = l_Lean_Syntax_getArg(v___y_6326_, v___x_6067_);
v___x_6340_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
lean_inc(v___x_6339_);
v___x_6341_ = l_Lean_Syntax_isOfKind(v___x_6339_, v___x_6340_);
if (v___x_6341_ == 0)
{
lean_object* v___x_6342_; uint8_t v___x_6343_; 
lean_dec(v_tk_6176_);
v___x_6342_ = l_Lean_Syntax_getArg(v___y_6326_, v___x_6177_);
v___x_6343_ = l_Lean_Syntax_isNone(v___x_6342_);
if (v___x_6343_ == 0)
{
uint8_t v___x_6344_; 
lean_inc(v___x_6342_);
v___x_6344_ = l_Lean_Syntax_matchesNull(v___x_6342_, v___x_6177_);
if (v___x_6344_ == 0)
{
lean_object* v___x_6345_; 
lean_dec(v___x_6342_);
lean_dec(v___x_6339_);
lean_dec(v___y_6326_);
lean_dec(v___y_6320_);
lean_dec_ref(v_dec_6052_);
v___x_6345_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6345_;
}
else
{
lean_object* v___x_6346_; lean_object* v___x_6347_; uint8_t v___x_6348_; 
v___x_6346_ = l_Lean_Syntax_getArg(v___x_6342_, v___x_6067_);
lean_dec(v___x_6342_);
v___x_6347_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6346_);
v___x_6348_ = l_Lean_Syntax_isOfKind(v___x_6346_, v___x_6347_);
if (v___x_6348_ == 0)
{
lean_object* v___x_6349_; 
lean_dec(v___x_6346_);
lean_dec(v___x_6339_);
lean_dec(v___y_6326_);
lean_dec(v___y_6320_);
lean_dec_ref(v_dec_6052_);
v___x_6349_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6349_;
}
else
{
lean_object* v___x_6350_; lean_object* v___x_6351_; 
v___x_6350_ = l_Lean_Syntax_getArg(v___x_6346_, v___x_6177_);
lean_dec(v___x_6346_);
v___x_6351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6351_, 0, v___x_6350_);
lean_inc(v___x_6339_);
v___y_6242_ = v___x_6341_;
v___y_6243_ = v___y_6319_;
v___y_6244_ = v___y_6320_;
v___y_6245_ = v___x_6339_;
v___y_6246_ = v___y_6321_;
v___y_6247_ = v___y_6322_;
v___y_6248_ = v___x_6339_;
v___y_6249_ = v___y_6326_;
v___y_6250_ = v___y_6328_;
v___y_6251_ = v___y_6327_;
v_patType_x3f_6252_ = v___x_6351_;
v___y_6253_ = v___y_6329_;
v___y_6254_ = v___y_6330_;
v___y_6255_ = v___y_6331_;
v___y_6256_ = v___y_6332_;
v___y_6257_ = v___y_6333_;
v___y_6258_ = v___y_6334_;
v___y_6259_ = v___y_6335_;
goto v___jp_6241_;
}
}
}
else
{
lean_dec(v___x_6342_);
lean_inc(v___y_6327_);
lean_inc(v___x_6339_);
v___y_6242_ = v___x_6341_;
v___y_6243_ = v___y_6319_;
v___y_6244_ = v___y_6320_;
v___y_6245_ = v___x_6339_;
v___y_6246_ = v___y_6321_;
v___y_6247_ = v___y_6322_;
v___y_6248_ = v___x_6339_;
v___y_6249_ = v___y_6326_;
v___y_6250_ = v___y_6328_;
v___y_6251_ = v___y_6327_;
v_patType_x3f_6252_ = v___y_6327_;
v___y_6253_ = v___y_6329_;
v___y_6254_ = v___y_6330_;
v___y_6255_ = v___y_6331_;
v___y_6256_ = v___y_6332_;
v___y_6257_ = v___y_6333_;
v___y_6258_ = v___y_6334_;
v___y_6259_ = v___y_6335_;
goto v___jp_6241_;
}
}
else
{
lean_object* v___x_6352_; lean_object* v___x_6353_; uint8_t v___x_6354_; 
v___x_6352_ = l_Lean_Syntax_getArg(v___x_6339_, v___x_6067_);
v___x_6353_ = l_Lean_Syntax_getArg(v___y_6326_, v___x_6177_);
v___x_6354_ = l_Lean_Syntax_isNone(v___x_6353_);
if (v___x_6354_ == 0)
{
uint8_t v___x_6355_; 
lean_inc(v___x_6353_);
v___x_6355_ = l_Lean_Syntax_matchesNull(v___x_6353_, v___x_6177_);
if (v___x_6355_ == 0)
{
lean_object* v___x_6356_; 
lean_dec(v___x_6353_);
lean_dec(v___x_6352_);
lean_dec(v___x_6339_);
lean_dec(v___y_6326_);
lean_dec(v___y_6320_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v___x_6356_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6356_;
}
else
{
lean_object* v___x_6357_; lean_object* v___x_6358_; uint8_t v___x_6359_; 
v___x_6357_ = l_Lean_Syntax_getArg(v___x_6353_, v___x_6067_);
lean_dec(v___x_6353_);
v___x_6358_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6357_);
v___x_6359_ = l_Lean_Syntax_isOfKind(v___x_6357_, v___x_6358_);
if (v___x_6359_ == 0)
{
lean_object* v___x_6360_; 
lean_dec(v___x_6357_);
lean_dec(v___x_6352_);
lean_dec(v___x_6339_);
lean_dec(v___y_6326_);
lean_dec(v___y_6320_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v___x_6360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6360_;
}
else
{
lean_object* v___x_6361_; lean_object* v___x_6362_; 
v___x_6361_ = l_Lean_Syntax_getArg(v___x_6357_, v___x_6177_);
lean_dec(v___x_6357_);
v___x_6362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6362_, 0, v___x_6361_);
lean_inc(v___x_6339_);
v___y_6179_ = v___y_6319_;
v___y_6180_ = v___y_6320_;
v___y_6181_ = v___x_6339_;
v___y_6182_ = v___x_6336_;
v___y_6183_ = v___x_6352_;
v___y_6184_ = v___y_6321_;
v___y_6185_ = v___y_6322_;
v___y_6186_ = v___x_6339_;
v___y_6187_ = v___y_6326_;
v___y_6188_ = v___y_6328_;
v___y_6189_ = v___y_6327_;
v_patType_x3f_6190_ = v___x_6362_;
v___y_6191_ = v___y_6329_;
v___y_6192_ = v___y_6330_;
v___y_6193_ = v___y_6331_;
v___y_6194_ = v___y_6332_;
v___y_6195_ = v___y_6333_;
v___y_6196_ = v___y_6334_;
v___y_6197_ = v___y_6335_;
goto v___jp_6178_;
}
}
}
else
{
lean_dec(v___x_6353_);
lean_inc(v___y_6327_);
lean_inc(v___x_6339_);
v___y_6179_ = v___y_6319_;
v___y_6180_ = v___y_6320_;
v___y_6181_ = v___x_6339_;
v___y_6182_ = v___x_6336_;
v___y_6183_ = v___x_6352_;
v___y_6184_ = v___y_6321_;
v___y_6185_ = v___y_6322_;
v___y_6186_ = v___x_6339_;
v___y_6187_ = v___y_6326_;
v___y_6188_ = v___y_6328_;
v___y_6189_ = v___y_6327_;
v_patType_x3f_6190_ = v___y_6327_;
v___y_6191_ = v___y_6329_;
v___y_6192_ = v___y_6330_;
v___y_6193_ = v___y_6331_;
v___y_6194_ = v___y_6332_;
v___y_6195_ = v___y_6333_;
v___y_6196_ = v___y_6334_;
v___y_6197_ = v___y_6335_;
goto v___jp_6178_;
}
}
}
}
else
{
lean_object* v___x_6363_; lean_object* v___x_6364_; uint8_t v___x_6365_; 
lean_dec(v___y_6320_);
v___x_6363_ = l_Lean_Syntax_getArg(v___y_6326_, v___x_6067_);
v___x_6364_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_6363_);
v___x_6365_ = l_Lean_Syntax_isOfKind(v___x_6363_, v___x_6364_);
if (v___x_6365_ == 0)
{
lean_object* v___x_6366_; 
lean_dec(v___x_6363_);
lean_dec(v___y_6326_);
lean_dec(v___y_6324_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v___x_6366_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6366_;
}
else
{
lean_object* v___x_6367_; uint8_t v___x_6368_; 
v___x_6367_ = l_Lean_Syntax_getArg(v___y_6326_, v___x_6177_);
v___x_6368_ = l_Lean_Syntax_isNone(v___x_6367_);
if (v___x_6368_ == 0)
{
uint8_t v___x_6369_; 
lean_inc(v___x_6367_);
v___x_6369_ = l_Lean_Syntax_matchesNull(v___x_6367_, v___x_6177_);
if (v___x_6369_ == 0)
{
lean_object* v___x_6370_; 
lean_dec(v___x_6367_);
lean_dec(v___x_6363_);
lean_dec(v___y_6326_);
lean_dec(v___y_6324_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v___x_6370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6370_;
}
else
{
lean_object* v___x_6371_; lean_object* v___x_6372_; uint8_t v___x_6373_; 
v___x_6371_ = l_Lean_Syntax_getArg(v___x_6367_, v___x_6067_);
lean_dec(v___x_6367_);
v___x_6372_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6371_);
v___x_6373_ = l_Lean_Syntax_isOfKind(v___x_6371_, v___x_6372_);
if (v___x_6373_ == 0)
{
lean_object* v___x_6374_; 
lean_dec(v___x_6371_);
lean_dec(v___x_6363_);
lean_dec(v___y_6326_);
lean_dec(v___y_6324_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v___x_6374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6374_;
}
else
{
lean_object* v___x_6375_; lean_object* v___x_6376_; 
v___x_6375_ = l_Lean_Syntax_getArg(v___x_6371_, v___x_6177_);
lean_dec(v___x_6371_);
v___x_6376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6376_, 0, v___x_6375_);
v___y_6278_ = v___y_6321_;
v___y_6279_ = v___y_6322_;
v___y_6280_ = v___x_6363_;
v___y_6281_ = v___y_6324_;
v___y_6282_ = v___y_6326_;
v_xType_x3f_6283_ = v___x_6376_;
v___y_6284_ = v___y_6329_;
v___y_6285_ = v___y_6330_;
v___y_6286_ = v___y_6331_;
v___y_6287_ = v___y_6332_;
v___y_6288_ = v___y_6333_;
v___y_6289_ = v___y_6334_;
v___y_6290_ = v___y_6335_;
goto v___jp_6277_;
}
}
}
else
{
lean_dec(v___x_6367_);
lean_inc(v___y_6327_);
v___y_6278_ = v___y_6321_;
v___y_6279_ = v___y_6322_;
v___y_6280_ = v___x_6363_;
v___y_6281_ = v___y_6324_;
v___y_6282_ = v___y_6326_;
v_xType_x3f_6283_ = v___y_6327_;
v___y_6284_ = v___y_6329_;
v___y_6285_ = v___y_6330_;
v___y_6286_ = v___y_6331_;
v___y_6287_ = v___y_6332_;
v___y_6288_ = v___y_6333_;
v___y_6289_ = v___y_6334_;
v___y_6290_ = v___y_6335_;
goto v___jp_6277_;
}
}
}
}
v___jp_6377_:
{
lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v_a_6398_; lean_object* v___x_6400_; uint8_t v_isShared_6401_; uint8_t v_isSharedCheck_6405_; 
lean_dec(v___y_6385_);
lean_dec(v___y_6384_);
lean_dec(v___y_6379_);
v___x_6396_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__1, &l_Lean_Elab_Do_elabDoLetArrow___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1);
v___x_6397_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v___y_6386_, v___x_6396_, v___y_6380_, v___y_6388_, v___y_6382_, v___y_6392_, v___y_6391_, v___y_6393_, v___y_6389_);
lean_dec(v___y_6386_);
v_a_6398_ = lean_ctor_get(v___x_6397_, 0);
v_isSharedCheck_6405_ = !lean_is_exclusive(v___x_6397_);
if (v_isSharedCheck_6405_ == 0)
{
v___x_6400_ = v___x_6397_;
v_isShared_6401_ = v_isSharedCheck_6405_;
goto v_resetjp_6399_;
}
else
{
lean_inc(v_a_6398_);
lean_dec(v___x_6397_);
v___x_6400_ = lean_box(0);
v_isShared_6401_ = v_isSharedCheck_6405_;
goto v_resetjp_6399_;
}
v_resetjp_6399_:
{
lean_object* v___x_6403_; 
if (v_isShared_6401_ == 0)
{
v___x_6403_ = v___x_6400_;
goto v_reusejp_6402_;
}
else
{
lean_object* v_reuseFailAlloc_6404_; 
v_reuseFailAlloc_6404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6404_, 0, v_a_6398_);
v___x_6403_ = v_reuseFailAlloc_6404_;
goto v_reusejp_6402_;
}
v_reusejp_6402_:
{
return v___x_6403_;
}
}
}
v___jp_6406_:
{
lean_object* v___x_6415_; lean_object* v_cfg_6416_; lean_object* v___x_6417_; uint8_t v___x_6418_; 
v___x_6415_ = lean_unsigned_to_nat(2u);
v_cfg_6416_ = l_Lean_Syntax_getArg(v_stx_6051_, v___x_6415_);
v___x_6417_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_6416_);
v___x_6418_ = l_Lean_Syntax_isOfKind(v_cfg_6416_, v___x_6417_);
if (v___x_6418_ == 0)
{
lean_object* v___x_6419_; 
lean_dec(v_cfg_6416_);
lean_dec(v_mutTk_x3f_6407_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
lean_dec(v_stx_6051_);
v___x_6419_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6419_;
}
else
{
lean_object* v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; uint8_t v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; 
v___x_6420_ = lean_unsigned_to_nat(3u);
v___x_6421_ = l_Lean_Syntax_getArg(v_stx_6051_, v___x_6420_);
lean_dec(v_stx_6051_);
v___x_6422_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
v___x_6423_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
v___x_6424_ = 0;
v___x_6425_ = lean_box(0);
v___x_6426_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
lean_inc(v_cfg_6416_);
v___x_6427_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_cfg_6416_, v_mutTk_x3f_6407_, v___x_6426_, v___y_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
if (lean_obj_tag(v___x_6427_) == 0)
{
lean_object* v_a_6428_; lean_object* v___x_6429_; 
v_a_6428_ = lean_ctor_get(v___x_6427_, 0);
lean_inc(v_a_6428_);
lean_dec_ref_known(v___x_6427_, 1);
v___x_6429_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_6428_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
if (lean_obj_tag(v___x_6429_) == 0)
{
uint8_t v_nondep_6430_; 
lean_dec_ref_known(v___x_6429_, 1);
v_nondep_6430_ = lean_ctor_get_uint8(v_a_6428_, sizeof(void*)*1);
if (v_nondep_6430_ == 0)
{
uint8_t v_usedOnly_6431_; 
v_usedOnly_6431_ = lean_ctor_get_uint8(v_a_6428_, sizeof(void*)*1 + 1);
if (v_usedOnly_6431_ == 0)
{
uint8_t v_zeta_6432_; 
v_zeta_6432_ = lean_ctor_get_uint8(v_a_6428_, sizeof(void*)*1 + 2);
if (v_zeta_6432_ == 0)
{
lean_object* v_eq_x3f_6433_; 
v_eq_x3f_6433_ = lean_ctor_get(v_a_6428_, 0);
lean_inc(v_eq_x3f_6433_);
lean_dec(v_a_6428_);
if (lean_obj_tag(v_eq_x3f_6433_) == 0)
{
lean_dec(v_cfg_6416_);
lean_inc(v_mutTk_x3f_6407_);
v___y_6319_ = v___x_6417_;
v___y_6320_ = v_mutTk_x3f_6407_;
v___y_6321_ = v___x_6420_;
v___y_6322_ = v___x_6424_;
v___y_6323_ = v___x_6423_;
v___y_6324_ = v_mutTk_x3f_6407_;
v___y_6325_ = v___x_6422_;
v___y_6326_ = v___x_6421_;
v___y_6327_ = v___x_6425_;
v___y_6328_ = v___x_6415_;
v___y_6329_ = v___y_6408_;
v___y_6330_ = v___y_6409_;
v___y_6331_ = v___y_6410_;
v___y_6332_ = v___y_6411_;
v___y_6333_ = v___y_6412_;
v___y_6334_ = v___y_6413_;
v___y_6335_ = v___y_6414_;
goto v___jp_6318_;
}
else
{
lean_dec_ref_known(v_eq_x3f_6433_, 1);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
lean_inc(v_mutTk_x3f_6407_);
v___y_6378_ = v___x_6417_;
v___y_6379_ = v_mutTk_x3f_6407_;
v___y_6380_ = v___y_6408_;
v___y_6381_ = v___x_6424_;
v___y_6382_ = v___y_6410_;
v___y_6383_ = v___x_6423_;
v___y_6384_ = v_mutTk_x3f_6407_;
v___y_6385_ = v___x_6421_;
v___y_6386_ = v_cfg_6416_;
v___y_6387_ = v___x_6425_;
v___y_6388_ = v___y_6409_;
v___y_6389_ = v___y_6414_;
v___y_6390_ = v___x_6420_;
v___y_6391_ = v___y_6412_;
v___y_6392_ = v___y_6411_;
v___y_6393_ = v___y_6413_;
v___y_6394_ = v___x_6422_;
v___y_6395_ = v___x_6415_;
goto v___jp_6377_;
}
}
else
{
lean_dec(v_a_6428_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
lean_inc(v_mutTk_x3f_6407_);
v___y_6378_ = v___x_6417_;
v___y_6379_ = v_mutTk_x3f_6407_;
v___y_6380_ = v___y_6408_;
v___y_6381_ = v___x_6424_;
v___y_6382_ = v___y_6410_;
v___y_6383_ = v___x_6423_;
v___y_6384_ = v_mutTk_x3f_6407_;
v___y_6385_ = v___x_6421_;
v___y_6386_ = v_cfg_6416_;
v___y_6387_ = v___x_6425_;
v___y_6388_ = v___y_6409_;
v___y_6389_ = v___y_6414_;
v___y_6390_ = v___x_6420_;
v___y_6391_ = v___y_6412_;
v___y_6392_ = v___y_6411_;
v___y_6393_ = v___y_6413_;
v___y_6394_ = v___x_6422_;
v___y_6395_ = v___x_6415_;
goto v___jp_6377_;
}
}
else
{
lean_dec(v_a_6428_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
lean_inc(v_mutTk_x3f_6407_);
v___y_6378_ = v___x_6417_;
v___y_6379_ = v_mutTk_x3f_6407_;
v___y_6380_ = v___y_6408_;
v___y_6381_ = v___x_6424_;
v___y_6382_ = v___y_6410_;
v___y_6383_ = v___x_6423_;
v___y_6384_ = v_mutTk_x3f_6407_;
v___y_6385_ = v___x_6421_;
v___y_6386_ = v_cfg_6416_;
v___y_6387_ = v___x_6425_;
v___y_6388_ = v___y_6409_;
v___y_6389_ = v___y_6414_;
v___y_6390_ = v___x_6420_;
v___y_6391_ = v___y_6412_;
v___y_6392_ = v___y_6411_;
v___y_6393_ = v___y_6413_;
v___y_6394_ = v___x_6422_;
v___y_6395_ = v___x_6415_;
goto v___jp_6377_;
}
}
else
{
lean_dec(v_a_6428_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
lean_inc(v_mutTk_x3f_6407_);
v___y_6378_ = v___x_6417_;
v___y_6379_ = v_mutTk_x3f_6407_;
v___y_6380_ = v___y_6408_;
v___y_6381_ = v___x_6424_;
v___y_6382_ = v___y_6410_;
v___y_6383_ = v___x_6423_;
v___y_6384_ = v_mutTk_x3f_6407_;
v___y_6385_ = v___x_6421_;
v___y_6386_ = v_cfg_6416_;
v___y_6387_ = v___x_6425_;
v___y_6388_ = v___y_6409_;
v___y_6389_ = v___y_6414_;
v___y_6390_ = v___x_6420_;
v___y_6391_ = v___y_6412_;
v___y_6392_ = v___y_6411_;
v___y_6393_ = v___y_6413_;
v___y_6394_ = v___x_6422_;
v___y_6395_ = v___x_6415_;
goto v___jp_6377_;
}
}
else
{
lean_object* v_a_6434_; lean_object* v___x_6436_; uint8_t v_isShared_6437_; uint8_t v_isSharedCheck_6441_; 
lean_dec(v_a_6428_);
lean_dec(v___x_6421_);
lean_dec(v_cfg_6416_);
lean_dec(v_mutTk_x3f_6407_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v_a_6434_ = lean_ctor_get(v___x_6429_, 0);
v_isSharedCheck_6441_ = !lean_is_exclusive(v___x_6429_);
if (v_isSharedCheck_6441_ == 0)
{
v___x_6436_ = v___x_6429_;
v_isShared_6437_ = v_isSharedCheck_6441_;
goto v_resetjp_6435_;
}
else
{
lean_inc(v_a_6434_);
lean_dec(v___x_6429_);
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
else
{
lean_object* v_a_6442_; lean_object* v___x_6444_; uint8_t v_isShared_6445_; uint8_t v_isSharedCheck_6449_; 
lean_dec(v___x_6421_);
lean_dec(v_cfg_6416_);
lean_dec(v_mutTk_x3f_6407_);
lean_dec(v_tk_6176_);
lean_dec_ref(v_dec_6052_);
v_a_6442_ = lean_ctor_get(v___x_6427_, 0);
v_isSharedCheck_6449_ = !lean_is_exclusive(v___x_6427_);
if (v_isSharedCheck_6449_ == 0)
{
v___x_6444_ = v___x_6427_;
v_isShared_6445_ = v_isSharedCheck_6449_;
goto v_resetjp_6443_;
}
else
{
lean_inc(v_a_6442_);
lean_dec(v___x_6427_);
v___x_6444_ = lean_box(0);
v_isShared_6445_ = v_isSharedCheck_6449_;
goto v_resetjp_6443_;
}
v_resetjp_6443_:
{
lean_object* v___x_6447_; 
if (v_isShared_6445_ == 0)
{
v___x_6447_ = v___x_6444_;
goto v_reusejp_6446_;
}
else
{
lean_object* v_reuseFailAlloc_6448_; 
v_reuseFailAlloc_6448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6448_, 0, v_a_6442_);
v___x_6447_ = v_reuseFailAlloc_6448_;
goto v_reusejp_6446_;
}
v_reusejp_6446_:
{
return v___x_6447_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_6457_, lean_object* v_dec_6458_, lean_object* v_a_6459_, lean_object* v_a_6460_, lean_object* v_a_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_){
_start:
{
lean_object* v_res_6467_; 
v_res_6467_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_6457_, v_dec_6458_, v_a_6459_, v_a_6460_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_, v_a_6465_);
lean_dec(v_a_6465_);
lean_dec_ref(v_a_6464_);
lean_dec(v_a_6463_);
lean_dec_ref(v_a_6462_);
lean_dec(v_a_6461_);
lean_dec_ref(v_a_6460_);
lean_dec_ref(v_a_6459_);
return v_res_6467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; 
v___x_6475_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6476_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_6477_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_6478_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_6479_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6475_, v___x_6476_, v___x_6477_, v___x_6478_);
return v___x_6479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_6480_){
_start:
{
lean_object* v_res_6481_; 
v_res_6481_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_6481_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3(void){
_start:
{
lean_object* v___x_6489_; lean_object* v___x_6490_; 
v___x_6489_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__2));
v___x_6490_ = l_Lean_stringToMessageData(v___x_6489_);
return v___x_6490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_6491_, lean_object* v_dec_6492_, lean_object* v_a_6493_, lean_object* v_a_6494_, lean_object* v_a_6495_, lean_object* v_a_6496_, lean_object* v_a_6497_, lean_object* v_a_6498_, lean_object* v_a_6499_){
_start:
{
lean_object* v___x_6501_; uint8_t v___x_6502_; 
v___x_6501_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_6491_);
v___x_6502_ = l_Lean_Syntax_isOfKind(v_stx_6491_, v___x_6501_);
if (v___x_6502_ == 0)
{
lean_object* v___x_6503_; 
lean_dec_ref(v_dec_6492_);
lean_dec(v_stx_6491_);
v___x_6503_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6503_;
}
else
{
lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; uint8_t v___x_6507_; 
v___x_6504_ = lean_unsigned_to_nat(0u);
v___x_6505_ = l_Lean_Syntax_getArg(v_stx_6491_, v___x_6504_);
lean_dec(v_stx_6491_);
v___x_6506_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_6505_);
v___x_6507_ = l_Lean_Syntax_isOfKind(v___x_6505_, v___x_6506_);
if (v___x_6507_ == 0)
{
lean_object* v___x_6508_; uint8_t v___x_6509_; 
v___x_6508_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
lean_inc(v___x_6505_);
v___x_6509_ = l_Lean_Syntax_isOfKind(v___x_6505_, v___x_6508_);
if (v___x_6509_ == 0)
{
lean_object* v___x_6510_; 
lean_dec(v___x_6505_);
lean_dec_ref(v_dec_6492_);
v___x_6510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6510_;
}
else
{
lean_object* v___x_6511_; lean_object* v___y_6513_; lean_object* v___y_6514_; lean_object* v___y_6515_; lean_object* v___y_6516_; lean_object* v___y_6517_; lean_object* v___y_6518_; lean_object* v___y_6519_; lean_object* v___y_6520_; lean_object* v___y_6521_; lean_object* v_t_x3f_6550_; lean_object* v___y_6551_; lean_object* v___y_6552_; lean_object* v___y_6553_; lean_object* v___y_6554_; lean_object* v___y_6555_; lean_object* v___y_6556_; lean_object* v___y_6557_; lean_object* v___x_6575_; lean_object* v___x_6576_; uint8_t v___x_6577_; 
v___x_6511_ = l_Lean_Syntax_getArg(v___x_6505_, v___x_6504_);
v___x_6575_ = lean_unsigned_to_nat(1u);
v___x_6576_ = l_Lean_Syntax_getArg(v___x_6505_, v___x_6575_);
v___x_6577_ = l_Lean_Syntax_isNone(v___x_6576_);
if (v___x_6577_ == 0)
{
uint8_t v___x_6578_; 
lean_inc(v___x_6576_);
v___x_6578_ = l_Lean_Syntax_matchesNull(v___x_6576_, v___x_6575_);
if (v___x_6578_ == 0)
{
lean_object* v___x_6579_; 
lean_dec(v___x_6576_);
lean_dec(v___x_6511_);
lean_dec(v___x_6505_);
lean_dec_ref(v_dec_6492_);
v___x_6579_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6579_;
}
else
{
lean_object* v___x_6580_; lean_object* v___x_6581_; uint8_t v___x_6582_; 
v___x_6580_ = l_Lean_Syntax_getArg(v___x_6576_, v___x_6504_);
lean_dec(v___x_6576_);
v___x_6581_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6580_);
v___x_6582_ = l_Lean_Syntax_isOfKind(v___x_6580_, v___x_6581_);
if (v___x_6582_ == 0)
{
lean_object* v___x_6583_; 
lean_dec(v___x_6580_);
lean_dec(v___x_6511_);
lean_dec(v___x_6505_);
lean_dec_ref(v_dec_6492_);
v___x_6583_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6583_;
}
else
{
lean_object* v_t_x3f_6584_; lean_object* v___x_6585_; 
v_t_x3f_6584_ = l_Lean_Syntax_getArg(v___x_6580_, v___x_6575_);
lean_dec(v___x_6580_);
v___x_6585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6585_, 0, v_t_x3f_6584_);
v_t_x3f_6550_ = v___x_6585_;
v___y_6551_ = v_a_6493_;
v___y_6552_ = v_a_6494_;
v___y_6553_ = v_a_6495_;
v___y_6554_ = v_a_6496_;
v___y_6555_ = v_a_6497_;
v___y_6556_ = v_a_6498_;
v___y_6557_ = v_a_6499_;
goto v___jp_6549_;
}
}
}
else
{
lean_object* v___x_6586_; 
lean_dec(v___x_6576_);
v___x_6586_ = lean_box(0);
v_t_x3f_6550_ = v___x_6586_;
v___y_6551_ = v_a_6493_;
v___y_6552_ = v_a_6494_;
v___y_6553_ = v_a_6495_;
v___y_6554_ = v_a_6496_;
v___y_6555_ = v_a_6497_;
v___y_6556_ = v_a_6498_;
v___y_6557_ = v_a_6499_;
goto v___jp_6549_;
}
v___jp_6512_:
{
lean_object* v___x_6522_; lean_object* v___x_6523_; 
v___x_6522_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6523_ = l_Lean_Core_mkFreshUserName(v___x_6522_, v___y_6520_, v___y_6521_);
if (lean_obj_tag(v___x_6523_) == 0)
{
lean_object* v_a_6524_; lean_object* v_ref_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; uint8_t v_kind_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; lean_object* v___x_6539_; lean_object* v___x_6540_; 
v_a_6524_ = lean_ctor_get(v___x_6523_, 0);
lean_inc(v_a_6524_);
lean_dec_ref_known(v___x_6523_, 1);
v_ref_6525_ = lean_ctor_get(v___y_6520_, 2);
v___x_6526_ = l_Lean_mkIdentFrom(v___x_6511_, v_a_6524_, v___x_6507_);
v___x_6527_ = l_Lean_SourceInfo_fromRef(v_ref_6525_, v___x_6507_);
v___x_6528_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6529_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
v___x_6530_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6531_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_6527_, 3);
v___x_6532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6532_, 0, v___x_6527_);
lean_ctor_set(v___x_6532_, 1, v___x_6530_);
lean_ctor_set(v___x_6532_, 2, v___x_6531_);
v___x_6533_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6534_, 0, v___x_6527_);
lean_ctor_set(v___x_6534_, 1, v___x_6533_);
lean_inc(v___x_6526_);
lean_inc_ref(v___x_6532_);
v___x_6535_ = l_Lean_Syntax_node5(v___x_6527_, v___x_6529_, v___x_6511_, v___x_6532_, v___x_6532_, v___x_6534_, v___x_6526_);
v_kind_6536_ = lean_ctor_get_uint8(v_dec_6492_, sizeof(void*)*3);
v___x_6537_ = l_Lean_Syntax_node1(v___x_6527_, v___x_6528_, v___x_6535_);
v___x_6538_ = lean_box(v___x_6502_);
v___x_6539_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6539_, 0, v___x_6537_);
lean_closure_set(v___x_6539_, 1, v_dec_6492_);
lean_closure_set(v___x_6539_, 2, v___x_6538_);
v___x_6540_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6526_, v___y_6513_, v___y_6514_, v___x_6539_, v_kind_6536_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_);
return v___x_6540_;
}
else
{
lean_object* v_a_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6548_; 
lean_dec(v___y_6514_);
lean_dec(v___y_6513_);
lean_dec(v___x_6511_);
lean_dec_ref(v_dec_6492_);
v_a_6541_ = lean_ctor_get(v___x_6523_, 0);
v_isSharedCheck_6548_ = !lean_is_exclusive(v___x_6523_);
if (v_isSharedCheck_6548_ == 0)
{
v___x_6543_ = v___x_6523_;
v_isShared_6544_ = v_isSharedCheck_6548_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_a_6541_);
lean_dec(v___x_6523_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6548_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
lean_object* v___x_6546_; 
if (v_isShared_6544_ == 0)
{
v___x_6546_ = v___x_6543_;
goto v_reusejp_6545_;
}
else
{
lean_object* v_reuseFailAlloc_6547_; 
v_reuseFailAlloc_6547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6547_, 0, v_a_6541_);
v___x_6546_ = v_reuseFailAlloc_6547_;
goto v_reusejp_6545_;
}
v_reusejp_6545_:
{
return v___x_6546_;
}
}
}
}
v___jp_6549_:
{
lean_object* v___x_6558_; lean_object* v_rhs_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; uint8_t v___x_6562_; 
v___x_6558_ = lean_unsigned_to_nat(3u);
v_rhs_6559_ = l_Lean_Syntax_getArg(v___x_6505_, v___x_6558_);
v___x_6560_ = lean_unsigned_to_nat(4u);
v___x_6561_ = l_Lean_Syntax_getArg(v___x_6505_, v___x_6560_);
lean_dec(v___x_6505_);
v___x_6562_ = l_Lean_Syntax_isNone(v___x_6561_);
if (v___x_6562_ == 0)
{
uint8_t v___x_6563_; 
lean_dec(v_rhs_6559_);
lean_dec(v_t_x3f_6550_);
lean_dec(v___x_6511_);
lean_dec_ref(v_dec_6492_);
v___x_6563_ = l_Lean_Syntax_matchesNull(v___x_6561_, v___x_6558_);
if (v___x_6563_ == 0)
{
lean_object* v___x_6564_; 
v___x_6564_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6564_;
}
else
{
lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v_a_6567_; lean_object* v___x_6569_; uint8_t v_isShared_6570_; uint8_t v_isSharedCheck_6574_; 
v___x_6565_ = lean_obj_once(&l_Lean_Elab_Do_elabDoReassignArrow___closed__3, &l_Lean_Elab_Do_elabDoReassignArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3);
v___x_6566_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v___x_6565_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_);
v_a_6567_ = lean_ctor_get(v___x_6566_, 0);
v_isSharedCheck_6574_ = !lean_is_exclusive(v___x_6566_);
if (v_isSharedCheck_6574_ == 0)
{
v___x_6569_ = v___x_6566_;
v_isShared_6570_ = v_isSharedCheck_6574_;
goto v_resetjp_6568_;
}
else
{
lean_inc(v_a_6567_);
lean_dec(v___x_6566_);
v___x_6569_ = lean_box(0);
v_isShared_6570_ = v_isSharedCheck_6574_;
goto v_resetjp_6568_;
}
v_resetjp_6568_:
{
lean_object* v___x_6572_; 
if (v_isShared_6570_ == 0)
{
v___x_6572_ = v___x_6569_;
goto v_reusejp_6571_;
}
else
{
lean_object* v_reuseFailAlloc_6573_; 
v_reuseFailAlloc_6573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6573_, 0, v_a_6567_);
v___x_6572_ = v_reuseFailAlloc_6573_;
goto v_reusejp_6571_;
}
v_reusejp_6571_:
{
return v___x_6572_;
}
}
}
}
else
{
lean_dec(v___x_6561_);
v___y_6513_ = v_t_x3f_6550_;
v___y_6514_ = v_rhs_6559_;
v___y_6515_ = v___y_6551_;
v___y_6516_ = v___y_6552_;
v___y_6517_ = v___y_6553_;
v___y_6518_ = v___y_6554_;
v___y_6519_ = v___y_6555_;
v___y_6520_ = v___y_6556_;
v___y_6521_ = v___y_6557_;
goto v___jp_6512_;
}
}
}
}
else
{
lean_object* v_x_6587_; lean_object* v___y_6589_; lean_object* v_t_6590_; lean_object* v___y_6591_; lean_object* v___y_6592_; lean_object* v___y_6593_; lean_object* v___y_6594_; lean_object* v___y_6595_; lean_object* v___y_6596_; lean_object* v___y_6597_; lean_object* v_t_x3f_6630_; lean_object* v___y_6631_; lean_object* v___y_6632_; lean_object* v___y_6633_; lean_object* v___y_6634_; lean_object* v___y_6635_; lean_object* v___y_6636_; lean_object* v___y_6637_; lean_object* v___x_6672_; uint8_t v___x_6673_; 
v_x_6587_ = l_Lean_Syntax_getArg(v___x_6505_, v___x_6504_);
v___x_6672_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_6587_);
v___x_6673_ = l_Lean_Syntax_isOfKind(v_x_6587_, v___x_6672_);
if (v___x_6673_ == 0)
{
lean_object* v___x_6674_; 
lean_dec(v_x_6587_);
lean_dec(v___x_6505_);
lean_dec_ref(v_dec_6492_);
v___x_6674_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6674_;
}
else
{
lean_object* v___x_6675_; lean_object* v___x_6676_; uint8_t v___x_6677_; 
v___x_6675_ = lean_unsigned_to_nat(1u);
v___x_6676_ = l_Lean_Syntax_getArg(v___x_6505_, v___x_6675_);
v___x_6677_ = l_Lean_Syntax_isNone(v___x_6676_);
if (v___x_6677_ == 0)
{
uint8_t v___x_6678_; 
lean_inc(v___x_6676_);
v___x_6678_ = l_Lean_Syntax_matchesNull(v___x_6676_, v___x_6675_);
if (v___x_6678_ == 0)
{
lean_object* v___x_6679_; 
lean_dec(v___x_6676_);
lean_dec(v_x_6587_);
lean_dec(v___x_6505_);
lean_dec_ref(v_dec_6492_);
v___x_6679_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6679_;
}
else
{
lean_object* v___x_6680_; lean_object* v___x_6681_; uint8_t v___x_6682_; 
v___x_6680_ = l_Lean_Syntax_getArg(v___x_6676_, v___x_6504_);
lean_dec(v___x_6676_);
v___x_6681_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6680_);
v___x_6682_ = l_Lean_Syntax_isOfKind(v___x_6680_, v___x_6681_);
if (v___x_6682_ == 0)
{
lean_object* v___x_6683_; 
lean_dec(v___x_6680_);
lean_dec(v_x_6587_);
lean_dec(v___x_6505_);
lean_dec_ref(v_dec_6492_);
v___x_6683_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6683_;
}
else
{
lean_object* v_t_x3f_6684_; lean_object* v___x_6685_; 
v_t_x3f_6684_ = l_Lean_Syntax_getArg(v___x_6680_, v___x_6675_);
lean_dec(v___x_6680_);
v___x_6685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6685_, 0, v_t_x3f_6684_);
v_t_x3f_6630_ = v___x_6685_;
v___y_6631_ = v_a_6493_;
v___y_6632_ = v_a_6494_;
v___y_6633_ = v_a_6495_;
v___y_6634_ = v_a_6496_;
v___y_6635_ = v_a_6497_;
v___y_6636_ = v_a_6498_;
v___y_6637_ = v_a_6499_;
goto v___jp_6629_;
}
}
}
else
{
lean_object* v___x_6686_; 
lean_dec(v___x_6676_);
v___x_6686_ = lean_box(0);
v_t_x3f_6630_ = v___x_6686_;
v___y_6631_ = v_a_6493_;
v___y_6632_ = v_a_6494_;
v___y_6633_ = v_a_6495_;
v___y_6634_ = v_a_6496_;
v___y_6635_ = v_a_6497_;
v___y_6636_ = v_a_6498_;
v___y_6637_ = v_a_6499_;
goto v___jp_6629_;
}
}
v___jp_6588_:
{
lean_object* v___x_6598_; lean_object* v___x_6599_; 
v___x_6598_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6599_ = l_Lean_Core_mkFreshUserName(v___x_6598_, v___y_6596_, v___y_6597_);
if (lean_obj_tag(v___x_6599_) == 0)
{
lean_object* v_a_6600_; lean_object* v_ref_6601_; uint8_t v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; uint8_t v_kind_6615_; lean_object* v___x_6616_; lean_object* v___x_6617_; lean_object* v___x_6618_; lean_object* v___x_6619_; lean_object* v___x_6620_; 
v_a_6600_ = lean_ctor_get(v___x_6599_, 0);
lean_inc(v_a_6600_);
lean_dec_ref_known(v___x_6599_, 1);
v_ref_6601_ = lean_ctor_get(v___y_6596_, 2);
v___x_6602_ = 0;
v___x_6603_ = l_Lean_mkIdentFrom(v_x_6587_, v_a_6600_, v___x_6602_);
v___x_6604_ = l_Lean_SourceInfo_fromRef(v_ref_6601_, v___x_6602_);
v___x_6605_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6606_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_6607_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v___x_6604_, 4);
v___x_6608_ = l_Lean_Syntax_node1(v___x_6604_, v___x_6607_, v_x_6587_);
v___x_6609_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6610_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_6611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6611_, 0, v___x_6604_);
lean_ctor_set(v___x_6611_, 1, v___x_6609_);
lean_ctor_set(v___x_6611_, 2, v___x_6610_);
v___x_6612_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6613_, 0, v___x_6604_);
lean_ctor_set(v___x_6613_, 1, v___x_6612_);
lean_inc(v___x_6603_);
lean_inc_ref(v___x_6611_);
v___x_6614_ = l_Lean_Syntax_node5(v___x_6604_, v___x_6606_, v___x_6608_, v___x_6611_, v___x_6611_, v___x_6613_, v___x_6603_);
v_kind_6615_ = lean_ctor_get_uint8(v_dec_6492_, sizeof(void*)*3);
v___x_6616_ = l_Lean_Syntax_node1(v___x_6604_, v___x_6605_, v___x_6614_);
v___x_6617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6617_, 0, v_t_6590_);
v___x_6618_ = lean_box(v___x_6502_);
v___x_6619_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6619_, 0, v___x_6616_);
lean_closure_set(v___x_6619_, 1, v_dec_6492_);
lean_closure_set(v___x_6619_, 2, v___x_6618_);
v___x_6620_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6603_, v___x_6617_, v___y_6589_, v___x_6619_, v_kind_6615_, v___y_6591_, v___y_6592_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_);
return v___x_6620_;
}
else
{
lean_object* v_a_6621_; lean_object* v___x_6623_; uint8_t v_isShared_6624_; uint8_t v_isSharedCheck_6628_; 
lean_dec(v_t_6590_);
lean_dec(v___y_6589_);
lean_dec(v_x_6587_);
lean_dec_ref(v_dec_6492_);
v_a_6621_ = lean_ctor_get(v___x_6599_, 0);
v_isSharedCheck_6628_ = !lean_is_exclusive(v___x_6599_);
if (v_isSharedCheck_6628_ == 0)
{
v___x_6623_ = v___x_6599_;
v_isShared_6624_ = v_isSharedCheck_6628_;
goto v_resetjp_6622_;
}
else
{
lean_inc(v_a_6621_);
lean_dec(v___x_6599_);
v___x_6623_ = lean_box(0);
v_isShared_6624_ = v_isSharedCheck_6628_;
goto v_resetjp_6622_;
}
v_resetjp_6622_:
{
lean_object* v___x_6626_; 
if (v_isShared_6624_ == 0)
{
v___x_6626_ = v___x_6623_;
goto v_reusejp_6625_;
}
else
{
lean_object* v_reuseFailAlloc_6627_; 
v_reuseFailAlloc_6627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6627_, 0, v_a_6621_);
v___x_6626_ = v_reuseFailAlloc_6627_;
goto v_reusejp_6625_;
}
v_reusejp_6625_:
{
return v___x_6626_;
}
}
}
}
v___jp_6629_:
{
lean_object* v___x_6638_; lean_object* v_rhs_6639_; lean_object* v___x_6640_; 
v___x_6638_ = lean_unsigned_to_nat(3u);
v_rhs_6639_ = l_Lean_Syntax_getArg(v___x_6505_, v___x_6638_);
lean_dec(v___x_6505_);
v___x_6640_ = l_Lean_Elab_Do_throwUnlessMutVarDeclared(v_x_6587_, v___y_6631_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
if (lean_obj_tag(v___x_6640_) == 0)
{
lean_dec_ref_known(v___x_6640_, 1);
if (lean_obj_tag(v_t_x3f_6630_) == 0)
{
lean_object* v___x_6641_; lean_object* v___x_6642_; 
v___x_6641_ = l_Lean_TSyntax_getId(v_x_6587_);
v___x_6642_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_6641_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
if (lean_obj_tag(v___x_6642_) == 0)
{
lean_object* v_a_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; 
v_a_6643_ = lean_ctor_get(v___x_6642_, 0);
lean_inc(v_a_6643_);
lean_dec_ref_known(v___x_6642_, 1);
v___x_6644_ = l_Lean_LocalDecl_type(v_a_6643_);
lean_dec(v_a_6643_);
v___x_6645_ = l_Lean_Elab_Term_exprToSyntax(v___x_6644_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
if (lean_obj_tag(v___x_6645_) == 0)
{
lean_object* v_a_6646_; 
v_a_6646_ = lean_ctor_get(v___x_6645_, 0);
lean_inc(v_a_6646_);
lean_dec_ref_known(v___x_6645_, 1);
v___y_6589_ = v_rhs_6639_;
v_t_6590_ = v_a_6646_;
v___y_6591_ = v___y_6631_;
v___y_6592_ = v___y_6632_;
v___y_6593_ = v___y_6633_;
v___y_6594_ = v___y_6634_;
v___y_6595_ = v___y_6635_;
v___y_6596_ = v___y_6636_;
v___y_6597_ = v___y_6637_;
goto v___jp_6588_;
}
else
{
lean_object* v_a_6647_; lean_object* v___x_6649_; uint8_t v_isShared_6650_; uint8_t v_isSharedCheck_6654_; 
lean_dec(v_rhs_6639_);
lean_dec(v_x_6587_);
lean_dec_ref(v_dec_6492_);
v_a_6647_ = lean_ctor_get(v___x_6645_, 0);
v_isSharedCheck_6654_ = !lean_is_exclusive(v___x_6645_);
if (v_isSharedCheck_6654_ == 0)
{
v___x_6649_ = v___x_6645_;
v_isShared_6650_ = v_isSharedCheck_6654_;
goto v_resetjp_6648_;
}
else
{
lean_inc(v_a_6647_);
lean_dec(v___x_6645_);
v___x_6649_ = lean_box(0);
v_isShared_6650_ = v_isSharedCheck_6654_;
goto v_resetjp_6648_;
}
v_resetjp_6648_:
{
lean_object* v___x_6652_; 
if (v_isShared_6650_ == 0)
{
v___x_6652_ = v___x_6649_;
goto v_reusejp_6651_;
}
else
{
lean_object* v_reuseFailAlloc_6653_; 
v_reuseFailAlloc_6653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6653_, 0, v_a_6647_);
v___x_6652_ = v_reuseFailAlloc_6653_;
goto v_reusejp_6651_;
}
v_reusejp_6651_:
{
return v___x_6652_;
}
}
}
}
else
{
lean_object* v_a_6655_; lean_object* v___x_6657_; uint8_t v_isShared_6658_; uint8_t v_isSharedCheck_6662_; 
lean_dec(v_rhs_6639_);
lean_dec(v_x_6587_);
lean_dec_ref(v_dec_6492_);
v_a_6655_ = lean_ctor_get(v___x_6642_, 0);
v_isSharedCheck_6662_ = !lean_is_exclusive(v___x_6642_);
if (v_isSharedCheck_6662_ == 0)
{
v___x_6657_ = v___x_6642_;
v_isShared_6658_ = v_isSharedCheck_6662_;
goto v_resetjp_6656_;
}
else
{
lean_inc(v_a_6655_);
lean_dec(v___x_6642_);
v___x_6657_ = lean_box(0);
v_isShared_6658_ = v_isSharedCheck_6662_;
goto v_resetjp_6656_;
}
v_resetjp_6656_:
{
lean_object* v___x_6660_; 
if (v_isShared_6658_ == 0)
{
v___x_6660_ = v___x_6657_;
goto v_reusejp_6659_;
}
else
{
lean_object* v_reuseFailAlloc_6661_; 
v_reuseFailAlloc_6661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6661_, 0, v_a_6655_);
v___x_6660_ = v_reuseFailAlloc_6661_;
goto v_reusejp_6659_;
}
v_reusejp_6659_:
{
return v___x_6660_;
}
}
}
}
else
{
lean_object* v_val_6663_; 
v_val_6663_ = lean_ctor_get(v_t_x3f_6630_, 0);
lean_inc(v_val_6663_);
lean_dec_ref_known(v_t_x3f_6630_, 1);
v___y_6589_ = v_rhs_6639_;
v_t_6590_ = v_val_6663_;
v___y_6591_ = v___y_6631_;
v___y_6592_ = v___y_6632_;
v___y_6593_ = v___y_6633_;
v___y_6594_ = v___y_6634_;
v___y_6595_ = v___y_6635_;
v___y_6596_ = v___y_6636_;
v___y_6597_ = v___y_6637_;
goto v___jp_6588_;
}
}
else
{
lean_object* v_a_6664_; lean_object* v___x_6666_; uint8_t v_isShared_6667_; uint8_t v_isSharedCheck_6671_; 
lean_dec(v_rhs_6639_);
lean_dec(v_t_x3f_6630_);
lean_dec(v_x_6587_);
lean_dec_ref(v_dec_6492_);
v_a_6664_ = lean_ctor_get(v___x_6640_, 0);
v_isSharedCheck_6671_ = !lean_is_exclusive(v___x_6640_);
if (v_isSharedCheck_6671_ == 0)
{
v___x_6666_ = v___x_6640_;
v_isShared_6667_ = v_isSharedCheck_6671_;
goto v_resetjp_6665_;
}
else
{
lean_inc(v_a_6664_);
lean_dec(v___x_6640_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_6687_, lean_object* v_dec_6688_, lean_object* v_a_6689_, lean_object* v_a_6690_, lean_object* v_a_6691_, lean_object* v_a_6692_, lean_object* v_a_6693_, lean_object* v_a_6694_, lean_object* v_a_6695_, lean_object* v_a_6696_){
_start:
{
lean_object* v_res_6697_; 
v_res_6697_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_6687_, v_dec_6688_, v_a_6689_, v_a_6690_, v_a_6691_, v_a_6692_, v_a_6693_, v_a_6694_, v_a_6695_);
lean_dec(v_a_6695_);
lean_dec_ref(v_a_6694_);
lean_dec(v_a_6693_);
lean_dec_ref(v_a_6692_);
lean_dec(v_a_6691_);
lean_dec_ref(v_a_6690_);
lean_dec_ref(v_a_6689_);
return v_res_6697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_6705_; lean_object* v___x_6706_; lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; 
v___x_6705_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6706_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_6707_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_6708_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_6709_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6705_, v___x_6706_, v___x_6707_, v___x_6708_);
return v___x_6709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_6710_){
_start:
{
lean_object* v_res_6711_; 
v_res_6711_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_6711_;
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
