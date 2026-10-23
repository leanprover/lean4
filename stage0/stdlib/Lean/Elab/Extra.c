// Lean compiler output
// Module: Lean.Elab.Extra
// Imports: public import Lean.Elab.App public import Lean.Elab.BuiltinNotation
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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFunUnit___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withTermInfoContext_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Term_mkCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedDefaultInstances_default;
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_Meta_defaultInstanceExtension;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
uint8_t l_Lean_Elab_Term_hasCDot(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "invalid 'for_in%' notation, expected type is not available"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__1;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 66, .m_data = "invalid 'for_in%' notation, expected type is not of the form `M α`"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "failed to synthesize instance for 'for_in%' notation"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__2 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "forInMacro"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__3 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__3_value),LEAN_SCALAR_PTR_LITERAL(235, 146, 198, 65, 99, 218, 100, 233)}};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__4 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__4_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ForIn"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__5 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__5_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "forIn"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__6 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__6_value),LEAN_SCALAR_PTR_LITERAL(9, 12, 142, 239, 44, 138, 10, 93)}};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__7 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__7_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__8 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__8_value),LEAN_SCALAR_PTR_LITERAL(165, 239, 73, 172, 230, 126, 139, 134)}};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__9 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__9_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__10 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__10_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__11 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__11_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "self"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__12 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__12_value),LEAN_SCALAR_PTR_LITERAL(120, 226, 111, 209, 39, 160, 197, 219)}};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__13 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__14 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__14_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "failed to construct 'ForIn' instance for collection"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__15 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Term_elabForIn___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_elabForIn___closed__16;
static const lean_string_object l_Lean_Elab_Term_elabForIn___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nand monad"};
static const lean_object* l_Lean_Elab_Term_elabForIn___closed__17 = (const lean_object*)&l_Lean_Elab_Term_elabForIn___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Term_elabForIn___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_elabForIn___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabForIn"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(227, 34, 236, 223, 176, 152, 238, 124)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__0_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__3_value),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__4_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_elabForIn_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "forInMacro'"};
static const lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn_x27___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_elabForIn_x27___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_elabForIn_x27___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_elabForIn_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 76, 157, 146, 186, 53, 21, 82)}};
static const lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ForIn'"};
static const lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__2 = (const lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forIn'"};
static const lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__3 = (const lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn_x27___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_ctor_object l_Lean_Elab_Term_elabForIn_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__3_value),LEAN_SCALAR_PTR_LITERAL(10, 254, 232, 131, 195, 189, 138, 93)}};
static const lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__4 = (const lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__4_value;
static const lean_string_object l_Lean_Elab_Term_elabForIn_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "failed to construct `ForIn'` instance for collection"};
static const lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__5 = (const lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Term_elabForIn_x27___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__6;
static const lean_string_object l_Lean_Elab_Term_elabForIn_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Membership"};
static const lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__7 = (const lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__7_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__8 = (const lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Term_elabForIn_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_object* l_Lean_Elab_Term_elabForIn_x27___closed__9 = (const lean_object*)&l_Lean_Elab_Term_elabForIn_x27___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabForIn'"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 231, 47, 50, 253, 196, 183, 104)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__0_value),((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__3_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__4_value),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_term_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_term_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_binop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_binop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_unop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_unop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_macroExpansion_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_macroExpansion_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "binop"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 253, 231, 222, 243, 42, 73, 191)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binop_lazy"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 222, 106, 2, 24, 145, 254, 163)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unop"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(68, 253, 109, 39, 185, 175, 169, 133)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "leftact"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(235, 190, 22, 58, 115, 190, 112, 107)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rightact"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__8_value),LEAN_SCALAR_PTR_LITERAL(147, 6, 66, 125, 81, 188, 156, 70)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__10 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__12 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__14 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__15 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "CoeT"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 0, 82, 253, 29, 221, 45, 84)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 183, 237, 4, 181, 75, 109, 5)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "uncomparable types: "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "added coercion: "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "visiting "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "result: "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", maxType: "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "hasUncomparable: "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__7 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", hasUnknown: "};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__9 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Op"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabBinOp"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 133, 134, 85, 150, 239, 79, 84)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(254, 97, 163, 42, 200, 140, 10, 73)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(475) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(475) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__0_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__1_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(475) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(475) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__3_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__4_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabBinOpLazy"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 133, 134, 85, 150, 239, 79, 84)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 108, 46, 201, 207, 65, 172, 53)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(476) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(476) << 1) | 1)),((lean_object*)(((size_t)(70) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__0_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__1_value),((lean_object*)(((size_t)(70) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(476) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(476) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__3_value),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__4_value),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabLeftact"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 133, 134, 85, 150, 239, 79, 84)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 112, 240, 137, 172, 217, 159, 78)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(477) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(477) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__0_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__1_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(477) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(477) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__3_value),((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__4_value),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabRightact"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 133, 134, 85, 150, 239, 79, 84)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 136, 170, 17, 87, 119, 44, 244)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(478) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(478) << 1) | 1)),((lean_object*)(((size_t)(67) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__0_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__1_value),((lean_object*)(((size_t)(67) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(478) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(478) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__3_value),((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__4_value),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabUnOp"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 133, 134, 85, 150, 239, 79, 84)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 173, 236, 6, 246, 162, 121, 135)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(479) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(479) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__0_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__1_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(479) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(479) << 1) | 1)),((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__3_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__4_value),((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binrel"};
static const lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 199, 148, 20, 207, 217, 213, 245)}};
static const lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 238, 75, 93, 70, 164, 233, 165)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabBinRel"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 133, 134, 85, 150, 239, 79, 84)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 176, 232, 149, 170, 221, 241, 244)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(561) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(561) << 1) | 1)),((lean_object*)(((size_t)(77) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__0_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__1_value),((lean_object*)(((size_t)(77) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(561) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(561) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__3_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__4_value),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "binrel_no_prop"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 122, 90, 92, 171, 187, 176, 37)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabBinRelNoProp"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 133, 134, 85, 150, 239, 79, 84)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(55, 6, 28, 236, 66, 74, 216, 19)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(563) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(563) << 1) | 1)),((lean_object*)(((size_t)(90) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__0_value),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__1_value),((lean_object*)(((size_t)(90) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(563) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(563) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__3_value),((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "invalid 'default_or_ofNonempty%', expected type is not known"};
static const lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1;
static const lean_string_object l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "failed to synthesize '"};
static const lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3;
static const lean_string_object l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__4 = (const lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__4_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__5 = (const lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__5_value;
static const lean_string_object l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "' or '"};
static const lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__6 = (const lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7;
static const lean_string_object l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__8 = (const lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__8_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__9 = (const lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__9_value;
static const lean_string_object l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "' instance for"};
static const lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__10 = (const lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11;
static const lean_string_object l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 127, .m_capacity = 127, .m_length = 126, .m_data = "\n\nIf this type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it."};
static const lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__12 = (const lean_object*)&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "defaultOrOfNonempty"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 19, 142, 204, 140, 85, 7, 204)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabDefaultOrNonempty"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 133, 134, 85, 150, 239, 79, 84)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 13, 100, 67, 210, 117, 66, 19)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(566) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(581) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(566) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(566) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__4_value),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__0_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__0_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__0_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__1_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__0_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__1_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__1_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__2_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__1_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__2_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__2_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__3_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__2_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__3_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__3_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__4_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Extra"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__4_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__4_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__5_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__3_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__4_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(3, 15, 182, 26, 247, 33, 203, 42)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__5_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__5_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__6_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__5_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(78, 187, 205, 52, 206, 14, 129, 139)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__6_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__6_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__7_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__6_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 94, 85, 34, 130, 97, 241, 93)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__7_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__7_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__8_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__7_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 42, 79, 210, 151, 194, 102, 238)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__8_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__8_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__9_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__8_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 95, 84, 54, 245, 86, 126, 132)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__9_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__9_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__10_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__9_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 233, 238, 46, 119, 252, 7, 141)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__10_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__10_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__11_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__11_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__11_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__12_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__10_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__11_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 197, 135, 204, 22, 23, 200, 247)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__12_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__12_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__13_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__13_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__13_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__14_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__12_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__13_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 92, 31, 51, 153, 79, 6, 21)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__14_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__14_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__15_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__14_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 205, 169, 233, 33, 60, 131, 204)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__15_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__15_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__16_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__15_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 175, 208, 212, 31, 237, 230, 118)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__16_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__16_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__17_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__16_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__4_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(199, 111, 29, 176, 220, 248, 251, 189)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__17_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__17_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__19_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__19_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__19_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__21_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__21_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__21_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_box(1);
v___x_2_ = l_Lean_MessageData_ofFormat(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__2));
v___x_7_ = l_Lean_MessageData_ofFormat(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3(lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
return v_x_8_;
}
else
{
lean_object* v_head_10_; lean_object* v_tail_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_33_; 
v_head_10_ = lean_ctor_get(v_x_9_, 0);
v_tail_11_ = lean_ctor_get(v_x_9_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_x_9_);
if (v_isSharedCheck_33_ == 0)
{
v___x_13_ = v_x_9_;
v_isShared_14_ = v_isSharedCheck_33_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_tail_11_);
lean_inc(v_head_10_);
lean_dec(v_x_9_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_33_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v_before_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_31_; 
v_before_15_ = lean_ctor_get(v_head_10_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v_head_10_);
if (v_isSharedCheck_31_ == 0)
{
lean_object* v_unused_32_; 
v_unused_32_ = lean_ctor_get(v_head_10_, 1);
lean_dec(v_unused_32_);
v___x_17_ = v_head_10_;
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_before_15_);
lean_dec(v_head_10_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_19_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_18_ == 0)
{
lean_ctor_set_tag(v___x_17_, 7);
lean_ctor_set(v___x_17_, 1, v___x_19_);
lean_ctor_set(v___x_17_, 0, v_x_8_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_x_8_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v___x_19_);
v___x_21_ = v_reuseFailAlloc_30_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_14_ == 0)
{
lean_ctor_set_tag(v___x_13_, 7);
lean_ctor_set(v___x_13_, 1, v___x_22_);
lean_ctor_set(v___x_13_, 0, v___x_21_);
v___x_24_ = v___x_13_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_21_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v___x_22_);
v___x_24_ = v_reuseFailAlloc_29_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = l_Lean_MessageData_ofSyntax(v_before_15_);
v___x_26_ = l_Lean_indentD(v___x_25_);
v___x_27_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_24_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v_x_8_ = v___x_27_;
v_x_9_ = v_tail_11_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__2(lean_object* v_opts_34_, lean_object* v_opt_35_){
_start:
{
lean_object* v_name_36_; lean_object* v_defValue_37_; lean_object* v_map_38_; lean_object* v___x_39_; 
v_name_36_ = lean_ctor_get(v_opt_35_, 0);
v_defValue_37_ = lean_ctor_get(v_opt_35_, 1);
v_map_38_ = lean_ctor_get(v_opts_34_, 0);
v___x_39_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_38_, v_name_36_);
if (lean_obj_tag(v___x_39_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = lean_unbox(v_defValue_37_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; 
v_val_41_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v___x_39_, 1);
if (lean_obj_tag(v_val_41_) == 1)
{
uint8_t v_v_42_; 
v_v_42_ = lean_ctor_get_uint8(v_val_41_, 0);
lean_dec_ref_known(v_val_41_, 0);
return v_v_42_;
}
else
{
uint8_t v___x_43_; 
lean_dec(v_val_41_);
v___x_43_ = lean_unbox(v_defValue_37_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_44_, lean_object* v_opt_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__2(v_opts_44_, v_opt_45_);
lean_dec_ref(v_opt_45_);
lean_dec_ref(v_opts_44_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__1));
v___x_52_ = l_Lean_MessageData_ofFormat(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg(lean_object* v_msgData_53_, lean_object* v_macroStack_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_57_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_55_);
v___x_58_ = l_Lean_Elab_pp_macroStack;
v___x_59_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__2(v___x_57_, v___x_58_);
lean_dec_ref(v___x_57_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec(v_macroStack_54_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v_msgData_53_);
return v___x_60_;
}
else
{
if (lean_obj_tag(v_macroStack_54_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_msgData_53_);
return v___x_61_;
}
else
{
lean_object* v_head_62_; lean_object* v_after_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_78_; 
v_head_62_ = lean_ctor_get(v_macroStack_54_, 0);
lean_inc(v_head_62_);
v_after_63_ = lean_ctor_get(v_head_62_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_head_62_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v_head_62_, 0);
lean_dec(v_unused_79_);
v___x_65_ = v_head_62_;
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_after_63_);
lean_dec(v_head_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 7);
lean_ctor_set(v___x_65_, 1, v___x_67_);
lean_ctor_set(v___x_65_, 0, v_msgData_53_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_msgData_53_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_77_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_msgData_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_70_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___closed__2);
v___x_71_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = l_Lean_MessageData_ofSyntax(v_after_63_);
v___x_73_ = l_Lean_indentD(v___x_72_);
v_msgData_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_74_, 0, v___x_71_);
lean_ctor_set(v_msgData_74_, 1, v___x_73_);
v___x_75_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1_spec__3(v_msgData_74_, v_macroStack_54_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_80_, lean_object* v_macroStack_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg(v_msgData_80_, v_macroStack_81_, v___y_82_);
lean_dec_ref(v___y_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_env_92_; uint8_t v___x_93_; lean_object* v_env_94_; lean_object* v___x_95_; lean_object* v_toCold_96_; lean_object* v_mctx_97_; lean_object* v_lctx_98_; lean_object* v_options_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = 0;
v_env_94_ = l_Lean_Environment_setRecordingDeps(v_env_92_, v___x_93_);
v___x_95_ = lean_st_ref_get(v___y_87_);
v_toCold_96_ = lean_ctor_get(v___y_88_, 0);
v_mctx_97_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_mctx_97_);
lean_dec(v___x_95_);
v_lctx_98_ = lean_ctor_get(v___y_86_, 2);
v_options_99_ = lean_ctor_get(v_toCold_96_, 2);
lean_inc_ref(v_options_99_);
lean_inc_ref(v_lctx_98_);
v___x_100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_100_, 0, v_env_94_);
lean_ctor_set(v___x_100_, 1, v_mctx_97_);
lean_ctor_set(v___x_100_, 2, v_lctx_98_);
lean_ctor_set(v___x_100_, 3, v_options_99_);
v___x_101_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_msgData_85_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0___boxed(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msgData_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_ref_118_; lean_object* v_macroStack_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_a_122_; lean_object* v___x_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_132_; 
v_ref_118_ = lean_ctor_get(v___y_115_, 2);
v_macroStack_119_ = lean_ctor_get(v___y_111_, 1);
v___x_120_ = l_Lean_Elab_getBetterRef(v_ref_118_, v_macroStack_119_);
v___x_121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_110_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref(v___x_121_);
lean_inc(v_macroStack_119_);
v___x_123_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg(v_a_122_, v_macroStack_119_, v___y_115_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_132_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_120_);
lean_ctor_set(v___x_128_, 1, v_a_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 1);
lean_ctor_set(v___x_126_, 0, v___x_128_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg___boxed(lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v_msg_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_141_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__1(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__0));
v___x_144_ = l_Lean_stringToMessageData(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__3(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__2));
v___x_147_ = l_Lean_stringToMessageData(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn(lean_object* v_expectedType_x3f_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
if (lean_obj_tag(v_expectedType_x3f_148_) == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__1);
v___x_157_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_156_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
return v___x_157_;
}
else
{
lean_object* v_val_158_; lean_object* v___x_159_; 
v_val_158_ = lean_ctor_get(v_expectedType_x3f_148_, 0);
lean_inc_n(v_val_158_, 2);
lean_dec_ref_known(v_expectedType_x3f_148_, 1);
v___x_159_ = l_Lean_Meta_isTypeApp_x3f(v_val_158_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_173_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_173_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_173_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_173_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
if (lean_obj_tag(v_a_160_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
lean_del_object(v___x_162_);
v___x_164_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___closed__3);
v___x_165_ = l_Lean_indentExpr(v_val_158_);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_166_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v_fst_169_; lean_object* v___x_171_; 
lean_dec(v_val_158_);
v_val_168_ = lean_ctor_get(v_a_160_, 0);
lean_inc(v_val_168_);
lean_dec_ref_known(v_a_160_, 1);
v_fst_169_ = lean_ctor_get(v_val_168_, 0);
lean_inc(v_fst_169_);
lean_dec(v_val_168_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v_fst_169_);
v___x_171_ = v___x_162_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_fst_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_val_158_);
v_a_174_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_159_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_159_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn___boxed(lean_object* v_expectedType_x3f_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn(v_expectedType_x3f_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0(lean_object* v_00_u03b1_191_, lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v_msg_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___boxed(lean_object* v_00_u03b1_201_, lean_object* v_msg_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0(v_00_u03b1_201_, v_msg_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1(lean_object* v_msgData_211_, lean_object* v_macroStack_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___redArg(v_msgData_211_, v_macroStack_212_, v___y_217_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1___boxed(lean_object* v_msgData_221_, lean_object* v_macroStack_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__1(v_msgData_221_, v_macroStack_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_230_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__1(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__0));
v___x_233_ = l_Lean_stringToMessageData(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure(lean_object* v_forInInstance_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___closed__1);
v___x_243_ = l_Lean_indentExpr(v_forInInstance_234_);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_244_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure___boxed(lean_object* v_forInInstance_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure(v_forInInstance_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_254_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_box(0);
v___x_256_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg(){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg___closed__0);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg___boxed(lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg();
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0(lean_object* v_00_u03b1_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg();
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___boxed(lean_object* v_00_u03b1_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0(v_00_u03b1_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForIn___closed__16(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__15));
v___x_308_ = l_Lean_stringToMessageData(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForIn___closed__18(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__17));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForIn(lean_object* v_stx_312_, lean_object* v_expectedType_x3f_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__4));
lean_inc(v_stx_312_);
v___x_322_ = l_Lean_Syntax_isOfKind(v_stx_312_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec(v_expectedType_x3f_313_);
lean_dec(v_stx_312_);
v___x_323_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg();
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = l_Lean_Syntax_getArg(v_stx_312_, v___x_325_);
v___x_327_ = lean_unsigned_to_nat(2u);
v___x_328_ = l_Lean_Syntax_getArg(v_stx_312_, v___x_327_);
v___x_329_ = lean_unsigned_to_nat(3u);
v___x_330_ = l_Lean_Syntax_getArg(v_stx_312_, v___x_329_);
lean_dec(v_stx_312_);
lean_inc(v_expectedType_x3f_313_);
v___x_331_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec_ref_known(v___x_331_, 1);
v___x_332_ = lean_box(0);
v___x_333_ = l_Lean_Elab_Term_elabTerm(v___x_326_, v___x_332_, v___x_322_, v___x_322_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_468_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_468_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_468_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_468_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; 
lean_inc(v_expectedType_x3f_313_);
v___x_338_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn(v_expectedType_x3f_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_467_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_467_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_467_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_467_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; 
lean_inc(v_a_319_);
lean_inc_ref(v_a_318_);
lean_inc(v_a_317_);
lean_inc_ref(v_a_316_);
lean_inc(v_a_334_);
v___x_343_ = lean_infer_type(v_a_334_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_466_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_466_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_466_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_466_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_mkFreshLevelMVar(v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = l_Lean_Level_succ___override(v_a_349_);
v___x_351_ = l_Lean_mkSort(v___x_350_);
if (v_isShared_347_ == 0)
{
lean_ctor_set_tag(v___x_346_, 1);
lean_ctor_set(v___x_346_, 0, v___x_351_);
v___x_353_ = v___x_346_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_457_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = 0;
v___x_355_ = lean_box(0);
v___x_356_ = l_Lean_Meta_mkFreshExprMVar(v___x_353_, v___x_354_, v___x_355_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_456_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_456_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_456_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_456_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_a_362_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_429_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__14));
v___x_430_ = lean_mk_empty_array_with_capacity(v___x_329_);
lean_inc(v_a_339_);
v___x_431_ = lean_array_push(v___x_430_, v_a_339_);
lean_inc(v_a_344_);
v___x_432_ = lean_array_push(v___x_431_, v_a_344_);
lean_inc(v_a_357_);
v___x_433_ = lean_array_push(v___x_432_, v_a_357_);
v___x_434_ = l_Lean_Meta_mkAppM(v___x_429_, v___x_433_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; 
lean_dec(v_a_344_);
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v_a_362_ = v_a_435_;
goto v___jp_361_;
}
else
{
lean_object* v_a_436_; uint8_t v___x_437_; 
lean_del_object(v___x_359_);
lean_dec(v_a_357_);
lean_del_object(v___x_341_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
v_a_436_ = lean_ctor_get(v___x_434_, 0);
v___x_437_ = l_Lean_Exception_isInterrupt(v_a_436_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
lean_inc(v_a_436_);
v___x_438_ = l_Lean_Exception_isRuntime(v_a_436_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_dec_ref_known(v___x_434_, 1);
v___x_439_ = l_Lean_Elab_Term_tryPostpone(v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec_ref_known(v___x_439_, 1);
v___x_440_ = lean_obj_once(&l_Lean_Elab_Term_elabForIn___closed__16, &l_Lean_Elab_Term_elabForIn___closed__16_once, _init_l_Lean_Elab_Term_elabForIn___closed__16);
v___x_441_ = l_Lean_indentExpr(v_a_344_);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_obj_once(&l_Lean_Elab_Term_elabForIn___closed__18, &l_Lean_Elab_Term_elabForIn___closed__18_once, _init_l_Lean_Elab_Term_elabForIn___closed__18);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_indentExpr(v_a_339_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_446_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_447_;
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_a_344_);
lean_dec(v_a_339_);
v_a_448_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_439_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_439_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_dec(v_a_344_);
lean_dec(v_a_339_);
return v___x_434_;
}
}
else
{
lean_dec(v_a_344_);
lean_dec(v_a_339_);
return v___x_434_;
}
}
v___jp_361_:
{
lean_object* v___x_363_; 
lean_inc_ref(v_a_362_);
v___x_363_ = l_Lean_Meta_trySynthInstance(v_a_362_, v___x_332_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
switch(lean_obj_tag(v_a_364_))
{
case 0:
{
lean_object* v___x_365_; 
lean_del_object(v___x_359_);
lean_dec(v_a_357_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
v___x_365_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure(v_a_362_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_365_;
}
case 1:
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v_a_362_);
v_a_366_ = lean_ctor_get(v_a_364_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v_a_364_);
if (v_isSharedCheck_410_ == 0)
{
v___x_368_ = v_a_364_;
v_isShared_369_ = v_isSharedCheck_410_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v_a_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_410_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__7));
v___x_371_ = lean_box(0);
v___x_372_ = l_Lean_Elab_Term_mkConst(v___x_370_, v___x_371_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_409_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_409_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_409_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_409_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_377_ = lean_box(0);
v___x_378_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__9));
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 1);
lean_ctor_set(v___x_375_, 0, v_a_339_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_339_);
v___x_380_ = v_reuseFailAlloc_408_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_381_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_381_, 0, v___x_377_);
lean_ctor_set(v___x_381_, 1, v___x_378_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
lean_ctor_set(v___x_381_, 3, v___x_324_);
v___x_382_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__11));
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v_a_357_);
v___x_384_ = v___x_368_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_357_);
v___x_384_ = v_reuseFailAlloc_407_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_385_, 0, v___x_377_);
lean_ctor_set(v___x_385_, 1, v___x_382_);
lean_ctor_set(v___x_385_, 2, v___x_384_);
lean_ctor_set(v___x_385_, 3, v___x_324_);
v___x_386_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__13));
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 1);
lean_ctor_set(v___x_359_, 0, v_a_366_);
v___x_388_ = v___x_359_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_366_);
v___x_388_ = v_reuseFailAlloc_406_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_389_, 0, v___x_377_);
lean_ctor_set(v___x_389_, 1, v___x_386_);
lean_ctor_set(v___x_389_, 2, v___x_388_);
lean_ctor_set(v___x_389_, 3, v___x_324_);
v___x_390_ = lean_mk_empty_array_with_capacity(v___x_329_);
lean_inc_ref(v___x_390_);
v___x_391_ = lean_array_push(v___x_390_, v___x_381_);
v___x_392_ = lean_array_push(v___x_391_, v___x_385_);
v___x_393_ = lean_array_push(v___x_392_, v___x_389_);
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 1);
lean_ctor_set(v___x_341_, 0, v_a_334_);
v___x_395_ = v___x_341_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_334_);
v___x_395_ = v_reuseFailAlloc_405_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_397_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_328_);
v___x_397_ = v___x_336_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_328_);
v___x_397_ = v_reuseFailAlloc_404_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_330_);
v___x_399_ = lean_array_push(v___x_390_, v___x_395_);
v___x_400_ = lean_array_push(v___x_399_, v___x_397_);
v___x_401_ = lean_array_push(v___x_400_, v___x_398_);
v___x_402_ = 0;
v___x_403_ = l_Lean_Elab_Term_elabAppArgs(v_a_373_, v___x_393_, v___x_401_, v_expectedType_x3f_313_, v___x_402_, v___x_402_, v___x_402_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_403_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_368_);
lean_dec(v_a_366_);
lean_del_object(v___x_359_);
lean_dec(v_a_357_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
return v___x_372_;
}
}
}
default: 
{
lean_object* v___x_411_; 
lean_del_object(v___x_359_);
lean_dec(v_a_357_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
v___x_411_ = l_Lean_Elab_Term_tryPostpone(v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v___x_412_; 
lean_dec_ref_known(v___x_411_, 1);
v___x_412_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure(v_a_362_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_412_;
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v_a_362_);
v_a_413_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_411_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec_ref(v_a_362_);
lean_del_object(v___x_359_);
lean_dec(v_a_357_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
v_a_421_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_363_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_363_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
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
}
}
else
{
lean_dec(v_a_344_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
return v___x_356_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_del_object(v___x_346_);
lean_dec(v_a_344_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
v_a_458_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_348_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_348_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
else
{
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
return v___x_343_;
}
}
}
else
{
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
return v___x_338_;
}
}
}
else
{
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v_expectedType_x3f_313_);
return v___x_333_;
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v___x_330_);
lean_dec(v___x_328_);
lean_dec(v___x_326_);
lean_dec(v_expectedType_x3f_313_);
v_a_469_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_331_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_331_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForIn___boxed(lean_object* v_stx_477_, lean_object* v_expectedType_x3f_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Elab_Term_elabForIn(v_stx_477_, v_expectedType_x3f_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1(){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_495_ = l_Lean_Elab_Term_termElabAttribute;
v___x_496_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__4));
v___x_497_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2));
v___x_498_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForIn___boxed), 9, 0);
v___x_499_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_495_, v___x_496_, v___x_497_, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___boxed(lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1();
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3(){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__2));
v___x_529_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___closed__6));
v___x_530_ = l_Lean_addBuiltinDeclarationRanges(v___x_528_, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3___boxed(lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3();
return v_res_532_;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabForIn_x27___closed__6(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn_x27___closed__5));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForIn_x27(lean_object* v_stx_552_, lean_object* v_expectedType_x3f_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn_x27___closed__1));
lean_inc(v_stx_552_);
v___x_562_ = l_Lean_Syntax_isOfKind(v_stx_552_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec(v_expectedType_x3f_553_);
lean_dec(v_stx_552_);
v___x_563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_elabForIn_spec__0___redArg();
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = l_Lean_Syntax_getArg(v_stx_552_, v___x_565_);
v___x_567_ = lean_unsigned_to_nat(2u);
v___x_568_ = l_Lean_Syntax_getArg(v_stx_552_, v___x_567_);
v___x_569_ = lean_unsigned_to_nat(3u);
v___x_570_ = l_Lean_Syntax_getArg(v_stx_552_, v___x_569_);
lean_dec(v_stx_552_);
lean_inc(v_expectedType_x3f_553_);
v___x_571_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec_ref_known(v___x_571_, 1);
v___x_572_ = lean_box(0);
v___x_573_ = l_Lean_Elab_Term_elabTerm(v___x_566_, v___x_572_, v___x_562_, v___x_562_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_730_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_730_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_730_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_730_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; 
lean_inc(v_expectedType_x3f_553_);
v___x_578_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn(v_expectedType_x3f_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_729_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_729_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_729_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_729_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; 
lean_inc(v_a_559_);
lean_inc_ref(v_a_558_);
lean_inc(v_a_557_);
lean_inc_ref(v_a_556_);
lean_inc(v_a_574_);
v___x_583_ = lean_infer_type(v_a_574_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_728_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_728_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_728_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_728_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_mkFreshLevelMVar(v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = l_Lean_Level_succ___override(v_a_589_);
v___x_591_ = l_Lean_mkSort(v___x_590_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 1);
lean_ctor_set(v___x_586_, 0, v___x_591_);
v___x_593_ = v___x_586_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_719_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = 0;
v___x_595_ = lean_box(0);
v___x_596_ = l_Lean_Meta_mkFreshExprMVar(v___x_593_, v___x_594_, v___x_595_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_718_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_718_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_718_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_718_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_a_602_; lean_object* v___y_670_; lean_object* v_a_671_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_691_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn_x27___closed__8));
v___x_692_ = lean_mk_empty_array_with_capacity(v___x_567_);
lean_inc(v_a_597_);
v___x_693_ = lean_array_push(v___x_692_, v_a_597_);
lean_inc(v_a_584_);
v___x_694_ = lean_array_push(v___x_693_, v_a_584_);
v___x_695_ = l_Lean_Meta_mkAppM(v___x_691_, v___x_694_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_716_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_716_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_716_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_716_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 1);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_715_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_mkFreshExprMVar(v___x_701_, v___x_594_, v___x_595_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn_x27___closed__9));
v___x_705_ = lean_unsigned_to_nat(4u);
v___x_706_ = lean_mk_empty_array_with_capacity(v___x_705_);
lean_inc(v_a_579_);
v___x_707_ = lean_array_push(v___x_706_, v_a_579_);
lean_inc(v_a_584_);
v___x_708_ = lean_array_push(v___x_707_, v_a_584_);
lean_inc(v_a_597_);
v___x_709_ = lean_array_push(v___x_708_, v_a_597_);
v___x_710_ = lean_array_push(v___x_709_, v_a_703_);
v___x_711_ = l_Lean_Meta_mkAppM(v___x_704_, v___x_710_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; 
lean_dec(v_a_584_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v_a_602_ = v_a_712_;
goto v___jp_601_;
}
else
{
lean_object* v_a_713_; 
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
lean_del_object(v___x_581_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
v_a_713_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_713_);
v___y_670_ = v___x_711_;
v_a_671_ = v_a_713_;
goto v___jp_669_;
}
}
else
{
lean_object* v_a_714_; 
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
lean_del_object(v___x_581_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
v_a_714_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_714_);
v___y_670_ = v___x_702_;
v_a_671_ = v_a_714_;
goto v___jp_669_;
}
}
}
}
else
{
lean_object* v_a_717_; 
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
lean_del_object(v___x_581_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
v_a_717_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_717_);
v___y_670_ = v___x_695_;
v_a_671_ = v_a_717_;
goto v___jp_669_;
}
v___jp_601_:
{
lean_object* v___x_603_; 
lean_inc_ref(v_a_602_);
v___x_603_ = l_Lean_Meta_trySynthInstance(v_a_602_, v___x_572_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
switch(lean_obj_tag(v_a_604_))
{
case 0:
{
lean_object* v___x_605_; 
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
lean_del_object(v___x_581_);
lean_dec(v_a_579_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
v___x_605_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure(v_a_602_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
return v___x_605_;
}
case 1:
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v_a_602_);
v_a_606_ = lean_ctor_get(v_a_604_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_650_ == 0)
{
v___x_608_ = v_a_604_;
v_isShared_609_ = v_isSharedCheck_650_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v_a_604_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_650_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn_x27___closed__4));
v___x_611_ = lean_box(0);
v___x_612_ = l_Lean_Elab_Term_mkConst(v___x_610_, v___x_611_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_649_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_649_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_649_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_649_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_617_ = lean_box(0);
v___x_618_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__9));
if (v_isShared_616_ == 0)
{
lean_ctor_set_tag(v___x_615_, 1);
lean_ctor_set(v___x_615_, 0, v_a_579_);
v___x_620_ = v___x_615_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_579_);
v___x_620_ = v_reuseFailAlloc_648_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_621_, 0, v___x_617_);
lean_ctor_set(v___x_621_, 1, v___x_618_);
lean_ctor_set(v___x_621_, 2, v___x_620_);
lean_ctor_set(v___x_621_, 3, v___x_564_);
v___x_622_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__11));
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v_a_597_);
v___x_624_ = v___x_608_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_597_);
v___x_624_ = v_reuseFailAlloc_647_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_625_, 0, v___x_617_);
lean_ctor_set(v___x_625_, 1, v___x_622_);
lean_ctor_set(v___x_625_, 2, v___x_624_);
lean_ctor_set(v___x_625_, 3, v___x_564_);
v___x_626_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn___closed__13));
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 1);
lean_ctor_set(v___x_599_, 0, v_a_606_);
v___x_628_ = v___x_599_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_606_);
v___x_628_ = v_reuseFailAlloc_646_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_629_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_629_, 0, v___x_617_);
lean_ctor_set(v___x_629_, 1, v___x_626_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
lean_ctor_set(v___x_629_, 3, v___x_564_);
v___x_630_ = lean_mk_empty_array_with_capacity(v___x_569_);
lean_inc_ref(v___x_630_);
v___x_631_ = lean_array_push(v___x_630_, v___x_621_);
v___x_632_ = lean_array_push(v___x_631_, v___x_625_);
v___x_633_ = lean_array_push(v___x_632_, v___x_629_);
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 1);
lean_ctor_set(v___x_581_, 0, v_a_574_);
v___x_635_ = v___x_581_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_574_);
v___x_635_ = v_reuseFailAlloc_645_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_568_);
v___x_637_ = v___x_576_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_568_);
v___x_637_ = v_reuseFailAlloc_644_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; lean_object* v___x_643_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_570_);
v___x_639_ = lean_array_push(v___x_630_, v___x_635_);
v___x_640_ = lean_array_push(v___x_639_, v___x_637_);
v___x_641_ = lean_array_push(v___x_640_, v___x_638_);
v___x_642_ = 0;
v___x_643_ = l_Lean_Elab_Term_elabAppArgs(v_a_613_, v___x_633_, v___x_641_, v_expectedType_x3f_553_, v___x_642_, v___x_642_, v___x_642_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
return v___x_643_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_608_);
lean_dec(v_a_606_);
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
lean_del_object(v___x_581_);
lean_dec(v_a_579_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
return v___x_612_;
}
}
}
default: 
{
lean_object* v___x_651_; 
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
lean_del_object(v___x_581_);
lean_dec(v_a_579_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
v___x_651_ = l_Lean_Elab_Term_tryPostpone(v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_652_; 
lean_dec_ref_known(v___x_651_, 1);
v___x_652_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_throwForInFailure(v_a_602_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
return v___x_652_;
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v_a_602_);
v_a_653_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_651_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v_a_602_);
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
lean_del_object(v___x_581_);
lean_dec(v_a_579_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
v_a_661_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_603_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_603_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
v___jp_669_:
{
uint8_t v___x_672_; 
v___x_672_ = l_Lean_Exception_isInterrupt(v_a_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = l_Lean_Exception_isRuntime(v_a_671_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec_ref(v___y_670_);
v___x_674_ = l_Lean_Elab_Term_tryPostpone(v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec_ref_known(v___x_674_, 1);
v___x_675_ = lean_obj_once(&l_Lean_Elab_Term_elabForIn_x27___closed__6, &l_Lean_Elab_Term_elabForIn_x27___closed__6_once, _init_l_Lean_Elab_Term_elabForIn_x27___closed__6);
v___x_676_ = l_Lean_indentExpr(v_a_584_);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_obj_once(&l_Lean_Elab_Term_elabForIn___closed__18, &l_Lean_Elab_Term_elabForIn___closed__18_once, _init_l_Lean_Elab_Term_elabForIn___closed__18);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = l_Lean_indentExpr(v_a_579_);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_681_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
return v___x_682_;
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_a_584_);
lean_dec(v_a_579_);
v_a_683_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_674_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_674_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_dec(v_a_584_);
lean_dec(v_a_579_);
return v___y_670_;
}
}
else
{
lean_dec_ref(v_a_671_);
lean_dec(v_a_584_);
lean_dec(v_a_579_);
return v___y_670_;
}
}
}
}
else
{
lean_dec(v_a_584_);
lean_del_object(v___x_581_);
lean_dec(v_a_579_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
return v___x_596_;
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_del_object(v___x_586_);
lean_dec(v_a_584_);
lean_del_object(v___x_581_);
lean_dec(v_a_579_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
v_a_720_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_588_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_588_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
else
{
lean_del_object(v___x_581_);
lean_dec(v_a_579_);
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
return v___x_583_;
}
}
}
else
{
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
return v___x_578_;
}
}
}
else
{
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v_expectedType_x3f_553_);
return v___x_573_;
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v___x_570_);
lean_dec(v___x_568_);
lean_dec(v___x_566_);
lean_dec(v_expectedType_x3f_553_);
v_a_731_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_571_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_571_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabForIn_x27___boxed(lean_object* v_stx_739_, lean_object* v_expectedType_x3f_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Elab_Term_elabForIn_x27(v_stx_739_, v_expectedType_x3f_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1(){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_756_ = l_Lean_Elab_Term_termElabAttribute;
v___x_757_ = ((lean_object*)(l_Lean_Elab_Term_elabForIn_x27___closed__1));
v___x_758_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1));
v___x_759_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForIn_x27___boxed), 9, 0);
v___x_760_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_756_, v___x_757_, v___x_758_, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___boxed(lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1();
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3(){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1___closed__1));
v___x_790_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___closed__6));
v___x_791_ = l_Lean_addBuiltinDeclarationRanges(v___x_789_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3___boxed(lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3();
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorIdx___impl(uint8_t v_x_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_box(v_x_794_);
v___x_796_ = lean_obj_tag_nat(v___x_795_);
lean_dec(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorIdx___impl___boxed(lean_object* v_x_797_){
_start:
{
uint8_t v_x_4__boxed_798_; lean_object* v_res_799_; 
v_x_4__boxed_798_ = lean_unbox(v_x_797_);
v_res_799_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorIdx___impl(v_x_4__boxed_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___redArg(lean_object* v_k_800_){
_start:
{
lean_inc(v_k_800_);
return v_k_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___redArg___boxed(lean_object* v_k_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___redArg(v_k_801_);
lean_dec(v_k_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim(lean_object* v_motive_803_, lean_object* v_ctorIdx_804_, uint8_t v_t_805_, lean_object* v_h_806_, lean_object* v_k_807_){
_start:
{
lean_inc(v_k_807_);
return v_k_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___boxed(lean_object* v_motive_808_, lean_object* v_ctorIdx_809_, lean_object* v_t_810_, lean_object* v_h_811_, lean_object* v_k_812_){
_start:
{
uint8_t v_t_boxed_813_; lean_object* v_res_814_; 
v_t_boxed_813_ = lean_unbox(v_t_810_);
v_res_814_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim(v_motive_808_, v_ctorIdx_809_, v_t_boxed_813_, v_h_811_, v_k_812_);
lean_dec(v_k_812_);
lean_dec(v_ctorIdx_809_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___redArg(lean_object* v_regular_815_){
_start:
{
lean_inc(v_regular_815_);
return v_regular_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___redArg___boxed(lean_object* v_regular_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___redArg(v_regular_816_);
lean_dec(v_regular_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim(lean_object* v_motive_818_, uint8_t v_t_819_, lean_object* v_h_820_, lean_object* v_regular_821_){
_start:
{
lean_inc(v_regular_821_);
return v_regular_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___boxed(lean_object* v_motive_822_, lean_object* v_t_823_, lean_object* v_h_824_, lean_object* v_regular_825_){
_start:
{
uint8_t v_t_boxed_826_; lean_object* v_res_827_; 
v_t_boxed_826_ = lean_unbox(v_t_823_);
v_res_827_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim(v_motive_822_, v_t_boxed_826_, v_h_824_, v_regular_825_);
lean_dec(v_regular_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___redArg(lean_object* v_lazy_828_){
_start:
{
lean_inc(v_lazy_828_);
return v_lazy_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___redArg___boxed(lean_object* v_lazy_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___redArg(v_lazy_829_);
lean_dec(v_lazy_829_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim(lean_object* v_motive_831_, uint8_t v_t_832_, lean_object* v_h_833_, lean_object* v_lazy_834_){
_start:
{
lean_inc(v_lazy_834_);
return v_lazy_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___boxed(lean_object* v_motive_835_, lean_object* v_t_836_, lean_object* v_h_837_, lean_object* v_lazy_838_){
_start:
{
uint8_t v_t_boxed_839_; lean_object* v_res_840_; 
v_t_boxed_839_ = lean_unbox(v_t_836_);
v_res_840_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim(v_motive_835_, v_t_boxed_839_, v_h_837_, v_lazy_838_);
lean_dec(v_lazy_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___redArg(lean_object* v_leftact_841_){
_start:
{
lean_inc(v_leftact_841_);
return v_leftact_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___redArg___boxed(lean_object* v_leftact_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___redArg(v_leftact_842_);
lean_dec(v_leftact_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim(lean_object* v_motive_844_, uint8_t v_t_845_, lean_object* v_h_846_, lean_object* v_leftact_847_){
_start:
{
lean_inc(v_leftact_847_);
return v_leftact_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___boxed(lean_object* v_motive_848_, lean_object* v_t_849_, lean_object* v_h_850_, lean_object* v_leftact_851_){
_start:
{
uint8_t v_t_boxed_852_; lean_object* v_res_853_; 
v_t_boxed_852_ = lean_unbox(v_t_849_);
v_res_853_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim(v_motive_848_, v_t_boxed_852_, v_h_850_, v_leftact_851_);
lean_dec(v_leftact_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___redArg(lean_object* v_rightact_854_){
_start:
{
lean_inc(v_rightact_854_);
return v_rightact_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___redArg___boxed(lean_object* v_rightact_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___redArg(v_rightact_855_);
lean_dec(v_rightact_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim(lean_object* v_motive_857_, uint8_t v_t_858_, lean_object* v_h_859_, lean_object* v_rightact_860_){
_start:
{
lean_inc(v_rightact_860_);
return v_rightact_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___boxed(lean_object* v_motive_861_, lean_object* v_t_862_, lean_object* v_h_863_, lean_object* v_rightact_864_){
_start:
{
uint8_t v_t_boxed_865_; lean_object* v_res_866_; 
v_t_boxed_865_ = lean_unbox(v_t_862_);
v_res_866_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim(v_motive_861_, v_t_boxed_865_, v_h_863_, v_rightact_864_);
lean_dec(v_rightact_864_);
return v_res_866_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(uint8_t v_x_867_, uint8_t v_y_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_869_ = lean_box(v_x_867_);
v___x_870_ = lean_obj_tag_nat(v___x_869_);
lean_dec(v___x_869_);
v___x_871_ = lean_box(v_y_868_);
v___x_872_ = lean_obj_tag_nat(v___x_871_);
lean_dec(v___x_871_);
v___x_873_ = lean_nat_dec_eq(v___x_870_, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq___boxed(lean_object* v_x_874_, lean_object* v_y_875_){
_start:
{
uint8_t v_x_24__boxed_876_; uint8_t v_y_25__boxed_877_; uint8_t v_res_878_; lean_object* v_r_879_; 
v_x_24__boxed_876_ = lean_unbox(v_x_874_);
v_y_25__boxed_877_ = lean_unbox(v_y_875_);
v_res_878_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_x_24__boxed_876_, v_y_25__boxed_877_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorIdx___impl(lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_obj_tag_nat(v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorIdx___impl___boxed(lean_object* v_x_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorIdx___impl(v_x_884_);
lean_dec_ref(v_x_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(lean_object* v_t_886_, lean_object* v_k_887_){
_start:
{
switch(lean_obj_tag(v_t_886_))
{
case 1:
{
lean_object* v_ref_888_; uint8_t v_kind_889_; lean_object* v_f_890_; lean_object* v_lhs_891_; lean_object* v_rhs_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_ref_888_ = lean_ctor_get(v_t_886_, 0);
lean_inc(v_ref_888_);
v_kind_889_ = lean_ctor_get_uint8(v_t_886_, sizeof(void*)*4);
v_f_890_ = lean_ctor_get(v_t_886_, 1);
lean_inc_ref(v_f_890_);
v_lhs_891_ = lean_ctor_get(v_t_886_, 2);
lean_inc_ref(v_lhs_891_);
v_rhs_892_ = lean_ctor_get(v_t_886_, 3);
lean_inc_ref(v_rhs_892_);
lean_dec_ref_known(v_t_886_, 4);
v___x_893_ = lean_box(v_kind_889_);
v___x_894_ = lean_apply_5(v_k_887_, v_ref_888_, v___x_893_, v_f_890_, v_lhs_891_, v_rhs_892_);
return v___x_894_;
}
case 3:
{
lean_object* v_macroName_895_; lean_object* v_stx_896_; lean_object* v_stx_x27_897_; lean_object* v_nested_898_; lean_object* v___x_899_; 
v_macroName_895_ = lean_ctor_get(v_t_886_, 0);
lean_inc(v_macroName_895_);
v_stx_896_ = lean_ctor_get(v_t_886_, 1);
lean_inc(v_stx_896_);
v_stx_x27_897_ = lean_ctor_get(v_t_886_, 2);
lean_inc(v_stx_x27_897_);
v_nested_898_ = lean_ctor_get(v_t_886_, 3);
lean_inc_ref(v_nested_898_);
lean_dec_ref_known(v_t_886_, 4);
v___x_899_ = lean_apply_4(v_k_887_, v_macroName_895_, v_stx_896_, v_stx_x27_897_, v_nested_898_);
return v___x_899_;
}
default: 
{
lean_object* v_ref_900_; lean_object* v_infoTrees_901_; lean_object* v_val_902_; lean_object* v___x_903_; 
v_ref_900_ = lean_ctor_get(v_t_886_, 0);
lean_inc(v_ref_900_);
v_infoTrees_901_ = lean_ctor_get(v_t_886_, 1);
lean_inc_ref(v_infoTrees_901_);
v_val_902_ = lean_ctor_get(v_t_886_, 2);
lean_inc_ref(v_val_902_);
lean_dec_ref(v_t_886_);
v___x_903_ = lean_apply_3(v_k_887_, v_ref_900_, v_infoTrees_901_, v_val_902_);
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim(lean_object* v_motive_904_, lean_object* v_ctorIdx_905_, lean_object* v_t_906_, lean_object* v_h_907_, lean_object* v_k_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_906_, v_k_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___boxed(lean_object* v_motive_910_, lean_object* v_ctorIdx_911_, lean_object* v_t_912_, lean_object* v_h_913_, lean_object* v_k_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim(v_motive_910_, v_ctorIdx_911_, v_t_912_, v_h_913_, v_k_914_);
lean_dec(v_ctorIdx_911_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_term_elim___redArg(lean_object* v_t_916_, lean_object* v_term_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_916_, v_term_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_term_elim(lean_object* v_motive_919_, lean_object* v_t_920_, lean_object* v_h_921_, lean_object* v_term_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_920_, v_term_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_binop_elim___redArg(lean_object* v_t_924_, lean_object* v_binop_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_924_, v_binop_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_binop_elim(lean_object* v_motive_927_, lean_object* v_t_928_, lean_object* v_h_929_, lean_object* v_binop_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_928_, v_binop_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_unop_elim___redArg(lean_object* v_t_932_, lean_object* v_unop_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_932_, v_unop_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_unop_elim(lean_object* v_motive_935_, lean_object* v_t_936_, lean_object* v_h_937_, lean_object* v_unop_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_936_, v_unop_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_macroExpansion_elim___redArg(lean_object* v_t_940_, lean_object* v_macroExpansion_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_940_, v_macroExpansion_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_macroExpansion_elim(lean_object* v_motive_943_, lean_object* v_t_944_, lean_object* v_h_945_, lean_object* v_macroExpansion_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_944_, v_macroExpansion_946_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_unsigned_to_nat(32u);
v___x_949_ = lean_mk_empty_array_with_capacity(v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_951_ = ((size_t)5ULL);
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = lean_unsigned_to_nat(32u);
v___x_954_ = lean_mk_empty_array_with_capacity(v___x_953_);
v___x_955_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0);
v___x_956_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_954_);
lean_ctor_set(v___x_956_, 2, v___x_952_);
lean_ctor_set(v___x_956_, 3, v___x_952_);
lean_ctor_set_usize(v___x_956_, 4, v___x_951_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_infoState_960_; lean_object* v_trees_961_; lean_object* v___x_962_; lean_object* v_infoState_963_; lean_object* v_env_964_; lean_object* v_nextMacroScope_965_; lean_object* v_ngen_966_; lean_object* v_auxDeclNGen_967_; lean_object* v_traceState_968_; lean_object* v_cache_969_; lean_object* v_recordedDeps_970_; lean_object* v_messages_971_; lean_object* v_snapshotTasks_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_993_; 
v___x_959_ = lean_st_ref_get(v___y_957_);
v_infoState_960_ = lean_ctor_get(v___x_959_, 8);
lean_inc_ref(v_infoState_960_);
lean_dec(v___x_959_);
v_trees_961_ = lean_ctor_get(v_infoState_960_, 2);
lean_inc_ref(v_trees_961_);
lean_dec_ref(v_infoState_960_);
v___x_962_ = lean_st_ref_take(v___y_957_);
v_infoState_963_ = lean_ctor_get(v___x_962_, 8);
v_env_964_ = lean_ctor_get(v___x_962_, 0);
v_nextMacroScope_965_ = lean_ctor_get(v___x_962_, 1);
v_ngen_966_ = lean_ctor_get(v___x_962_, 2);
v_auxDeclNGen_967_ = lean_ctor_get(v___x_962_, 3);
v_traceState_968_ = lean_ctor_get(v___x_962_, 4);
v_cache_969_ = lean_ctor_get(v___x_962_, 5);
v_recordedDeps_970_ = lean_ctor_get(v___x_962_, 6);
v_messages_971_ = lean_ctor_get(v___x_962_, 7);
v_snapshotTasks_972_ = lean_ctor_get(v___x_962_, 9);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_993_ == 0)
{
v___x_974_ = v___x_962_;
v_isShared_975_ = v_isSharedCheck_993_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_snapshotTasks_972_);
lean_inc(v_infoState_963_);
lean_inc(v_messages_971_);
lean_inc(v_recordedDeps_970_);
lean_inc(v_cache_969_);
lean_inc(v_traceState_968_);
lean_inc(v_auxDeclNGen_967_);
lean_inc(v_ngen_966_);
lean_inc(v_nextMacroScope_965_);
lean_inc(v_env_964_);
lean_dec(v___x_962_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_993_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
uint8_t v_enabled_976_; lean_object* v_assignment_977_; lean_object* v_lazyAssignment_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_991_; 
v_enabled_976_ = lean_ctor_get_uint8(v_infoState_963_, sizeof(void*)*3);
v_assignment_977_ = lean_ctor_get(v_infoState_963_, 0);
v_lazyAssignment_978_ = lean_ctor_get(v_infoState_963_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v_infoState_963_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v_infoState_963_, 2);
lean_dec(v_unused_992_);
v___x_980_ = v_infoState_963_;
v_isShared_981_ = v_isSharedCheck_991_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_lazyAssignment_978_);
lean_inc(v_assignment_977_);
lean_dec(v_infoState_963_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_991_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 2, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_assignment_977_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_lazyAssignment_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v___x_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*3, v_enabled_976_);
v___x_984_ = v_reuseFailAlloc_990_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 8, v___x_984_);
v___x_986_ = v___x_974_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_env_964_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_nextMacroScope_965_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_ngen_966_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_auxDeclNGen_967_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_traceState_968_);
lean_ctor_set(v_reuseFailAlloc_989_, 5, v_cache_969_);
lean_ctor_set(v_reuseFailAlloc_989_, 6, v_recordedDeps_970_);
lean_ctor_set(v_reuseFailAlloc_989_, 7, v_messages_971_);
lean_ctor_set(v_reuseFailAlloc_989_, 8, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_989_, 9, v_snapshotTasks_972_);
v___x_986_ = v_reuseFailAlloc_989_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_st_ref_put(v___y_957_, v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_trees_961_);
return v___x_988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___boxed(lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v___y_994_);
lean_dec(v___y_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0(lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v___y_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___boxed(lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0(v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(lean_object* v_s_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = lean_box(0);
v___x_1022_ = 1;
lean_inc(v_s_1013_);
v___x_1023_ = l_Lean_Elab_Term_elabTerm(v_s_1013_, v___x_1021_, v___x_1022_, v___x_1022_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v_a_1019_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1030_, 0, v_s_1013_);
lean_ctor_set(v___x_1030_, 1, v_a_1026_);
lean_ctor_set(v___x_1030_, 2, v_a_1024_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v_s_1013_);
v_a_1035_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1023_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1023_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf___boxed(lean_object* v_s_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(lean_object* v_beforeStx_1052_, lean_object* v_afterStx_1053_, lean_object* v_x_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_declName_x3f_1062_; lean_object* v_macroStack_1063_; uint8_t v_mayPostpone_1064_; uint8_t v_errToSorry_1065_; lean_object* v_autoBoundImplicitContext_1066_; lean_object* v_autoBoundImplicitForbidden_1067_; lean_object* v_sectionVars_1068_; lean_object* v_sectionFVars_1069_; uint8_t v_implicitLambda_1070_; uint8_t v_heedElabAsElim_1071_; uint8_t v_isNoncomputableSection_1072_; uint8_t v_isMetaSection_1073_; uint8_t v_ignoreTCFailures_1074_; uint8_t v_inPattern_1075_; lean_object* v_tacSnap_x3f_1076_; uint8_t v_saveRecAppSyntax_1077_; uint8_t v_holesAsSyntheticOpaque_1078_; lean_object* v_fixedTermElabs_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_declName_x3f_1062_ = lean_ctor_get(v___y_1055_, 0);
v_macroStack_1063_ = lean_ctor_get(v___y_1055_, 1);
v_mayPostpone_1064_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8);
v_errToSorry_1065_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1066_ = lean_ctor_get(v___y_1055_, 2);
v_autoBoundImplicitForbidden_1067_ = lean_ctor_get(v___y_1055_, 3);
v_sectionVars_1068_ = lean_ctor_get(v___y_1055_, 4);
v_sectionFVars_1069_ = lean_ctor_get(v___y_1055_, 5);
v_implicitLambda_1070_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1071_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1072_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 4);
v_isMetaSection_1073_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_1074_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 6);
v_inPattern_1075_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1076_ = lean_ctor_get(v___y_1055_, 6);
v_saveRecAppSyntax_1077_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1078_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 9);
v_fixedTermElabs_1079_ = lean_ctor_get(v___y_1055_, 7);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_beforeStx_1052_);
lean_ctor_set(v___x_1080_, 1, v_afterStx_1053_);
lean_inc(v_macroStack_1063_);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_macroStack_1063_);
lean_inc_ref(v_fixedTermElabs_1079_);
lean_inc(v_tacSnap_x3f_1076_);
lean_inc(v_sectionFVars_1069_);
lean_inc(v_sectionVars_1068_);
lean_inc_ref(v_autoBoundImplicitForbidden_1067_);
lean_inc(v_autoBoundImplicitContext_1066_);
lean_inc(v_declName_x3f_1062_);
v___x_1082_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_1082_, 0, v_declName_x3f_1062_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
lean_ctor_set(v___x_1082_, 2, v_autoBoundImplicitContext_1066_);
lean_ctor_set(v___x_1082_, 3, v_autoBoundImplicitForbidden_1067_);
lean_ctor_set(v___x_1082_, 4, v_sectionVars_1068_);
lean_ctor_set(v___x_1082_, 5, v_sectionFVars_1069_);
lean_ctor_set(v___x_1082_, 6, v_tacSnap_x3f_1076_);
lean_ctor_set(v___x_1082_, 7, v_fixedTermElabs_1079_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8, v_mayPostpone_1064_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8 + 1, v_errToSorry_1065_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8 + 2, v_implicitLambda_1070_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8 + 3, v_heedElabAsElim_1071_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1072_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8 + 5, v_isMetaSection_1073_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8 + 6, v_ignoreTCFailures_1074_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8 + 7, v_inPattern_1075_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1077_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1078_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
v___x_1083_ = lean_apply_7(v_x_1054_, v___x_1082_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg___boxed(lean_object* v_beforeStx_1084_, lean_object* v_afterStx_1085_, lean_object* v_x_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_beforeStx_1084_, v_afterStx_1085_, v_x_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0(lean_object* v_00_u03b1_1095_, lean_object* v_beforeStx_1096_, lean_object* v_afterStx_1097_, lean_object* v_x_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_beforeStx_1096_, v_afterStx_1097_, v_x_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_beforeStx_1108_, lean_object* v_afterStx_1109_, lean_object* v_x_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0(v_00_u03b1_1107_, v_beforeStx_1108_, v_afterStx_1109_, v_x_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
return v_res_1118_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
lean_ctor_set(v___x_1125_, 2, v___x_1124_);
lean_ctor_set(v___x_1125_, 3, v___x_1124_);
lean_ctor_set(v___x_1125_, 4, v___x_1123_);
lean_ctor_set(v___x_1125_, 5, v___x_1123_);
lean_ctor_set(v___x_1125_, 6, v___x_1123_);
lean_ctor_set(v___x_1125_, 7, v___x_1123_);
lean_ctor_set(v___x_1125_, 8, v___x_1123_);
lean_ctor_set(v___x_1125_, 9, v___x_1123_);
lean_ctor_set(v___x_1125_, 10, v___x_1123_);
lean_ctor_set(v___x_1125_, 11, v___x_1122_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_unsigned_to_nat(32u);
v___x_1127_ = lean_mk_empty_array_with_capacity(v___x_1126_);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1129_ = ((size_t)5ULL);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_unsigned_to_nat(32u);
v___x_1132_ = lean_mk_empty_array_with_capacity(v___x_1131_);
v___x_1133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3);
v___x_1134_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1132_);
lean_ctor_set(v___x_1134_, 2, v___x_1130_);
lean_ctor_set(v___x_1134_, 3, v___x_1130_);
lean_ctor_set_usize(v___x_1134_, 4, v___x_1129_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1135_ = lean_box(1);
v___x_1136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4);
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_1138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1136_);
lean_ctor_set(v___x_1138_, 2, v___x_1135_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__6));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__8));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__10));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__12));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__14));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18));
v___x_1159_ = l_Lean_stringToMessageData(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(lean_object* v_msg_1160_, lean_object* v_declHint_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_env_1166_; uint8_t v___x_1167_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_st_ref_get(v___y_1162_);
v_env_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc_ref(v_env_1166_);
lean_dec(v___x_1165_);
v___x_1167_ = l_Lean_Name_isAnonymous(v_declHint_1161_);
if (v___x_1167_ == 0)
{
uint8_t v_isExporting_1168_; 
v_isExporting_1168_ = lean_ctor_get_uint8(v_env_1166_, sizeof(void*)*13);
if (v_isExporting_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_dec_ref(v_env_1166_);
lean_dec(v_declHint_1161_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_msg_1160_);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
lean_inc_ref(v_env_1166_);
v___x_1170_ = l_Lean_Environment_setExporting(v_env_1166_, v___x_1167_);
lean_inc(v_declHint_1161_);
lean_inc_ref(v___x_1170_);
v___x_1171_ = l_Lean_Environment_contains(v___x_1170_, v_declHint_1161_, v_isExporting_1168_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
lean_dec_ref(v___x_1170_);
lean_dec_ref(v_env_1166_);
lean_dec(v_declHint_1161_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_msg_1160_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_c_1178_; lean_object* v___x_1179_; 
v___x_1173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_1174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5);
v___x_1175_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1170_);
v___x_1176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1170_);
lean_ctor_set(v___x_1176_, 1, v___x_1173_);
lean_ctor_set(v___x_1176_, 2, v___x_1174_);
lean_ctor_set(v___x_1176_, 3, v___x_1175_);
lean_inc(v_declHint_1161_);
v___x_1177_ = l_Lean_MessageData_ofConstName(v_declHint_1161_, v___x_1167_);
v_c_1178_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1178_, 0, v___x_1176_);
lean_ctor_set(v_c_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1170_, v_declHint_1161_);
lean_dec_ref(v___x_1170_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec_ref(v_env_1166_);
lean_dec(v_declHint_1161_);
v___x_1180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v_c_1178_);
v___x_1182_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_MessageData_note(v___x_1183_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_msg_1160_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
else
{
lean_object* v_val_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1221_; 
v_val_1187_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1189_ = v___x_1179_;
v_isShared_1190_ = v_isSharedCheck_1221_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_val_1187_);
lean_dec(v___x_1179_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1221_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v_moduleNames_1192_; lean_object* v_mod_1193_; uint8_t v___x_1194_; 
v___x_1191_ = l_Lean_Environment_header(v_env_1166_);
lean_dec_ref(v_env_1166_);
v_moduleNames_1192_ = lean_ctor_get(v___x_1191_, 4);
lean_inc_ref(v_moduleNames_1192_);
lean_dec_ref(v___x_1191_);
v_mod_1193_ = lean_array_get(v___x_1164_, v_moduleNames_1192_, v_val_1187_);
lean_dec(v_val_1187_);
lean_dec_ref(v_moduleNames_1192_);
v___x_1194_ = l_Lean_isPrivateName(v_declHint_1161_);
lean_dec(v_declHint_1161_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v_c_1178_);
v___x_1197_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = l_Lean_MessageData_ofName(v_mod_1193_);
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = l_Lean_MessageData_note(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_msg_1160_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1204_);
v___x_1206_ = v___x_1189_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v_c_1178_);
v___x_1210_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = l_Lean_MessageData_ofName(v_mod_1193_);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l_Lean_MessageData_note(v___x_1215_);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_msg_1160_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1217_);
v___x_1219_ = v___x_1189_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1222_; 
lean_dec_ref(v_env_1166_);
lean_dec(v_declHint_1161_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_msg_1160_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1223_, lean_object* v_declHint_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1223_, v_declHint_1224_, v___y_1225_);
lean_dec(v___y_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(lean_object* v_msg_1228_, lean_object* v_declHint_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1247_; 
v___x_1237_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1228_, v_declHint_1229_, v___y_1235_);
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1242_ = l_Lean_unknownIdentifierMessageTag;
v___x_1243_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_a_1238_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1243_);
v___x_1245_ = v___x_1240_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4___boxed(lean_object* v_msg_1248_, lean_object* v_declHint_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(v_msg_1248_, v_declHint_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_1258_, lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_toCold_1267_; lean_object* v_currRecDepth_1268_; lean_object* v_ref_1269_; uint16_t v_optionFlags_1270_; uint8_t v_suppressElabErrors_1271_; uint8_t v_checkDeprecated_1272_; uint8_t v_isRecordingDeps_1273_; lean_object* v_ref_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_toCold_1267_ = lean_ctor_get(v___y_1264_, 0);
v_currRecDepth_1268_ = lean_ctor_get(v___y_1264_, 1);
v_ref_1269_ = lean_ctor_get(v___y_1264_, 2);
v_optionFlags_1270_ = lean_ctor_get_uint16(v___y_1264_, sizeof(void*)*3);
v_suppressElabErrors_1271_ = lean_ctor_get_uint8(v___y_1264_, sizeof(void*)*3 + 2);
v_checkDeprecated_1272_ = lean_ctor_get_uint8(v___y_1264_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1273_ = lean_ctor_get_uint8(v___y_1264_, sizeof(void*)*3 + 4);
v_ref_1274_ = l_Lean_replaceRef(v_ref_1258_, v_ref_1269_);
lean_inc(v_currRecDepth_1268_);
lean_inc_ref(v_toCold_1267_);
v___x_1275_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1275_, 0, v_toCold_1267_);
lean_ctor_set(v___x_1275_, 1, v_currRecDepth_1268_);
lean_ctor_set(v___x_1275_, 2, v_ref_1274_);
lean_ctor_set_uint16(v___x_1275_, sizeof(void*)*3, v_optionFlags_1270_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*3 + 2, v_suppressElabErrors_1271_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*3 + 3, v_checkDeprecated_1272_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*3 + 4, v_isRecordingDeps_1273_);
v___x_1276_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___x_1275_, v___y_1265_);
lean_dec_ref_known(v___x_1275_, 3);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1277_, lean_object* v_msg_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_1277_, v_msg_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v_ref_1277_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(lean_object* v_ref_1287_, lean_object* v_msg_1288_, lean_object* v_declHint_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; lean_object* v_a_1298_; lean_object* v___x_1299_; 
v___x_1297_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(v_msg_1288_, v_declHint_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_1287_, v_a_1298_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg___boxed(lean_object* v_ref_1300_, lean_object* v_msg_1301_, lean_object* v_declHint_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_1300_, v_msg_1301_, v_declHint_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v_ref_1300_);
return v_res_1310_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__0));
v___x_1313_ = l_Lean_stringToMessageData(v___x_1312_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__2));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(lean_object* v_ref_1317_, lean_object* v_constName_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1326_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1);
v___x_1327_ = 0;
lean_inc(v_constName_1318_);
v___x_1328_ = l_Lean_MessageData_ofConstName(v_constName_1318_, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1326_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_1317_, v___x_1331_, v_constName_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___boxed(lean_object* v_ref_1333_, lean_object* v_constName_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_ref_1333_, v_constName_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v_ref_1333_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed(lean_object* v_snd_1379_, lean_object* v_fst_1380_, lean_object* v_s_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0(v_snd_1379_, v_fst_1380_, v_s_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(lean_object* v_ref_1400_, uint8_t v_kind_1401_, lean_object* v_f_1402_, lean_object* v_lhs_1403_, lean_object* v_rhs_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_1413_ = 0;
lean_inc(v_f_1402_);
v___x_1414_ = l_Lean_Elab_Term_resolveId_x3f(v_f_1402_, v___x_1412_, v___x_1413_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1449_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1449_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1449_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
if (lean_obj_tag(v_a_1415_) == 1)
{
lean_object* v_val_1419_; lean_object* v___y_1421_; lean_object* v_rhs_1422_; lean_object* v_lhs_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; uint8_t v___x_1441_; uint8_t v___x_1442_; 
lean_dec(v_f_1402_);
v_val_1419_ = lean_ctor_get(v_a_1415_, 0);
lean_inc(v_val_1419_);
lean_dec_ref_known(v_a_1415_, 1);
v___x_1441_ = 2;
v___x_1442_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_1401_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_lhs_1403_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1443_, 1);
v_lhs_1428_ = v_a_1444_;
v___y_1429_ = v_a_1405_;
v___y_1430_ = v_a_1406_;
v___y_1431_ = v_a_1407_;
v___y_1432_ = v_a_1408_;
v___y_1433_ = v_a_1409_;
v___y_1434_ = v_a_1410_;
goto v___jp_1427_;
}
else
{
lean_dec(v_val_1419_);
lean_del_object(v___x_1417_);
lean_dec(v_rhs_1404_);
lean_dec(v_ref_1400_);
return v___x_1443_;
}
}
else
{
lean_object* v___x_1445_; 
v___x_1445_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_lhs_1403_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v_lhs_1428_ = v_a_1446_;
v___y_1429_ = v_a_1405_;
v___y_1430_ = v_a_1406_;
v___y_1431_ = v_a_1407_;
v___y_1432_ = v_a_1408_;
v___y_1433_ = v_a_1409_;
v___y_1434_ = v_a_1410_;
goto v___jp_1427_;
}
else
{
lean_dec(v_val_1419_);
lean_del_object(v___x_1417_);
lean_dec(v_rhs_1404_);
lean_dec(v_ref_1400_);
return v___x_1445_;
}
}
v___jp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1423_, 0, v_ref_1400_);
lean_ctor_set(v___x_1423_, 1, v_val_1419_);
lean_ctor_set(v___x_1423_, 2, v___y_1421_);
lean_ctor_set(v___x_1423_, 3, v_rhs_1422_);
lean_ctor_set_uint8(v___x_1423_, sizeof(void*)*4, v_kind_1401_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1423_);
v___x_1425_ = v___x_1417_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
v___jp_1427_:
{
uint8_t v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = 3;
v___x_1436_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_1401_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_rhs_1404_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___y_1421_ = v_lhs_1428_;
v_rhs_1422_ = v_a_1438_;
goto v___jp_1420_;
}
else
{
lean_dec_ref(v_lhs_1428_);
lean_dec(v_val_1419_);
lean_del_object(v___x_1417_);
lean_dec(v_ref_1400_);
return v___x_1437_;
}
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_rhs_1404_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___y_1421_ = v_lhs_1428_;
v_rhs_1422_ = v_a_1440_;
goto v___jp_1420_;
}
else
{
lean_dec_ref(v_lhs_1428_);
lean_dec(v_val_1419_);
lean_del_object(v___x_1417_);
lean_dec(v_ref_1400_);
return v___x_1439_;
}
}
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_del_object(v___x_1417_);
lean_dec(v_a_1415_);
lean_dec(v_rhs_1404_);
lean_dec(v_lhs_1403_);
lean_dec(v_ref_1400_);
v___x_1447_ = l_Lean_Syntax_getId(v_f_1402_);
v___x_1448_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_f_1402_, v___x_1447_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_f_1402_);
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_rhs_1404_);
lean_dec(v_lhs_1403_);
lean_dec(v_f_1402_);
lean_dec(v_ref_1400_);
v_a_1450_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1414_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1414_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(lean_object* v_ref_1458_, lean_object* v_f_1459_, lean_object* v_arg_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_1469_ = 0;
lean_inc(v_f_1459_);
v___x_1470_ = l_Lean_Elab_Term_resolveId_x3f(v_f_1459_, v___x_1468_, v___x_1469_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
if (lean_obj_tag(v_a_1471_) == 1)
{
lean_object* v_val_1472_; lean_object* v___x_1473_; 
lean_dec(v_f_1459_);
v_val_1472_ = lean_ctor_get(v_a_1471_, 0);
lean_inc(v_val_1472_);
lean_dec_ref_known(v_a_1471_, 1);
v___x_1473_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_arg_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1482_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1478_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1478_, 0, v_ref_1458_);
lean_ctor_set(v___x_1478_, 1, v_val_1472_);
lean_ctor_set(v___x_1478_, 2, v_a_1474_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1478_);
v___x_1480_ = v___x_1476_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_dec(v_val_1472_);
lean_dec(v_ref_1458_);
return v___x_1473_;
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v_a_1471_);
lean_dec(v_arg_1460_);
lean_dec(v_ref_1458_);
v___x_1483_ = l_Lean_Syntax_getId(v_f_1459_);
v___x_1484_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_f_1459_, v___x_1483_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_f_1459_);
return v___x_1484_;
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_arg_1460_);
lean_dec(v_f_1459_);
lean_dec(v_ref_1458_);
v_a_1485_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1470_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1470_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(lean_object* v_s_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1));
lean_inc(v_s_1493_);
v___x_1502_ = l_Lean_Syntax_isOfKind(v_s_1493_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3));
lean_inc(v_s_1493_);
v___x_1504_ = l_Lean_Syntax_isOfKind(v_s_1493_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5));
lean_inc(v_s_1493_);
v___x_1506_ = l_Lean_Syntax_isOfKind(v_s_1493_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7));
lean_inc(v_s_1493_);
v___x_1508_ = l_Lean_Syntax_isOfKind(v_s_1493_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9));
lean_inc(v_s_1493_);
v___x_1510_ = l_Lean_Syntax_isOfKind(v_s_1493_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11));
lean_inc(v_s_1493_);
v___x_1512_ = l_Lean_Syntax_isOfKind(v_s_1493_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v_toCold_1513_; lean_object* v_currRecDepth_1514_; lean_object* v_ref_1515_; uint16_t v_optionFlags_1516_; uint8_t v_suppressElabErrors_1517_; uint8_t v_checkDeprecated_1518_; uint8_t v_isRecordingDeps_1519_; lean_object* v_ref_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_toCold_1513_ = lean_ctor_get(v_a_1498_, 0);
v_currRecDepth_1514_ = lean_ctor_get(v_a_1498_, 1);
v_ref_1515_ = lean_ctor_get(v_a_1498_, 2);
v_optionFlags_1516_ = lean_ctor_get_uint16(v_a_1498_, sizeof(void*)*3);
v_suppressElabErrors_1517_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 2);
v_checkDeprecated_1518_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1519_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 4);
v_ref_1520_ = l_Lean_replaceRef(v_s_1493_, v_ref_1515_);
lean_inc(v_currRecDepth_1514_);
lean_inc_ref(v_toCold_1513_);
v___x_1521_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1521_, 0, v_toCold_1513_);
lean_ctor_set(v___x_1521_, 1, v_currRecDepth_1514_);
lean_ctor_set(v___x_1521_, 2, v_ref_1520_);
lean_ctor_set_uint16(v___x_1521_, sizeof(void*)*3, v_optionFlags_1516_);
lean_ctor_set_uint8(v___x_1521_, sizeof(void*)*3 + 2, v_suppressElabErrors_1517_);
lean_ctor_set_uint8(v___x_1521_, sizeof(void*)*3 + 3, v_checkDeprecated_1518_);
lean_ctor_set_uint8(v___x_1521_, sizeof(void*)*3 + 4, v_isRecordingDeps_1519_);
lean_inc(v_s_1493_);
v___x_1522_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1521_, v_a_1499_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
if (lean_obj_tag(v_a_1523_) == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1521_, v_a_1499_);
lean_dec_ref_known(v___x_1521_, 3);
return v___x_1524_;
}
else
{
lean_object* v_val_1525_; lean_object* v_fst_1526_; lean_object* v_snd_1527_; lean_object* v___f_1528_; lean_object* v___x_1529_; 
v_val_1525_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_val_1525_);
lean_dec_ref_known(v_a_1523_, 1);
v_fst_1526_ = lean_ctor_get(v_val_1525_, 0);
lean_inc(v_fst_1526_);
v_snd_1527_ = lean_ctor_get(v_val_1525_, 1);
lean_inc_n(v_snd_1527_, 2);
lean_dec(v_val_1525_);
lean_inc(v_s_1493_);
v___f_1528_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1528_, 0, v_snd_1527_);
lean_closure_set(v___f_1528_, 1, v_fst_1526_);
lean_closure_set(v___f_1528_, 2, v_s_1493_);
v___x_1529_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1493_, v_snd_1527_, v___f_1528_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1521_, v_a_1499_);
lean_dec_ref_known(v___x_1521_, 3);
return v___x_1529_;
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref_known(v___x_1521_, 3);
lean_dec(v_s_1493_);
v_a_1530_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1522_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1522_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1538_);
v___x_1540_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13));
lean_inc(v___x_1539_);
v___x_1541_ = l_Lean_Syntax_isOfKind(v___x_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v_toCold_1542_; lean_object* v_currRecDepth_1543_; lean_object* v_ref_1544_; uint16_t v_optionFlags_1545_; uint8_t v_suppressElabErrors_1546_; uint8_t v_checkDeprecated_1547_; uint8_t v_isRecordingDeps_1548_; lean_object* v_ref_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v___x_1539_);
v_toCold_1542_ = lean_ctor_get(v_a_1498_, 0);
v_currRecDepth_1543_ = lean_ctor_get(v_a_1498_, 1);
v_ref_1544_ = lean_ctor_get(v_a_1498_, 2);
v_optionFlags_1545_ = lean_ctor_get_uint16(v_a_1498_, sizeof(void*)*3);
v_suppressElabErrors_1546_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 2);
v_checkDeprecated_1547_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1548_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 4);
v_ref_1549_ = l_Lean_replaceRef(v_s_1493_, v_ref_1544_);
lean_inc(v_currRecDepth_1543_);
lean_inc_ref(v_toCold_1542_);
v___x_1550_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1550_, 0, v_toCold_1542_);
lean_ctor_set(v___x_1550_, 1, v_currRecDepth_1543_);
lean_ctor_set(v___x_1550_, 2, v_ref_1549_);
lean_ctor_set_uint16(v___x_1550_, sizeof(void*)*3, v_optionFlags_1545_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*3 + 2, v_suppressElabErrors_1546_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*3 + 3, v_checkDeprecated_1547_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*3 + 4, v_isRecordingDeps_1548_);
lean_inc(v_s_1493_);
v___x_1551_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1550_, v_a_1499_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
if (lean_obj_tag(v_a_1552_) == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1550_, v_a_1499_);
lean_dec_ref_known(v___x_1550_, 3);
return v___x_1553_;
}
else
{
lean_object* v_val_1554_; lean_object* v_fst_1555_; lean_object* v_snd_1556_; lean_object* v___f_1557_; lean_object* v___x_1558_; 
v_val_1554_ = lean_ctor_get(v_a_1552_, 0);
lean_inc(v_val_1554_);
lean_dec_ref_known(v_a_1552_, 1);
v_fst_1555_ = lean_ctor_get(v_val_1554_, 0);
lean_inc(v_fst_1555_);
v_snd_1556_ = lean_ctor_get(v_val_1554_, 1);
lean_inc_n(v_snd_1556_, 2);
lean_dec(v_val_1554_);
lean_inc(v_s_1493_);
v___f_1557_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1557_, 0, v_snd_1556_);
lean_closure_set(v___f_1557_, 1, v_fst_1555_);
lean_closure_set(v___f_1557_, 2, v_s_1493_);
v___x_1558_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1493_, v_snd_1556_, v___f_1557_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1550_, v_a_1499_);
lean_dec_ref_known(v___x_1550_, 3);
return v___x_1558_;
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref_known(v___x_1550_, 3);
lean_dec(v_s_1493_);
v_a_1559_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1551_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1551_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_object* v___x_1567_; lean_object* v_h_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1567_ = lean_unsigned_to_nat(1u);
v_h_1568_ = l_Lean_Syntax_getArg(v___x_1539_, v___x_1567_);
lean_dec(v___x_1539_);
v___x_1569_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__15));
lean_inc(v_h_1568_);
v___x_1570_ = l_Lean_Syntax_isOfKind(v_h_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v_toCold_1571_; lean_object* v_currRecDepth_1572_; lean_object* v_ref_1573_; uint16_t v_optionFlags_1574_; uint8_t v_suppressElabErrors_1575_; uint8_t v_checkDeprecated_1576_; uint8_t v_isRecordingDeps_1577_; lean_object* v_ref_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec(v_h_1568_);
v_toCold_1571_ = lean_ctor_get(v_a_1498_, 0);
v_currRecDepth_1572_ = lean_ctor_get(v_a_1498_, 1);
v_ref_1573_ = lean_ctor_get(v_a_1498_, 2);
v_optionFlags_1574_ = lean_ctor_get_uint16(v_a_1498_, sizeof(void*)*3);
v_suppressElabErrors_1575_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 2);
v_checkDeprecated_1576_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1577_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 4);
v_ref_1578_ = l_Lean_replaceRef(v_s_1493_, v_ref_1573_);
lean_inc(v_currRecDepth_1572_);
lean_inc_ref(v_toCold_1571_);
v___x_1579_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1579_, 0, v_toCold_1571_);
lean_ctor_set(v___x_1579_, 1, v_currRecDepth_1572_);
lean_ctor_set(v___x_1579_, 2, v_ref_1578_);
lean_ctor_set_uint16(v___x_1579_, sizeof(void*)*3, v_optionFlags_1574_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3 + 2, v_suppressElabErrors_1575_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3 + 3, v_checkDeprecated_1576_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3 + 4, v_isRecordingDeps_1577_);
lean_inc(v_s_1493_);
v___x_1580_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1579_, v_a_1499_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
if (lean_obj_tag(v_a_1581_) == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1579_, v_a_1499_);
lean_dec_ref_known(v___x_1579_, 3);
return v___x_1582_;
}
else
{
lean_object* v_val_1583_; lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; 
v_val_1583_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v_a_1581_, 1);
v_fst_1584_ = lean_ctor_get(v_val_1583_, 0);
lean_inc(v_fst_1584_);
v_snd_1585_ = lean_ctor_get(v_val_1583_, 1);
lean_inc_n(v_snd_1585_, 2);
lean_dec(v_val_1583_);
lean_inc(v_s_1493_);
v___f_1586_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1586_, 0, v_snd_1585_);
lean_closure_set(v___f_1586_, 1, v_fst_1584_);
lean_closure_set(v___f_1586_, 2, v_s_1493_);
v___x_1587_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1493_, v_snd_1585_, v___f_1586_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1579_, v_a_1499_);
lean_dec_ref_known(v___x_1579_, 3);
return v___x_1587_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref_known(v___x_1579_, 3);
lean_dec(v_s_1493_);
v_a_1588_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1580_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1580_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1596_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1567_);
v___x_1597_ = l_Lean_TSyntax_getHygieneInfo(v_h_1568_);
lean_dec(v_h_1568_);
v___x_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_inc(v___x_1596_);
v___x_1599_ = l_Lean_Elab_Term_hasCDot(v___x_1596_, v___x_1598_);
lean_dec_ref_known(v___x_1598_, 1);
if (v___x_1599_ == 0)
{
lean_dec(v_s_1493_);
v_s_1493_ = v___x_1596_;
goto _start;
}
else
{
lean_object* v___x_1601_; 
lean_dec(v___x_1596_);
v___x_1601_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1601_;
}
}
}
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; 
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1602_);
v___x_1604_ = lean_unsigned_to_nat(2u);
v___x_1605_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1604_);
v___x_1606_ = lean_unsigned_to_nat(3u);
v___x_1607_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1606_);
v___x_1608_ = 3;
v___x_1609_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1493_, v___x_1608_, v___x_1603_, v___x_1605_, v___x_1607_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1609_;
}
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1610_);
v___x_1612_ = lean_unsigned_to_nat(2u);
v___x_1613_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1612_);
v___x_1614_ = lean_unsigned_to_nat(3u);
v___x_1615_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1614_);
v___x_1616_ = 2;
v___x_1617_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1493_, v___x_1616_, v___x_1611_, v___x_1613_, v___x_1615_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1617_;
}
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1618_ = lean_unsigned_to_nat(1u);
v___x_1619_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1618_);
v___x_1620_ = lean_unsigned_to_nat(2u);
v___x_1621_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1620_);
v___x_1622_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(v_s_1493_, v___x_1619_, v___x_1621_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1622_;
}
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; 
v___x_1623_ = lean_unsigned_to_nat(1u);
v___x_1624_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1623_);
v___x_1625_ = lean_unsigned_to_nat(2u);
v___x_1626_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1625_);
v___x_1627_ = lean_unsigned_to_nat(3u);
v___x_1628_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1627_);
v___x_1629_ = 1;
v___x_1630_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1493_, v___x_1629_, v___x_1624_, v___x_1626_, v___x_1628_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1630_;
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; 
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1631_);
v___x_1633_ = lean_unsigned_to_nat(2u);
v___x_1634_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1633_);
v___x_1635_ = lean_unsigned_to_nat(3u);
v___x_1636_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1635_);
v___x_1637_ = 0;
v___x_1638_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1493_, v___x_1637_, v___x_1632_, v___x_1634_, v___x_1636_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0(lean_object* v_snd_1639_, lean_object* v_fst_1640_, lean_object* v_s_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; 
lean_inc(v_snd_1639_);
v___x_1649_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_snd_1639_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1654_, 0, v_fst_1640_);
lean_ctor_set(v___x_1654_, 1, v_s_1641_);
lean_ctor_set(v___x_1654_, 2, v_snd_1639_);
lean_ctor_set(v___x_1654_, 3, v_a_1650_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_dec(v_s_1641_);
lean_dec(v_fst_1640_);
lean_dec(v_snd_1639_);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___boxed(lean_object* v_ref_1659_, lean_object* v_f_1660_, lean_object* v_arg_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(v_ref_1659_, v_f_1660_, v_arg_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp___boxed(lean_object* v_ref_1670_, lean_object* v_kind_1671_, lean_object* v_f_1672_, lean_object* v_lhs_1673_, lean_object* v_rhs_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
uint8_t v_kind_boxed_1682_; lean_object* v_res_1683_; 
v_kind_boxed_1682_ = lean_unbox(v_kind_1671_);
v_res_1683_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_ref_1670_, v_kind_boxed_1682_, v_f_1672_, v_lhs_1673_, v_rhs_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed(lean_object* v_s_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_s_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2(lean_object* v_00_u03b1_1693_, lean_object* v_ref_1694_, lean_object* v_constName_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_ref_1694_, v_constName_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___boxed(lean_object* v_00_u03b1_1704_, lean_object* v_ref_1705_, lean_object* v_constName_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2(v_00_u03b1_1704_, v_ref_1705_, v_constName_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v_ref_1705_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2(lean_object* v_00_u03b1_1715_, lean_object* v_ref_1716_, lean_object* v_msg_1717_, lean_object* v_declHint_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_1716_, v_msg_1717_, v_declHint_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1727_, lean_object* v_ref_1728_, lean_object* v_msg_1729_, lean_object* v_declHint_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2(v_00_u03b1_1727_, v_ref_1728_, v_msg_1729_, v_declHint_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v_ref_1728_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5(lean_object* v_msg_1739_, lean_object* v_declHint_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1739_, v_declHint_1740_, v___y_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1749_, lean_object* v_declHint_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5(v_msg_1749_, v_declHint_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_1759_, lean_object* v_ref_1760_, lean_object* v_msg_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_1760_, v_msg_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_ref_1771_, lean_object* v_msg_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5(v_00_u03b1_1770_, v_ref_1771_, v_msg_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v_ref_1771_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(lean_object* v_s_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_s_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; uint8_t v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1789_, 1);
v___x_1791_ = 0;
v___x_1792_ = 0;
v___x_1793_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1791_, v___x_1792_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v___x_1793_, 0);
lean_dec(v_unused_1801_);
v___x_1795_ = v___x_1793_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_dec(v___x_1793_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v_a_1790_);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1790_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v_a_1790_);
v_a_1802_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1793_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1793_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree___boxed(lean_object* v_s_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v_s_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0(lean_object* v_toType_1819_, uint8_t v___x_1820_, lean_object* v_x_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Meta_coerceSimple_x3f(v_x_1821_, v_toType_1819_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1843_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1843_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1843_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
if (lean_obj_tag(v_a_1830_) == 1)
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_dec_ref_known(v_a_1830_, 1);
v___x_1834_ = lean_box(v___x_1820_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
else
{
uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_dec(v_a_1830_);
v___x_1838_ = 0;
v___x_1839_ = lean_box(v___x_1838_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1839_);
v___x_1841_ = v___x_1832_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
v_a_1844_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1829_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1829_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0___boxed(lean_object* v_toType_1852_, lean_object* v___x_1853_, lean_object* v_x_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
uint8_t v___x_1720__boxed_1862_; lean_object* v_res_1863_; 
v___x_1720__boxed_1862_ = lean_unbox(v___x_1853_);
v_res_1863_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0(v_toType_1852_, v___x_1720__boxed_1862_, v_x_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v_b_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
lean_inc(v___y_1871_);
lean_inc_ref(v___y_1870_);
lean_inc(v___y_1869_);
lean_inc_ref(v___y_1868_);
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
v___x_1873_ = lean_apply_8(v_k_1864_, v_b_1867_, v___y_1865_, v___y_1866_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, lean_box(0));
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0(v_k_1874_, v___y_1875_, v___y_1876_, v_b_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(lean_object* v_name_1884_, uint8_t v_bi_1885_, lean_object* v_type_1886_, lean_object* v_k_1887_, uint8_t v_kind_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___f_1896_; lean_object* v___x_1897_; 
lean_inc(v___y_1890_);
lean_inc_ref(v___y_1889_);
v___f_1896_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1896_, 0, v_k_1887_);
lean_closure_set(v___f_1896_, 1, v___y_1889_);
lean_closure_set(v___f_1896_, 2, v___y_1890_);
v___x_1897_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1884_, v_bi_1885_, v_type_1886_, v___f_1896_, v_kind_1888_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1897_) == 0)
{
return v___x_1897_;
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___boxed(lean_object* v_name_1906_, lean_object* v_bi_1907_, lean_object* v_type_1908_, lean_object* v_k_1909_, lean_object* v_kind_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
uint8_t v_bi_boxed_1918_; uint8_t v_kind_boxed_1919_; lean_object* v_res_1920_; 
v_bi_boxed_1918_ = lean_unbox(v_bi_1907_);
v_kind_boxed_1919_ = lean_unbox(v_kind_1910_);
v_res_1920_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_1906_, v_bi_boxed_1918_, v_type_1908_, v_k_1909_, v_kind_boxed_1919_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(lean_object* v_name_1921_, lean_object* v_type_1922_, lean_object* v_k_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v___x_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = 0;
v___x_1932_ = 0;
v___x_1933_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_1921_, v___x_1931_, v_type_1922_, v_k_1923_, v___x_1932_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg___boxed(lean_object* v_name_1934_, lean_object* v_type_1935_, lean_object* v_k_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v_name_1934_, v_type_1935_, v_k_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(lean_object* v_fromType_1951_, lean_object* v_toType_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v_env_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; uint8_t v___x_1964_; 
v___x_1960_ = lean_st_ref_get(v_a_1958_);
v_env_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc_ref(v_env_1961_);
lean_dec(v___x_1960_);
v___x_1962_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__1));
v___x_1963_ = 1;
v___x_1964_ = l_Lean_Environment_contains(v_env_1961_, v___x_1962_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec_ref(v_toType_1952_);
lean_dec_ref(v_fromType_1951_);
v___x_1965_ = lean_box(v___x_1964_);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; lean_object* v___f_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = lean_box(v___x_1963_);
v___f_1968_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1968_, 0, v_toType_1952_);
lean_closure_set(v___f_1968_, 1, v___x_1967_);
v___x_1969_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__3));
v___x_1970_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v___x_1969_, v_fromType_1951_, v___f_1968_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___boxed(lean_object* v_fromType_1971_, lean_object* v_toType_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v_fromType_1971_, v_toType_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0(lean_object* v_00_u03b1_1981_, lean_object* v_name_1982_, uint8_t v_bi_1983_, lean_object* v_type_1984_, lean_object* v_k_1985_, uint8_t v_kind_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_1982_, v_bi_1983_, v_type_1984_, v_k_1985_, v_kind_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1995_, lean_object* v_name_1996_, lean_object* v_bi_1997_, lean_object* v_type_1998_, lean_object* v_k_1999_, lean_object* v_kind_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
uint8_t v_bi_boxed_2008_; uint8_t v_kind_boxed_2009_; lean_object* v_res_2010_; 
v_bi_boxed_2008_ = lean_unbox(v_bi_1997_);
v_kind_boxed_2009_ = lean_unbox(v_kind_2000_);
v_res_2010_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0(v_00_u03b1_1995_, v_name_1996_, v_bi_boxed_2008_, v_type_1998_, v_k_1999_, v_kind_boxed_2009_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0(lean_object* v_00_u03b1_2011_, lean_object* v_name_2012_, lean_object* v_type_2013_, lean_object* v_k_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v_name_2012_, v_type_2013_, v_k_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___boxed(lean_object* v_00_u03b1_2023_, lean_object* v_name_2024_, lean_object* v_type_2025_, lean_object* v_k_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0(v_00_u03b1_2023_, v_name_2024_, v_type_2025_, v_k_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2034_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(lean_object* v_x_2035_){
_start:
{
switch(lean_obj_tag(v_x_2035_))
{
case 2:
{
uint8_t v___x_2036_; 
v___x_2036_ = 1;
return v___x_2036_;
}
case 5:
{
lean_object* v_fn_2037_; 
v_fn_2037_ = lean_ctor_get(v_x_2035_, 0);
v_x_2035_ = v_fn_2037_;
goto _start;
}
case 8:
{
lean_object* v_body_2039_; 
v_body_2039_ = lean_ctor_get(v_x_2035_, 3);
v_x_2035_ = v_body_2039_;
goto _start;
}
case 10:
{
lean_object* v_expr_2041_; 
v_expr_2041_ = lean_ctor_get(v_x_2035_, 1);
v_x_2035_ = v_expr_2041_;
goto _start;
}
default: 
{
uint8_t v___x_2043_; 
v___x_2043_ = 0;
return v___x_2043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown___boxed(lean_object* v_x_2044_){
_start:
{
uint8_t v_res_2045_; lean_object* v_r_2046_; 
v_res_2045_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v_x_2044_);
lean_dec_ref(v_x_2044_);
v_r_2046_ = lean_box(v_res_2045_);
return v_r_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(lean_object* v_e_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v___x_2050_; 
v___x_2050_ = l_Lean_Expr_hasMVar(v_e_2047_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_e_2047_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; lean_object* v_mctx_2053_; lean_object* v___x_2054_; lean_object* v_fst_2055_; lean_object* v_snd_2056_; lean_object* v___x_2057_; lean_object* v_cache_2058_; lean_object* v_zetaDeltaFVarIds_2059_; lean_object* v_postponed_2060_; lean_object* v_diag_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2070_; 
v___x_2052_ = lean_st_ref_get(v___y_2048_);
v_mctx_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_ref(v_mctx_2053_);
lean_dec(v___x_2052_);
v___x_2054_ = l_Lean_instantiateMVarsCore(v_mctx_2053_, v_e_2047_);
v_fst_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_fst_2055_);
v_snd_2056_ = lean_ctor_get(v___x_2054_, 1);
lean_inc(v_snd_2056_);
lean_dec_ref(v___x_2054_);
v___x_2057_ = lean_st_ref_take(v___y_2048_);
v_cache_2058_ = lean_ctor_get(v___x_2057_, 1);
v_zetaDeltaFVarIds_2059_ = lean_ctor_get(v___x_2057_, 2);
v_postponed_2060_ = lean_ctor_get(v___x_2057_, 3);
v_diag_2061_ = lean_ctor_get(v___x_2057_, 4);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v___x_2057_, 0);
lean_dec(v_unused_2071_);
v___x_2063_ = v___x_2057_;
v_isShared_2064_ = v_isSharedCheck_2070_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_diag_2061_);
lean_inc(v_postponed_2060_);
lean_inc(v_zetaDeltaFVarIds_2059_);
lean_inc(v_cache_2058_);
lean_dec(v___x_2057_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2070_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v_snd_2056_);
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_snd_2056_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_cache_2058_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_zetaDeltaFVarIds_2059_);
lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_postponed_2060_);
lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_diag_2061_);
v___x_2066_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_st_ref_put(v___y_2048_, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v_fst_2055_);
return v___x_2068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg___boxed(lean_object* v_e_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_e_2072_, v___y_2073_);
lean_dec(v___y_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0(lean_object* v_e_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_e_2076_, v___y_2081_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___boxed(lean_object* v_e_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0(v_e_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0(lean_object* v_k_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2105_; 
lean_inc(v___y_2099_);
lean_inc_ref(v___y_2098_);
lean_inc(v___y_2097_);
v___x_2105_ = lean_apply_8(v_k_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, lean_box(0));
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0(v_k_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(lean_object* v_k_2116_, uint8_t v_allowLevelAssignments_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___f_2126_; lean_object* v___x_2127_; 
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___y_2118_);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2126_, 0, v_k_2116_);
lean_closure_set(v___f_2126_, 1, v___y_2118_);
lean_closure_set(v___f_2126_, 2, v___y_2119_);
lean_closure_set(v___f_2126_, 3, v___y_2120_);
v___x_2127_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2117_, v___f_2126_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2127_) == 0)
{
return v___x_2127_;
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___boxed(lean_object* v_k_2136_, lean_object* v_allowLevelAssignments_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2146_; lean_object* v_res_2147_; 
v_allowLevelAssignments_boxed_2146_ = lean_unbox(v_allowLevelAssignments_2137_);
v_res_2147_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v_k_2136_, v_allowLevelAssignments_boxed_2146_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1(lean_object* v_00_u03b1_2148_, lean_object* v_k_2149_, uint8_t v_allowLevelAssignments_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v_k_2149_, v_allowLevelAssignments_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___boxed(lean_object* v_00_u03b1_2160_, lean_object* v_k_2161_, lean_object* v_allowLevelAssignments_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2171_; lean_object* v_res_2172_; 
v_allowLevelAssignments_boxed_2171_ = lean_unbox(v_allowLevelAssignments_2162_);
v_res_2172_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1(v_00_u03b1_2160_, v_k_2161_, v_allowLevelAssignments_boxed_2171_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0(uint8_t v___x_2173_, lean_object* v_val_2174_, lean_object* v___x_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; uint8_t v_foApprox_2185_; uint8_t v_ctxApprox_2186_; uint8_t v_quasiPatternApprox_2187_; uint8_t v_constApprox_2188_; uint8_t v_unificationHints_2189_; uint8_t v_proofIrrelevance_2190_; uint8_t v_assignSyntheticOpaque_2191_; uint8_t v_offsetCnstrs_2192_; uint8_t v_transparency_2193_; uint8_t v_etaStruct_2194_; uint8_t v_univApprox_2195_; uint8_t v_iota_2196_; uint8_t v_beta_2197_; uint8_t v_proj_2198_; uint8_t v_zeta_2199_; uint8_t v_zetaDelta_2200_; uint8_t v_zetaUnused_2201_; uint8_t v_zetaHave_2202_; uint8_t v_canUnfoldPredicateConfig_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2224_; 
v___x_2184_ = l_Lean_Meta_Context_config(v___y_2179_);
v_foApprox_2185_ = lean_ctor_get_uint8(v___x_2184_, 0);
v_ctxApprox_2186_ = lean_ctor_get_uint8(v___x_2184_, 1);
v_quasiPatternApprox_2187_ = lean_ctor_get_uint8(v___x_2184_, 2);
v_constApprox_2188_ = lean_ctor_get_uint8(v___x_2184_, 3);
v_unificationHints_2189_ = lean_ctor_get_uint8(v___x_2184_, 5);
v_proofIrrelevance_2190_ = lean_ctor_get_uint8(v___x_2184_, 6);
v_assignSyntheticOpaque_2191_ = lean_ctor_get_uint8(v___x_2184_, 7);
v_offsetCnstrs_2192_ = lean_ctor_get_uint8(v___x_2184_, 8);
v_transparency_2193_ = lean_ctor_get_uint8(v___x_2184_, 9);
v_etaStruct_2194_ = lean_ctor_get_uint8(v___x_2184_, 10);
v_univApprox_2195_ = lean_ctor_get_uint8(v___x_2184_, 11);
v_iota_2196_ = lean_ctor_get_uint8(v___x_2184_, 12);
v_beta_2197_ = lean_ctor_get_uint8(v___x_2184_, 13);
v_proj_2198_ = lean_ctor_get_uint8(v___x_2184_, 14);
v_zeta_2199_ = lean_ctor_get_uint8(v___x_2184_, 15);
v_zetaDelta_2200_ = lean_ctor_get_uint8(v___x_2184_, 16);
v_zetaUnused_2201_ = lean_ctor_get_uint8(v___x_2184_, 17);
v_zetaHave_2202_ = lean_ctor_get_uint8(v___x_2184_, 18);
v_canUnfoldPredicateConfig_2203_ = lean_ctor_get_uint8(v___x_2184_, 19);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2205_ = v___x_2184_;
v_isShared_2206_ = v_isSharedCheck_2224_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v___x_2184_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2224_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
uint8_t v_trackZetaDelta_2207_; lean_object* v_zetaDeltaSet_2208_; lean_object* v_lctx_2209_; lean_object* v_localInstances_2210_; lean_object* v_defEqCtx_x3f_2211_; lean_object* v_synthPendingDepth_2212_; lean_object* v_customCanUnfoldPredicate_x3f_2213_; uint8_t v_univApprox_2214_; uint8_t v_inTypeClassResolution_2215_; uint8_t v_cacheInferType_2216_; lean_object* v___x_2218_; 
v_trackZetaDelta_2207_ = lean_ctor_get_uint8(v___y_2179_, sizeof(void*)*7);
v_zetaDeltaSet_2208_ = lean_ctor_get(v___y_2179_, 1);
v_lctx_2209_ = lean_ctor_get(v___y_2179_, 2);
v_localInstances_2210_ = lean_ctor_get(v___y_2179_, 3);
v_defEqCtx_x3f_2211_ = lean_ctor_get(v___y_2179_, 4);
v_synthPendingDepth_2212_ = lean_ctor_get(v___y_2179_, 5);
v_customCanUnfoldPredicate_x3f_2213_ = lean_ctor_get(v___y_2179_, 6);
v_univApprox_2214_ = lean_ctor_get_uint8(v___y_2179_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2215_ = lean_ctor_get_uint8(v___y_2179_, sizeof(void*)*7 + 2);
v_cacheInferType_2216_ = lean_ctor_get_uint8(v___y_2179_, sizeof(void*)*7 + 3);
if (v_isShared_2206_ == 0)
{
v___x_2218_ = v___x_2205_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 0, v_foApprox_2185_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 1, v_ctxApprox_2186_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 2, v_quasiPatternApprox_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 3, v_constApprox_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 5, v_unificationHints_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 6, v_proofIrrelevance_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 7, v_assignSyntheticOpaque_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 8, v_offsetCnstrs_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 9, v_transparency_2193_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 10, v_etaStruct_2194_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 11, v_univApprox_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 12, v_iota_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 13, v_beta_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 14, v_proj_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 15, v_zeta_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 16, v_zetaDelta_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 17, v_zetaUnused_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 18, v_zetaHave_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, 19, v_canUnfoldPredicateConfig_2203_);
v___x_2218_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
uint64_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_ctor_set_uint8(v___x_2218_, 4, v___x_2173_);
v___x_2219_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2218_);
v___x_2220_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set_uint64(v___x_2220_, sizeof(void*)*1, v___x_2219_);
lean_inc(v_customCanUnfoldPredicate_x3f_2213_);
lean_inc(v_synthPendingDepth_2212_);
lean_inc(v_defEqCtx_x3f_2211_);
lean_inc_ref(v_localInstances_2210_);
lean_inc_ref(v_lctx_2209_);
lean_inc(v_zetaDeltaSet_2208_);
v___x_2221_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v_zetaDeltaSet_2208_);
lean_ctor_set(v___x_2221_, 2, v_lctx_2209_);
lean_ctor_set(v___x_2221_, 3, v_localInstances_2210_);
lean_ctor_set(v___x_2221_, 4, v_defEqCtx_x3f_2211_);
lean_ctor_set(v___x_2221_, 5, v_synthPendingDepth_2212_);
lean_ctor_set(v___x_2221_, 6, v_customCanUnfoldPredicate_x3f_2213_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*7, v_trackZetaDelta_2207_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*7 + 1, v_univApprox_2214_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2215_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*7 + 3, v_cacheInferType_2216_);
v___x_2222_ = l_Lean_Meta_isExprDefEqGuarded(v_val_2174_, v___x_2175_, v___x_2221_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec_ref_known(v___x_2221_, 7);
return v___x_2222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0___boxed(lean_object* v___x_2225_, lean_object* v_val_2226_, lean_object* v___x_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
uint8_t v___x_14785__boxed_2236_; lean_object* v_res_2237_; 
v___x_14785__boxed_2236_ = lean_unbox(v___x_2225_);
v_res_2237_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0(v___x_14785__boxed_2236_, v_val_2226_, v___x_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
return v_res_2237_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2238_; double v___x_2239_; 
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_float_of_nat(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(lean_object* v_cls_2243_, lean_object* v_msg_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_ref_2250_; lean_object* v___x_2251_; lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2297_; 
v_ref_2250_ = lean_ctor_get(v___y_2247_, 2);
v___x_2251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2297_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2297_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v_traceState_2257_; lean_object* v_env_2258_; lean_object* v_nextMacroScope_2259_; lean_object* v_ngen_2260_; lean_object* v_auxDeclNGen_2261_; lean_object* v_cache_2262_; lean_object* v_recordedDeps_2263_; lean_object* v_messages_2264_; lean_object* v_infoState_2265_; lean_object* v_snapshotTasks_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2296_; 
v___x_2256_ = lean_st_ref_take(v___y_2248_);
v_traceState_2257_ = lean_ctor_get(v___x_2256_, 4);
v_env_2258_ = lean_ctor_get(v___x_2256_, 0);
v_nextMacroScope_2259_ = lean_ctor_get(v___x_2256_, 1);
v_ngen_2260_ = lean_ctor_get(v___x_2256_, 2);
v_auxDeclNGen_2261_ = lean_ctor_get(v___x_2256_, 3);
v_cache_2262_ = lean_ctor_get(v___x_2256_, 5);
v_recordedDeps_2263_ = lean_ctor_get(v___x_2256_, 6);
v_messages_2264_ = lean_ctor_get(v___x_2256_, 7);
v_infoState_2265_ = lean_ctor_get(v___x_2256_, 8);
v_snapshotTasks_2266_ = lean_ctor_get(v___x_2256_, 9);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2268_ = v___x_2256_;
v_isShared_2269_ = v_isSharedCheck_2296_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_snapshotTasks_2266_);
lean_inc(v_infoState_2265_);
lean_inc(v_messages_2264_);
lean_inc(v_recordedDeps_2263_);
lean_inc(v_cache_2262_);
lean_inc(v_traceState_2257_);
lean_inc(v_auxDeclNGen_2261_);
lean_inc(v_ngen_2260_);
lean_inc(v_nextMacroScope_2259_);
lean_inc(v_env_2258_);
lean_dec(v___x_2256_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2296_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint64_t v_tid_2270_; lean_object* v_traces_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2295_; 
v_tid_2270_ = lean_ctor_get_uint64(v_traceState_2257_, sizeof(void*)*1);
v_traces_2271_ = lean_ctor_get(v_traceState_2257_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_traceState_2257_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2273_ = v_traceState_2257_;
v_isShared_2274_ = v_isSharedCheck_2295_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_traces_2271_);
lean_dec(v_traceState_2257_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2295_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; double v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = lean_box(0);
v___x_2277_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0);
v___x_2278_ = 0;
v___x_2279_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1));
v___x_2280_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2280_, 0, v_cls_2243_);
lean_ctor_set(v___x_2280_, 1, v___x_2276_);
lean_ctor_set(v___x_2280_, 2, v___x_2279_);
lean_ctor_set_float(v___x_2280_, sizeof(void*)*3, v___x_2277_);
lean_ctor_set_float(v___x_2280_, sizeof(void*)*3 + 8, v___x_2277_);
lean_ctor_set_uint8(v___x_2280_, sizeof(void*)*3 + 16, v___x_2278_);
v___x_2281_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2));
v___x_2282_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v_a_2252_);
lean_ctor_set(v___x_2282_, 2, v___x_2281_);
lean_inc(v_ref_2250_);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v_ref_2250_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = l_Lean_PersistentArray_push___redArg(v_traces_2271_, v___x_2283_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2284_);
v___x_2286_ = v___x_2273_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2284_);
lean_ctor_set_uint64(v_reuseFailAlloc_2294_, sizeof(void*)*1, v_tid_2270_);
v___x_2286_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v___x_2286_);
v___x_2288_ = v___x_2268_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_env_2258_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_nextMacroScope_2259_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_ngen_2260_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_auxDeclNGen_2261_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2293_, 5, v_cache_2262_);
lean_ctor_set(v_reuseFailAlloc_2293_, 6, v_recordedDeps_2263_);
lean_ctor_set(v_reuseFailAlloc_2293_, 7, v_messages_2264_);
lean_ctor_set(v_reuseFailAlloc_2293_, 8, v_infoState_2265_);
lean_ctor_set(v_reuseFailAlloc_2293_, 9, v_snapshotTasks_2266_);
v___x_2288_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2289_ = lean_st_ref_put(v___y_2248_, v___x_2288_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2275_);
v___x_2291_ = v___x_2254_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2275_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___boxed(lean_object* v_cls_2298_, lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v_cls_2298_, v_msg_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2305_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_2313_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2));
v___x_2314_ = l_Lean_Name_append(v___x_2313_, v___x_2312_);
return v___x_2314_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__4));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__6));
v___x_2320_ = l_Lean_stringToMessageData(v___x_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(lean_object* v_t_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___x_2330_; uint8_t v_hasUncomparable_2331_; 
v___x_2330_ = lean_st_ref_get(v_a_2322_);
v_hasUncomparable_2331_ = lean_ctor_get_uint8(v___x_2330_, sizeof(void*)*1);
lean_dec(v___x_2330_);
if (v_hasUncomparable_2331_ == 0)
{
switch(lean_obj_tag(v_t_2321_))
{
case 0:
{
lean_object* v_val_2332_; uint8_t v___x_2333_; lean_object* v___y_2335_; lean_object* v___x_2349_; 
v_val_2332_ = lean_ctor_get(v_t_2321_, 2);
lean_inc_ref(v_val_2332_);
lean_dec_ref_known(v_t_2321_, 3);
v___x_2333_ = 1;
lean_inc(v_a_2328_);
lean_inc_ref(v_a_2327_);
lean_inc(v_a_2326_);
lean_inc_ref(v_a_2325_);
v___x_2349_ = lean_infer_type(v_val_2332_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2486_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2351_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_a_2350_, v_a_2326_);
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2486_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2486_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = l_Lean_Expr_cleanupAnnotations(v_a_2352_);
v___x_2357_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; lean_object* v_max_x3f_2359_; 
v___x_2358_ = lean_st_ref_get(v_a_2322_);
v_max_x3f_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_max_x3f_2359_);
lean_dec(v___x_2358_);
if (lean_obj_tag(v_max_x3f_2359_) == 0)
{
lean_object* v___x_2360_; uint8_t v_hasUncomparable_2361_; uint8_t v_hasUnknown_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2375_; 
v___x_2360_ = lean_st_ref_take(v_a_2322_);
v_hasUncomparable_2361_ = lean_ctor_get_uint8(v___x_2360_, sizeof(void*)*1);
v_hasUnknown_2362_ = lean_ctor_get_uint8(v___x_2360_, sizeof(void*)*1 + 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v___x_2360_, 0);
lean_dec(v_unused_2376_);
v___x_2364_ = v___x_2360_;
v_isShared_2365_ = v_isSharedCheck_2375_;
goto v_resetjp_2363_;
}
else
{
lean_dec(v___x_2360_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2375_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2356_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2367_);
v___x_2369_ = v___x_2364_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*1, v_hasUncomparable_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*1 + 1, v_hasUnknown_2362_);
v___x_2369_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2370_ = lean_st_ref_put(v_a_2322_, v___x_2369_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2366_);
v___x_2372_ = v___x_2354_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2366_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_val_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2470_; 
lean_del_object(v___x_2354_);
v_val_2377_ = lean_ctor_get(v_max_x3f_2359_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_max_x3f_2359_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2379_ = v_max_x3f_2359_;
v_isShared_2380_ = v_isSharedCheck_2470_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_val_2377_);
lean_dec(v_max_x3f_2359_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2470_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; 
v___x_2381_ = lean_box(v___x_2333_);
lean_inc_ref(v___x_2356_);
lean_inc(v_val_2377_);
v___f_2382_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2382_, 0, v___x_2381_);
lean_closure_set(v___f_2382_, 1, v_val_2377_);
lean_closure_set(v___f_2382_, 2, v___x_2356_);
v___x_2383_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v___f_2382_, v___x_2357_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2461_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2461_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2461_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
uint8_t v___x_2388_; 
v___x_2388_ = lean_unbox(v_a_2384_);
lean_dec(v_a_2384_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; 
lean_del_object(v___x_2386_);
lean_inc(v_val_2377_);
lean_inc_ref(v___x_2356_);
v___x_2389_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v___x_2356_, v_val_2377_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2448_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2448_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2448_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_unbox(v_a_2390_);
lean_dec(v_a_2390_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
lean_del_object(v___x_2392_);
lean_inc_ref(v___x_2356_);
lean_inc(v_val_2377_);
v___x_2395_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v_val_2377_, v___x_2356_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2435_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2435_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2435_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
uint8_t v___x_2400_; 
v___x_2400_ = lean_unbox(v_a_2396_);
lean_dec(v_a_2396_);
if (v___x_2400_ == 0)
{
lean_object* v_toCold_2401_; lean_object* v_options_2402_; uint8_t v_hasTrace_2403_; 
lean_del_object(v___x_2398_);
lean_del_object(v___x_2379_);
v_toCold_2401_ = lean_ctor_get(v_a_2327_, 0);
v_options_2402_ = lean_ctor_get(v_toCold_2401_, 2);
v_hasTrace_2403_ = lean_ctor_get_uint8(v_options_2402_, sizeof(void*)*1);
if (v_hasTrace_2403_ == 0)
{
lean_dec(v_val_2377_);
lean_dec_ref(v___x_2356_);
v___y_2335_ = v_a_2322_;
goto v___jp_2334_;
}
else
{
lean_object* v_inheritedTraceOptions_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v_inheritedTraceOptions_2404_ = lean_ctor_get(v_toCold_2401_, 11);
v___x_2405_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_2406_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_2407_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2404_, v_options_2402_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_dec(v_val_2377_);
lean_dec_ref(v___x_2356_);
v___y_2335_ = v_a_2322_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2408_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5);
v___x_2409_ = l_Lean_MessageData_ofExpr(v_val_2377_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l_Lean_MessageData_ofExpr(v___x_2356_);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v___x_2405_, v___x_2414_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_dec_ref_known(v___x_2415_, 1);
v___y_2335_ = v_a_2322_;
goto v___jp_2334_;
}
else
{
return v___x_2415_;
}
}
}
}
else
{
lean_object* v___x_2416_; uint8_t v_hasUncomparable_2417_; uint8_t v_hasUnknown_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_val_2377_);
v___x_2416_ = lean_st_ref_take(v_a_2322_);
v_hasUncomparable_2417_ = lean_ctor_get_uint8(v___x_2416_, sizeof(void*)*1);
v_hasUnknown_2418_ = lean_ctor_get_uint8(v___x_2416_, sizeof(void*)*1 + 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; 
v_unused_2434_ = lean_ctor_get(v___x_2416_, 0);
lean_dec(v_unused_2434_);
v___x_2420_ = v___x_2416_;
v_isShared_2421_ = v_isSharedCheck_2433_;
goto v_resetjp_2419_;
}
else
{
lean_dec(v___x_2416_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2433_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = lean_box(0);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2356_);
v___x_2424_ = v___x_2379_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2356_);
v___x_2424_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2424_);
v___x_2426_ = v___x_2420_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*1, v_hasUncomparable_2417_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*1 + 1, v_hasUnknown_2418_);
v___x_2426_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_st_ref_put(v_a_2322_, v___x_2426_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2422_);
v___x_2429_ = v___x_2398_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2422_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_del_object(v___x_2379_);
lean_dec(v_val_2377_);
lean_dec_ref(v___x_2356_);
v_a_2436_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2395_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2395_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_del_object(v___x_2379_);
lean_dec(v_val_2377_);
lean_dec_ref(v___x_2356_);
v___x_2444_ = lean_box(0);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2444_);
v___x_2446_ = v___x_2392_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_del_object(v___x_2379_);
lean_dec(v_val_2377_);
lean_dec_ref(v___x_2356_);
v_a_2449_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2389_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2389_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
lean_del_object(v___x_2379_);
lean_dec(v_val_2377_);
lean_dec_ref(v___x_2356_);
v___x_2457_ = lean_box(0);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2457_);
v___x_2459_ = v___x_2386_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_del_object(v___x_2379_);
lean_dec(v_val_2377_);
lean_dec_ref(v___x_2356_);
v_a_2462_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2383_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2383_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
}
else
{
lean_object* v___x_2471_; lean_object* v_max_x3f_2472_; uint8_t v_hasUncomparable_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v___x_2356_);
v___x_2471_ = lean_st_ref_take(v_a_2322_);
v_max_x3f_2472_ = lean_ctor_get(v___x_2471_, 0);
v_hasUncomparable_2473_ = lean_ctor_get_uint8(v___x_2471_, sizeof(void*)*1);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2475_ = v___x_2471_;
v_isShared_2476_ = v_isSharedCheck_2485_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_max_x3f_2472_);
lean_dec(v___x_2471_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2485_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2477_ = lean_box(0);
if (v_isShared_2476_ == 0)
{
v___x_2479_ = v___x_2475_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_max_x3f_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, sizeof(void*)*1, v_hasUncomparable_2473_);
v___x_2479_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*1 + 1, v___x_2333_);
v___x_2480_ = lean_st_ref_put(v_a_2322_, v___x_2479_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2477_);
v___x_2482_ = v___x_2354_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
v_a_2487_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2349_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2349_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
v___jp_2334_:
{
lean_object* v___x_2336_; lean_object* v_max_x3f_2337_; uint8_t v_hasUnknown_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2348_; 
v___x_2336_ = lean_st_ref_take(v___y_2335_);
v_max_x3f_2337_ = lean_ctor_get(v___x_2336_, 0);
v_hasUnknown_2338_ = lean_ctor_get_uint8(v___x_2336_, sizeof(void*)*1 + 1);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2340_ = v___x_2336_;
v_isShared_2341_ = v_isSharedCheck_2348_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_max_x3f_2337_);
lean_dec(v___x_2336_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2348_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2342_ = lean_box(0);
if (v_isShared_2341_ == 0)
{
v___x_2344_ = v___x_2340_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_max_x3f_2337_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*1 + 1, v_hasUnknown_2338_);
v___x_2344_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*1, v___x_2333_);
v___x_2345_ = lean_st_ref_put(v___y_2335_, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2342_);
return v___x_2346_;
}
}
}
}
case 1:
{
uint8_t v_kind_2495_; 
v_kind_2495_ = lean_ctor_get_uint8(v_t_2321_, sizeof(void*)*4);
switch(v_kind_2495_)
{
case 2:
{
lean_object* v_rhs_2496_; 
v_rhs_2496_ = lean_ctor_get(v_t_2321_, 3);
lean_inc_ref(v_rhs_2496_);
lean_dec_ref_known(v_t_2321_, 4);
v_t_2321_ = v_rhs_2496_;
goto _start;
}
case 3:
{
lean_object* v_lhs_2498_; 
v_lhs_2498_ = lean_ctor_get(v_t_2321_, 2);
lean_inc_ref(v_lhs_2498_);
lean_dec_ref_known(v_t_2321_, 4);
v_t_2321_ = v_lhs_2498_;
goto _start;
}
default: 
{
lean_object* v_lhs_2500_; lean_object* v_rhs_2501_; lean_object* v___x_2502_; 
v_lhs_2500_ = lean_ctor_get(v_t_2321_, 2);
lean_inc_ref(v_lhs_2500_);
v_rhs_2501_ = lean_ctor_get(v_t_2321_, 3);
lean_inc_ref(v_rhs_2501_);
lean_dec_ref_known(v_t_2321_, 4);
v___x_2502_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_lhs_2500_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_dec_ref_known(v___x_2502_, 1);
v_t_2321_ = v_rhs_2501_;
goto _start;
}
else
{
lean_dec_ref(v_rhs_2501_);
return v___x_2502_;
}
}
}
}
case 2:
{
lean_object* v_arg_2504_; 
v_arg_2504_ = lean_ctor_get(v_t_2321_, 2);
lean_inc_ref(v_arg_2504_);
lean_dec_ref_known(v_t_2321_, 3);
v_t_2321_ = v_arg_2504_;
goto _start;
}
default: 
{
lean_object* v_nested_2506_; 
v_nested_2506_ = lean_ctor_get(v_t_2321_, 3);
lean_inc_ref(v_nested_2506_);
lean_dec_ref_known(v_t_2321_, 4);
v_t_2321_ = v_nested_2506_;
goto _start;
}
}
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec_ref(v_t_2321_);
v___x_2508_ = lean_box(0);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___boxed(lean_object* v_t_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_t_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2(lean_object* v_cls_2520_, lean_object* v_msg_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v_cls_2520_, v_msg_2521_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___boxed(lean_object* v_cls_2531_, lean_object* v_msg_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2(v_cls_2531_, v_msg_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(lean_object* v_e_2542_, lean_object* v___y_2543_){
_start:
{
uint8_t v___x_2545_; 
v___x_2545_ = l_Lean_Expr_hasMVar(v_e_2542_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v_e_2542_);
return v___x_2546_;
}
else
{
lean_object* v___x_2547_; lean_object* v_mctx_2548_; lean_object* v___x_2549_; lean_object* v_fst_2550_; lean_object* v_snd_2551_; lean_object* v___x_2552_; lean_object* v_cache_2553_; lean_object* v_zetaDeltaFVarIds_2554_; lean_object* v_postponed_2555_; lean_object* v_diag_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2565_; 
v___x_2547_ = lean_st_ref_get(v___y_2543_);
v_mctx_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc_ref(v_mctx_2548_);
lean_dec(v___x_2547_);
v___x_2549_ = l_Lean_instantiateMVarsCore(v_mctx_2548_, v_e_2542_);
v_fst_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_fst_2550_);
v_snd_2551_ = lean_ctor_get(v___x_2549_, 1);
lean_inc(v_snd_2551_);
lean_dec_ref(v___x_2549_);
v___x_2552_ = lean_st_ref_take(v___y_2543_);
v_cache_2553_ = lean_ctor_get(v___x_2552_, 1);
v_zetaDeltaFVarIds_2554_ = lean_ctor_get(v___x_2552_, 2);
v_postponed_2555_ = lean_ctor_get(v___x_2552_, 3);
v_diag_2556_ = lean_ctor_get(v___x_2552_, 4);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2552_, 0);
lean_dec(v_unused_2566_);
v___x_2558_ = v___x_2552_;
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_diag_2556_);
lean_inc(v_postponed_2555_);
lean_inc(v_zetaDeltaFVarIds_2554_);
lean_inc(v_cache_2553_);
lean_dec(v___x_2552_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v_snd_2551_);
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_snd_2551_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_cache_2553_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_zetaDeltaFVarIds_2554_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v_postponed_2555_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v_diag_2556_);
v___x_2561_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_st_ref_put(v___y_2543_, v___x_2561_);
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_fst_2550_);
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg___boxed(lean_object* v_e_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(v_e_2567_, v___y_2568_);
lean_dec(v___y_2568_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0(lean_object* v_e_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(v_e_2571_, v___y_2575_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___boxed(lean_object* v_e_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0(v_e_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(lean_object* v_t_2589_, lean_object* v_expectedType_x3f_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v_max_x3f_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; 
if (lean_obj_tag(v_expectedType_x3f_2590_) == 0)
{
v_max_x3f_2599_ = v_expectedType_x3f_2590_;
v___y_2600_ = v_a_2591_;
v___y_2601_ = v_a_2592_;
v___y_2602_ = v_a_2593_;
v___y_2603_ = v_a_2594_;
v___y_2604_ = v_a_2595_;
v___y_2605_ = v_a_2596_;
goto v___jp_2598_;
}
else
{
lean_object* v_val_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2640_; 
v_val_2628_ = lean_ctor_get(v_expectedType_x3f_2590_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_expectedType_x3f_2590_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2630_ = v_expectedType_x3f_2590_;
v_isShared_2631_ = v_isSharedCheck_2640_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_val_2628_);
lean_dec(v_expectedType_x3f_2590_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2640_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v_a_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2632_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(v_val_2628_, v_a_2594_);
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref(v___x_2632_);
v___x_2634_ = l_Lean_Expr_cleanupAnnotations(v_a_2633_);
v___x_2635_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_2634_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2637_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2634_);
v___x_2637_ = v___x_2630_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2634_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
v_max_x3f_2599_ = v___x_2637_;
v___y_2600_ = v_a_2591_;
v___y_2601_ = v_a_2592_;
v___y_2602_ = v_a_2593_;
v___y_2603_ = v_a_2594_;
v___y_2604_ = v_a_2595_;
v___y_2605_ = v_a_2596_;
goto v___jp_2598_;
}
}
else
{
lean_object* v___x_2639_; 
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2630_);
v___x_2639_ = lean_box(0);
v_max_x3f_2599_ = v___x_2639_;
v___y_2600_ = v_a_2591_;
v___y_2601_ = v_a_2592_;
v___y_2602_ = v_a_2593_;
v___y_2603_ = v_a_2594_;
v___y_2604_ = v_a_2595_;
v___y_2605_ = v_a_2596_;
goto v___jp_2598_;
}
}
}
v___jp_2598_:
{
uint8_t v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2606_ = 0;
v___x_2607_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2607_, 0, v_max_x3f_2599_);
lean_ctor_set_uint8(v___x_2607_, sizeof(void*)*1, v___x_2606_);
lean_ctor_set_uint8(v___x_2607_, sizeof(void*)*1 + 1, v___x_2606_);
v___x_2608_ = lean_st_mk_ref(v___x_2607_);
v___x_2609_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_t_2589_, v___x_2608_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2618_; 
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v___x_2609_, 0);
lean_dec(v_unused_2619_);
v___x_2611_ = v___x_2609_;
v_isShared_2612_ = v_isSharedCheck_2618_;
goto v_resetjp_2610_;
}
else
{
lean_dec(v___x_2609_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2618_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
v___x_2613_ = lean_st_ref_get(v___x_2608_);
v___x_2614_ = lean_st_ref_get(v___x_2608_);
lean_dec(v___x_2608_);
lean_dec(v___x_2614_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2613_);
v___x_2616_ = v___x_2611_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2613_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v___x_2608_);
v_a_2620_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2609_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2609_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze___boxed(lean_object* v_t_2641_, lean_object* v_expectedType_x3f_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v_t_2641_, v_expectedType_x3f_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(uint8_t v_lazy_2653_, lean_object* v_f_2654_, lean_object* v_lhs_2655_, lean_object* v_rhs_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_rhs_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; 
if (v_lazy_2653_ == 0)
{
v_rhs_2665_ = v_rhs_2656_;
v___y_2666_ = v_a_2657_;
v___y_2667_ = v_a_2658_;
v___y_2668_ = v_a_2659_;
v___y_2669_ = v_a_2660_;
v___y_2670_ = v_a_2661_;
v___y_2671_ = v_a_2662_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_Meta_mkFunUnit___redArg(v_rhs_2656_, v_a_2661_, v_a_2662_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v_rhs_2665_ = v_a_2683_;
v___y_2666_ = v_a_2657_;
v___y_2667_ = v_a_2658_;
v___y_2668_ = v_a_2659_;
v___y_2669_ = v_a_2660_;
v___y_2670_ = v_a_2661_;
v___y_2671_ = v_a_2662_;
goto v___jp_2664_;
}
else
{
lean_dec_ref(v_lhs_2655_);
lean_dec_ref(v_f_2654_);
return v___x_2682_;
}
}
v___jp_2664_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; lean_object* v___x_2681_; 
v___x_2672_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
v___x_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_lhs_2655_);
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_rhs_2665_);
v___x_2675_ = lean_unsigned_to_nat(2u);
v___x_2676_ = lean_mk_empty_array_with_capacity(v___x_2675_);
v___x_2677_ = lean_array_push(v___x_2676_, v___x_2673_);
v___x_2678_ = lean_array_push(v___x_2677_, v___x_2674_);
v___x_2679_ = lean_box(0);
v___x_2680_ = 0;
v___x_2681_ = l_Lean_Elab_Term_elabAppArgs(v_f_2654_, v___x_2672_, v___x_2678_, v___x_2679_, v___x_2680_, v___x_2680_, v___x_2680_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___boxed(lean_object* v_lazy_2684_, lean_object* v_f_2685_, lean_object* v_lhs_2686_, lean_object* v_rhs_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
uint8_t v_lazy_boxed_2695_; lean_object* v_res_2696_; 
v_lazy_boxed_2695_ = lean_unbox(v_lazy_2684_);
v_res_2696_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v_lazy_boxed_2695_, v_f_2685_, v_lhs_2686_, v_rhs_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(lean_object* v_f_2697_, lean_object* v_arg_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; 
v___x_2706_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v_arg_2698_);
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2709_ = lean_mk_empty_array_with_capacity(v___x_2708_);
v___x_2710_ = lean_array_push(v___x_2709_, v___x_2707_);
v___x_2711_ = lean_box(0);
v___x_2712_ = 0;
v___x_2713_ = l_Lean_Elab_Term_elabAppArgs(v_f_2697_, v___x_2706_, v___x_2710_, v___x_2711_, v___x_2712_, v___x_2712_, v___x_2712_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp___boxed(lean_object* v_f_2714_, lean_object* v_arg_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(v_f_2714_, v_arg_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___y_2724_, lean_object* v_mkInfoTree_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v_a_2731_, lean_object* v_a_x3f_2732_){
_start:
{
lean_object* v___x_2734_; lean_object* v_infoState_2735_; lean_object* v_trees_2736_; lean_object* v___x_2737_; 
v___x_2734_ = lean_st_ref_get(v___y_2724_);
v_infoState_2735_ = lean_ctor_get(v___x_2734_, 8);
lean_inc_ref(v_infoState_2735_);
lean_dec(v___x_2734_);
v_trees_2736_ = lean_ctor_get(v_infoState_2735_, 2);
lean_inc_ref(v_trees_2736_);
lean_dec_ref(v_infoState_2735_);
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2730_);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
v___x_2737_ = lean_apply_8(v_mkInfoTree_2725_, v_trees_2736_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2724_, lean_box(0));
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2777_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2777_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2777_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v_infoState_2743_; lean_object* v_env_2744_; lean_object* v_nextMacroScope_2745_; lean_object* v_ngen_2746_; lean_object* v_auxDeclNGen_2747_; lean_object* v_traceState_2748_; lean_object* v_cache_2749_; lean_object* v_recordedDeps_2750_; lean_object* v_messages_2751_; lean_object* v_snapshotTasks_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2776_; 
v___x_2742_ = lean_st_ref_take(v___y_2724_);
v_infoState_2743_ = lean_ctor_get(v___x_2742_, 8);
v_env_2744_ = lean_ctor_get(v___x_2742_, 0);
v_nextMacroScope_2745_ = lean_ctor_get(v___x_2742_, 1);
v_ngen_2746_ = lean_ctor_get(v___x_2742_, 2);
v_auxDeclNGen_2747_ = lean_ctor_get(v___x_2742_, 3);
v_traceState_2748_ = lean_ctor_get(v___x_2742_, 4);
v_cache_2749_ = lean_ctor_get(v___x_2742_, 5);
v_recordedDeps_2750_ = lean_ctor_get(v___x_2742_, 6);
v_messages_2751_ = lean_ctor_get(v___x_2742_, 7);
v_snapshotTasks_2752_ = lean_ctor_get(v___x_2742_, 9);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2754_ = v___x_2742_;
v_isShared_2755_ = v_isSharedCheck_2776_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_snapshotTasks_2752_);
lean_inc(v_infoState_2743_);
lean_inc(v_messages_2751_);
lean_inc(v_recordedDeps_2750_);
lean_inc(v_cache_2749_);
lean_inc(v_traceState_2748_);
lean_inc(v_auxDeclNGen_2747_);
lean_inc(v_ngen_2746_);
lean_inc(v_nextMacroScope_2745_);
lean_inc(v_env_2744_);
lean_dec(v___x_2742_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2776_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
uint8_t v_enabled_2756_; lean_object* v_assignment_2757_; lean_object* v_lazyAssignment_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2774_; 
v_enabled_2756_ = lean_ctor_get_uint8(v_infoState_2743_, sizeof(void*)*3);
v_assignment_2757_ = lean_ctor_get(v_infoState_2743_, 0);
v_lazyAssignment_2758_ = lean_ctor_get(v_infoState_2743_, 1);
v_isSharedCheck_2774_ = !lean_is_exclusive(v_infoState_2743_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; 
v_unused_2775_ = lean_ctor_get(v_infoState_2743_, 2);
lean_dec(v_unused_2775_);
v___x_2760_ = v_infoState_2743_;
v_isShared_2761_ = v_isSharedCheck_2774_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_lazyAssignment_2758_);
lean_inc(v_assignment_2757_);
lean_dec(v_infoState_2743_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2774_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2762_ = lean_box(0);
v___x_2763_ = l_Lean_PersistentArray_push___redArg(v_a_2731_, v_a_2738_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 2, v___x_2763_);
v___x_2765_ = v___x_2760_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_assignment_2757_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_lazyAssignment_2758_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v___x_2763_);
lean_ctor_set_uint8(v_reuseFailAlloc_2773_, sizeof(void*)*3, v_enabled_2756_);
v___x_2765_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2767_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 8, v___x_2765_);
v___x_2767_ = v___x_2754_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_env_2744_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_nextMacroScope_2745_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_ngen_2746_);
lean_ctor_set(v_reuseFailAlloc_2772_, 3, v_auxDeclNGen_2747_);
lean_ctor_set(v_reuseFailAlloc_2772_, 4, v_traceState_2748_);
lean_ctor_set(v_reuseFailAlloc_2772_, 5, v_cache_2749_);
lean_ctor_set(v_reuseFailAlloc_2772_, 6, v_recordedDeps_2750_);
lean_ctor_set(v_reuseFailAlloc_2772_, 7, v_messages_2751_);
lean_ctor_set(v_reuseFailAlloc_2772_, 8, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2772_, 9, v_snapshotTasks_2752_);
v___x_2767_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2768_ = lean_st_ref_put(v___y_2724_, v___x_2767_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v___x_2762_);
v___x_2770_ = v___x_2740_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2762_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec_ref(v_a_2731_);
v_a_2778_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2737_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2737_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_2786_, lean_object* v_mkInfoTree_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v_a_2793_, lean_object* v_a_x3f_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_2786_, v_mkInfoTree_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v_a_2793_, v_a_x3f_2794_);
lean_dec(v_a_x3f_2794_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2786_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2797_, lean_object* v_mkInfoTree_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___x_2806_; lean_object* v_infoState_2807_; uint8_t v_enabled_2808_; 
v___x_2806_ = lean_st_ref_get(v___y_2804_);
v_infoState_2807_ = lean_ctor_get(v___x_2806_, 8);
lean_inc_ref(v_infoState_2807_);
lean_dec(v___x_2806_);
v_enabled_2808_ = lean_ctor_get_uint8(v_infoState_2807_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2807_);
if (v_enabled_2808_ == 0)
{
lean_object* v___x_2809_; 
lean_dec_ref(v_mkInfoTree_2798_);
lean_inc(v___y_2804_);
lean_inc_ref(v___y_2803_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2809_ = lean_apply_7(v_x_2797_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, lean_box(0));
return v___x_2809_;
}
else
{
lean_object* v___x_2810_; lean_object* v_a_2811_; lean_object* v_r_2812_; 
v___x_2810_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v___y_2804_);
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2810_);
lean_inc(v___y_2804_);
lean_inc_ref(v___y_2803_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v_r_2812_ = lean_apply_7(v_x_2797_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, lean_box(0));
if (lean_obj_tag(v_r_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2837_; 
v_a_2813_ = lean_ctor_get(v_r_2812_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_r_2812_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2815_ = v_r_2812_;
v_isShared_2816_ = v_isSharedCheck_2837_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v_r_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2837_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
lean_inc(v_a_2813_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 1);
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_2804_, v_mkInfoTree_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v_a_2811_, v___x_2818_);
lean_dec_ref(v___x_2818_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v___x_2819_, 0);
lean_dec(v_unused_2827_);
v___x_2821_ = v___x_2819_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v___x_2819_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v_a_2813_);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2813_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_a_2813_);
v_a_2828_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2819_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2819_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v_a_2838_ = lean_ctor_get(v_r_2812_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v_r_2812_, 1);
v___x_2839_ = lean_box(0);
v___x_2840_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_2804_, v_mkInfoTree_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v_a_2811_, v___x_2839_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v___x_2840_, 0);
lean_dec(v_unused_2848_);
v___x_2842_ = v___x_2840_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_dec(v___x_2840_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 1);
lean_ctor_set(v___x_2842_, 0, v_a_2838_);
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2838_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v_a_2838_);
v_a_2849_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2840_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2840_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2857_, lean_object* v_mkInfoTree_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_2857_, v_mkInfoTree_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0(lean_object* v_stx_2867_, lean_object* v_output_2868_, lean_object* v_trees_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_lctx_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_lctx_2877_ = lean_ctor_get(v___y_2872_, 2);
lean_inc_ref(v_lctx_2877_);
v___x_2878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2878_, 0, v_lctx_2877_);
lean_ctor_set(v___x_2878_, 1, v_stx_2867_);
lean_ctor_set(v___x_2878_, 2, v_output_2868_);
v___x_2879_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
lean_ctor_set(v___x_2880_, 1, v_trees_2869_);
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_stx_2882_, lean_object* v_output_2883_, lean_object* v_trees_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0(v_stx_2882_, v_output_2883_, v_trees_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(lean_object* v_stx_2893_, lean_object* v_output_2894_, lean_object* v_x_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v___f_2903_; lean_object* v___x_2904_; 
v___f_2903_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2903_, 0, v_stx_2893_);
lean_closure_set(v___f_2903_, 1, v_output_2894_);
v___x_2904_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_2895_, v___f_2903_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___boxed(lean_object* v_stx_2905_, lean_object* v_output_2906_, lean_object* v_x_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_stx_2905_, v_output_2906_, v_x_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(lean_object* v_beforeStx_2916_, lean_object* v_afterStx_2917_, lean_object* v_x_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_inc(v_afterStx_2917_);
lean_inc(v_beforeStx_2916_);
v___x_2926_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___boxed), 11, 4);
lean_closure_set(v___x_2926_, 0, lean_box(0));
lean_closure_set(v___x_2926_, 1, v_beforeStx_2916_);
lean_closure_set(v___x_2926_, 2, v_afterStx_2917_);
lean_closure_set(v___x_2926_, 3, v_x_2918_);
v___x_2927_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_beforeStx_2916_, v_afterStx_2917_, v___x_2926_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
v_a_2936_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2927_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2927_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg___boxed(lean_object* v_beforeStx_2944_, lean_object* v_afterStx_2945_, lean_object* v_x_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(v_beforeStx_2944_, v_afterStx_2945_, v_x_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0(lean_object* v_00_u03b1_2955_, lean_object* v_beforeStx_2956_, lean_object* v_afterStx_2957_, lean_object* v_x_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(v_beforeStx_2956_, v_afterStx_2957_, v_x_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___boxed(lean_object* v_00_u03b1_2967_, lean_object* v_beforeStx_2968_, lean_object* v_afterStx_2969_, lean_object* v_x_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0(v_00_u03b1_2967_, v_beforeStx_2968_, v_afterStx_2969_, v_x_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0(lean_object* v_lhs_2979_, lean_object* v_rhs_2980_, uint8_t v_kind_2981_, lean_object* v_f_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_lhs_2979_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_rhs_2980_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; uint8_t v___x_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v___x_2994_ = 1;
v___x_2995_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_2981_, v___x_2994_);
v___x_2996_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v___x_2995_, v_f_2982_, v_a_2991_, v_a_2993_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
return v___x_2996_;
}
else
{
lean_dec(v_a_2991_);
lean_dec_ref(v_f_2982_);
return v___x_2992_;
}
}
else
{
lean_dec_ref(v_f_2982_);
lean_dec_ref(v_rhs_2980_);
return v___x_2990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0___boxed(lean_object* v_lhs_2997_, lean_object* v_rhs_2998_, lean_object* v_kind_2999_, lean_object* v_f_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
uint8_t v_kind_7882__boxed_3008_; lean_object* v_res_3009_; 
v_kind_7882__boxed_3008_ = lean_unbox(v_kind_2999_);
v_res_3009_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0(v_lhs_2997_, v_rhs_2998_, v_kind_7882__boxed_3008_, v_f_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1___boxed(lean_object* v_arg_3010_, lean_object* v_f_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1(v_arg_3010_, v_f_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___boxed(lean_object* v_t_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_t_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(lean_object* v_t_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
switch(lean_obj_tag(v_t_3029_))
{
case 0:
{
lean_object* v_infoTrees_3037_; lean_object* v_val_3038_; lean_object* v___x_3039_; lean_object* v_infoState_3040_; lean_object* v_env_3041_; lean_object* v_nextMacroScope_3042_; lean_object* v_ngen_3043_; lean_object* v_auxDeclNGen_3044_; lean_object* v_traceState_3045_; lean_object* v_cache_3046_; lean_object* v_recordedDeps_3047_; lean_object* v_messages_3048_; lean_object* v_snapshotTasks_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3070_; 
v_infoTrees_3037_ = lean_ctor_get(v_t_3029_, 1);
lean_inc_ref(v_infoTrees_3037_);
v_val_3038_ = lean_ctor_get(v_t_3029_, 2);
lean_inc_ref(v_val_3038_);
lean_dec_ref_known(v_t_3029_, 3);
v___x_3039_ = lean_st_ref_take(v_a_3035_);
v_infoState_3040_ = lean_ctor_get(v___x_3039_, 8);
v_env_3041_ = lean_ctor_get(v___x_3039_, 0);
v_nextMacroScope_3042_ = lean_ctor_get(v___x_3039_, 1);
v_ngen_3043_ = lean_ctor_get(v___x_3039_, 2);
v_auxDeclNGen_3044_ = lean_ctor_get(v___x_3039_, 3);
v_traceState_3045_ = lean_ctor_get(v___x_3039_, 4);
v_cache_3046_ = lean_ctor_get(v___x_3039_, 5);
v_recordedDeps_3047_ = lean_ctor_get(v___x_3039_, 6);
v_messages_3048_ = lean_ctor_get(v___x_3039_, 7);
v_snapshotTasks_3049_ = lean_ctor_get(v___x_3039_, 9);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3051_ = v___x_3039_;
v_isShared_3052_ = v_isSharedCheck_3070_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_snapshotTasks_3049_);
lean_inc(v_infoState_3040_);
lean_inc(v_messages_3048_);
lean_inc(v_recordedDeps_3047_);
lean_inc(v_cache_3046_);
lean_inc(v_traceState_3045_);
lean_inc(v_auxDeclNGen_3044_);
lean_inc(v_ngen_3043_);
lean_inc(v_nextMacroScope_3042_);
lean_inc(v_env_3041_);
lean_dec(v___x_3039_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3070_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
uint8_t v_enabled_3053_; lean_object* v_assignment_3054_; lean_object* v_lazyAssignment_3055_; lean_object* v_trees_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3069_; 
v_enabled_3053_ = lean_ctor_get_uint8(v_infoState_3040_, sizeof(void*)*3);
v_assignment_3054_ = lean_ctor_get(v_infoState_3040_, 0);
v_lazyAssignment_3055_ = lean_ctor_get(v_infoState_3040_, 1);
v_trees_3056_ = lean_ctor_get(v_infoState_3040_, 2);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_infoState_3040_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3058_ = v_infoState_3040_;
v_isShared_3059_ = v_isSharedCheck_3069_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_trees_3056_);
lean_inc(v_lazyAssignment_3055_);
lean_inc(v_assignment_3054_);
lean_dec(v_infoState_3040_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3069_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = l_Lean_PersistentArray_append___redArg(v_trees_3056_, v_infoTrees_3037_);
lean_dec_ref(v_infoTrees_3037_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 2, v___x_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_assignment_3054_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_lazyAssignment_3055_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v___x_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3068_, sizeof(void*)*3, v_enabled_3053_);
v___x_3062_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3064_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 8, v___x_3062_);
v___x_3064_ = v___x_3051_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_env_3041_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_nextMacroScope_3042_);
lean_ctor_set(v_reuseFailAlloc_3067_, 2, v_ngen_3043_);
lean_ctor_set(v_reuseFailAlloc_3067_, 3, v_auxDeclNGen_3044_);
lean_ctor_set(v_reuseFailAlloc_3067_, 4, v_traceState_3045_);
lean_ctor_set(v_reuseFailAlloc_3067_, 5, v_cache_3046_);
lean_ctor_set(v_reuseFailAlloc_3067_, 6, v_recordedDeps_3047_);
lean_ctor_set(v_reuseFailAlloc_3067_, 7, v_messages_3048_);
lean_ctor_set(v_reuseFailAlloc_3067_, 8, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3067_, 9, v_snapshotTasks_3049_);
v___x_3064_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = lean_st_ref_put(v_a_3035_, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v_val_3038_);
return v___x_3066_;
}
}
}
}
}
case 1:
{
lean_object* v_ref_3071_; uint8_t v_kind_3072_; lean_object* v_f_3073_; lean_object* v_lhs_3074_; lean_object* v_rhs_3075_; lean_object* v_toCold_3076_; lean_object* v_currRecDepth_3077_; lean_object* v_ref_3078_; uint16_t v_optionFlags_3079_; uint8_t v_suppressElabErrors_3080_; uint8_t v_checkDeprecated_3081_; uint8_t v_isRecordingDeps_3082_; lean_object* v___x_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; lean_object* v_ref_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_ref_3071_ = lean_ctor_get(v_t_3029_, 0);
lean_inc(v_ref_3071_);
v_kind_3072_ = lean_ctor_get_uint8(v_t_3029_, sizeof(void*)*4);
v_f_3073_ = lean_ctor_get(v_t_3029_, 1);
lean_inc_ref(v_f_3073_);
v_lhs_3074_ = lean_ctor_get(v_t_3029_, 2);
lean_inc_ref(v_lhs_3074_);
v_rhs_3075_ = lean_ctor_get(v_t_3029_, 3);
lean_inc_ref(v_rhs_3075_);
lean_dec_ref_known(v_t_3029_, 4);
v_toCold_3076_ = lean_ctor_get(v_a_3034_, 0);
v_currRecDepth_3077_ = lean_ctor_get(v_a_3034_, 1);
v_ref_3078_ = lean_ctor_get(v_a_3034_, 2);
v_optionFlags_3079_ = lean_ctor_get_uint16(v_a_3034_, sizeof(void*)*3);
v_suppressElabErrors_3080_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*3 + 2);
v_checkDeprecated_3081_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3082_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*3 + 4);
v___x_3083_ = lean_box(v_kind_3072_);
v___f_3084_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3084_, 0, v_lhs_3074_);
lean_closure_set(v___f_3084_, 1, v_rhs_3075_);
lean_closure_set(v___f_3084_, 2, v___x_3083_);
lean_closure_set(v___f_3084_, 3, v_f_3073_);
v___x_3085_ = lean_box(0);
v___x_3086_ = lean_box(0);
v___x_3087_ = 0;
v_ref_3088_ = l_Lean_replaceRef(v_ref_3071_, v_ref_3078_);
lean_inc(v_currRecDepth_3077_);
lean_inc_ref(v_toCold_3076_);
v___x_3089_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3089_, 0, v_toCold_3076_);
lean_ctor_set(v___x_3089_, 1, v_currRecDepth_3077_);
lean_ctor_set(v___x_3089_, 2, v_ref_3088_);
lean_ctor_set_uint16(v___x_3089_, sizeof(void*)*3, v_optionFlags_3079_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*3 + 2, v_suppressElabErrors_3080_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*3 + 3, v_checkDeprecated_3081_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*3 + 4, v_isRecordingDeps_3082_);
v___x_3090_ = l_Lean_Elab_Term_withTermInfoContext_x27(v___x_3085_, v_ref_3071_, v___f_3084_, v___x_3086_, v___x_3086_, v___x_3087_, v___x_3087_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v___x_3089_, v_a_3035_);
lean_dec_ref_known(v___x_3089_, 3);
return v___x_3090_;
}
case 2:
{
lean_object* v_ref_3091_; lean_object* v_f_3092_; lean_object* v_arg_3093_; lean_object* v_toCold_3094_; lean_object* v_currRecDepth_3095_; lean_object* v_ref_3096_; uint16_t v_optionFlags_3097_; uint8_t v_suppressElabErrors_3098_; uint8_t v_checkDeprecated_3099_; uint8_t v_isRecordingDeps_3100_; lean_object* v___f_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; lean_object* v_ref_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_ref_3091_ = lean_ctor_get(v_t_3029_, 0);
lean_inc(v_ref_3091_);
v_f_3092_ = lean_ctor_get(v_t_3029_, 1);
lean_inc_ref(v_f_3092_);
v_arg_3093_ = lean_ctor_get(v_t_3029_, 2);
lean_inc_ref(v_arg_3093_);
lean_dec_ref_known(v_t_3029_, 3);
v_toCold_3094_ = lean_ctor_get(v_a_3034_, 0);
v_currRecDepth_3095_ = lean_ctor_get(v_a_3034_, 1);
v_ref_3096_ = lean_ctor_get(v_a_3034_, 2);
v_optionFlags_3097_ = lean_ctor_get_uint16(v_a_3034_, sizeof(void*)*3);
v_suppressElabErrors_3098_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*3 + 2);
v_checkDeprecated_3099_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3100_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*3 + 4);
v___f_3101_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3101_, 0, v_arg_3093_);
lean_closure_set(v___f_3101_, 1, v_f_3092_);
v___x_3102_ = lean_box(0);
v___x_3103_ = lean_box(0);
v___x_3104_ = 0;
v_ref_3105_ = l_Lean_replaceRef(v_ref_3091_, v_ref_3096_);
lean_inc(v_currRecDepth_3095_);
lean_inc_ref(v_toCold_3094_);
v___x_3106_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3106_, 0, v_toCold_3094_);
lean_ctor_set(v___x_3106_, 1, v_currRecDepth_3095_);
lean_ctor_set(v___x_3106_, 2, v_ref_3105_);
lean_ctor_set_uint16(v___x_3106_, sizeof(void*)*3, v_optionFlags_3097_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*3 + 2, v_suppressElabErrors_3098_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*3 + 3, v_checkDeprecated_3099_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*3 + 4, v_isRecordingDeps_3100_);
v___x_3107_ = l_Lean_Elab_Term_withTermInfoContext_x27(v___x_3102_, v_ref_3091_, v___f_3101_, v___x_3103_, v___x_3103_, v___x_3104_, v___x_3104_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v___x_3106_, v_a_3035_);
lean_dec_ref_known(v___x_3106_, 3);
return v___x_3107_;
}
default: 
{
lean_object* v_macroName_3108_; lean_object* v_stx_3109_; lean_object* v_stx_x27_3110_; lean_object* v_nested_3111_; lean_object* v_toCold_3112_; lean_object* v_currRecDepth_3113_; lean_object* v_ref_3114_; uint16_t v_optionFlags_3115_; uint8_t v_suppressElabErrors_3116_; uint8_t v_checkDeprecated_3117_; uint8_t v_isRecordingDeps_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; lean_object* v_ref_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_macroName_3108_ = lean_ctor_get(v_t_3029_, 0);
lean_inc(v_macroName_3108_);
v_stx_3109_ = lean_ctor_get(v_t_3029_, 1);
lean_inc_n(v_stx_3109_, 2);
v_stx_x27_3110_ = lean_ctor_get(v_t_3029_, 2);
lean_inc(v_stx_x27_3110_);
v_nested_3111_ = lean_ctor_get(v_t_3029_, 3);
lean_inc_ref(v_nested_3111_);
lean_dec_ref_known(v_t_3029_, 4);
v_toCold_3112_ = lean_ctor_get(v_a_3034_, 0);
v_currRecDepth_3113_ = lean_ctor_get(v_a_3034_, 1);
v_ref_3114_ = lean_ctor_get(v_a_3034_, 2);
v_optionFlags_3115_ = lean_ctor_get_uint16(v_a_3034_, sizeof(void*)*3);
v_suppressElabErrors_3116_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*3 + 2);
v_checkDeprecated_3117_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3118_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*3 + 4);
v___x_3119_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___boxed), 8, 1);
lean_closure_set(v___x_3119_, 0, v_nested_3111_);
v___x_3120_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___boxed), 11, 4);
lean_closure_set(v___x_3120_, 0, lean_box(0));
lean_closure_set(v___x_3120_, 1, v_stx_3109_);
lean_closure_set(v___x_3120_, 2, v_stx_x27_3110_);
lean_closure_set(v___x_3120_, 3, v___x_3119_);
v___x_3121_ = lean_box(0);
v___x_3122_ = 0;
v_ref_3123_ = l_Lean_replaceRef(v_stx_3109_, v_ref_3114_);
lean_inc(v_currRecDepth_3113_);
lean_inc_ref(v_toCold_3112_);
v___x_3124_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3124_, 0, v_toCold_3112_);
lean_ctor_set(v___x_3124_, 1, v_currRecDepth_3113_);
lean_ctor_set(v___x_3124_, 2, v_ref_3123_);
lean_ctor_set_uint16(v___x_3124_, sizeof(void*)*3, v_optionFlags_3115_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*3 + 2, v_suppressElabErrors_3116_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*3 + 3, v_checkDeprecated_3117_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*3 + 4, v_isRecordingDeps_3118_);
v___x_3125_ = l_Lean_Elab_Term_withTermInfoContext_x27(v_macroName_3108_, v_stx_3109_, v___x_3120_, v___x_3121_, v___x_3121_, v___x_3122_, v___x_3122_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v___x_3124_, v_a_3035_);
lean_dec_ref_known(v___x_3124_, 3);
return v___x_3125_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1(lean_object* v_arg_3126_, lean_object* v_f_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_arg_3126_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3137_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3135_, 1);
v___x_3137_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(v_f_3127_, v_a_3136_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
return v___x_3137_;
}
else
{
lean_dec_ref(v_f_3127_);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0(lean_object* v_00_u03b1_3138_, lean_object* v_stx_3139_, lean_object* v_output_3140_, lean_object* v_x_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_stx_3139_, v_output_3140_, v_x_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3150_, lean_object* v_stx_3151_, lean_object* v_output_3152_, lean_object* v_x_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0(v_00_u03b1_3150_, v_stx_3151_, v_output_3152_, v_x_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3162_, lean_object* v_x_3163_, lean_object* v_mkInfoTree_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_3163_, v_mkInfoTree_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3173_, lean_object* v_x_3174_, lean_object* v_mkInfoTree_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1(v_00_u03b1_3173_, v_x_3174_, v_mkInfoTree_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(lean_object* v___x_3184_, uint8_t v___x_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
if (lean_obj_tag(v_a_3186_) == 0)
{
lean_object* v___x_3188_; 
lean_dec_ref(v___x_3184_);
v___x_3188_ = l_List_reverse___redArg(v_a_3187_);
return v___x_3188_;
}
else
{
lean_object* v_head_3189_; lean_object* v_tail_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3201_; 
v_head_3189_ = lean_ctor_get(v_a_3186_, 0);
v_tail_3190_ = lean_ctor_get(v_a_3186_, 1);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_a_3186_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3192_ = v_a_3186_;
v_isShared_3193_ = v_isSharedCheck_3201_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_tail_3190_);
lean_inc(v_head_3189_);
lean_dec(v_a_3186_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3201_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v_fst_3194_; uint8_t v___x_3195_; 
v_fst_3194_ = lean_ctor_get(v_head_3189_, 0);
lean_inc(v_fst_3194_);
lean_inc_ref(v___x_3184_);
v___x_3195_ = l_Lean_Environment_contains(v___x_3184_, v_fst_3194_, v___x_3185_);
if (v___x_3195_ == 0)
{
lean_del_object(v___x_3192_);
lean_dec(v_head_3189_);
v_a_3186_ = v_tail_3190_;
goto _start;
}
else
{
lean_object* v___x_3198_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 1, v_a_3187_);
v___x_3198_ = v___x_3192_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_head_3189_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_a_3187_);
v___x_3198_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
v_a_3186_ = v_tail_3190_;
v_a_3187_ = v___x_3198_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0___boxed(lean_object* v___x_3202_, lean_object* v___x_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
uint8_t v___x_5471__boxed_3206_; lean_object* v_res_3207_; 
v___x_5471__boxed_3206_ = lean_unbox(v___x_3203_);
v_res_3207_ = l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(v___x_3202_, v___x_5471__boxed_3206_, v_a_3204_, v_a_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(lean_object* v_className_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_env_3213_; lean_object* v___y_3215_; lean_object* v___x_3221_; lean_object* v_toEnvExtension_3222_; lean_object* v_asyncMode_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v_defaultInstances_3226_; lean_object* v___x_3227_; 
v___x_3211_ = l_Lean_Meta_instInhabitedDefaultInstances_default;
v___x_3212_ = lean_st_ref_get(v___y_3209_);
v_env_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc_ref_n(v_env_3213_, 2);
lean_dec(v___x_3212_);
v___x_3221_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_3222_ = lean_ctor_get(v___x_3221_, 0);
v_asyncMode_3223_ = lean_ctor_get(v_toEnvExtension_3222_, 2);
v___x_3224_ = lean_box(0);
v___x_3225_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3211_, v___x_3221_, v_env_3213_, v_asyncMode_3223_, v___x_3224_);
v_defaultInstances_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_defaultInstances_3226_);
lean_dec(v___x_3225_);
v___x_3227_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_3226_, v_className_3208_);
lean_dec(v_defaultInstances_3226_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_box(0);
v___y_3215_ = v___x_3228_;
goto v___jp_3214_;
}
else
{
lean_object* v_val_3229_; 
v_val_3229_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_val_3229_);
lean_dec_ref_known(v___x_3227_, 1);
v___y_3215_ = v_val_3229_;
goto v___jp_3214_;
}
v___jp_3214_:
{
uint8_t v_isExporting_3216_; 
v_isExporting_3216_ = lean_ctor_get_uint8(v_env_3213_, sizeof(void*)*13);
if (v_isExporting_3216_ == 0)
{
lean_object* v___x_3217_; 
lean_dec_ref(v_env_3213_);
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___y_3215_);
return v___x_3217_;
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = lean_box(0);
v___x_3219_ = l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(v_env_3213_, v_isExporting_3216_, v___y_3215_, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
return v___x_3220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg___boxed(lean_object* v_className_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec(v_className_3230_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3234_, lean_object* v_declHint_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v_env_3240_; uint8_t v___x_3241_; 
v___x_3238_ = lean_box(0);
v___x_3239_ = lean_st_ref_get(v___y_3236_);
v_env_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc_ref(v_env_3240_);
lean_dec(v___x_3239_);
v___x_3241_ = l_Lean_Name_isAnonymous(v_declHint_3235_);
if (v___x_3241_ == 0)
{
uint8_t v_isExporting_3242_; 
v_isExporting_3242_ = lean_ctor_get_uint8(v_env_3240_, sizeof(void*)*13);
if (v_isExporting_3242_ == 0)
{
lean_object* v___x_3243_; 
lean_dec_ref(v_env_3240_);
lean_dec(v_declHint_3235_);
v___x_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3243_, 0, v_msg_3234_);
return v___x_3243_;
}
else
{
lean_object* v___x_3244_; uint8_t v___x_3245_; 
lean_inc_ref(v_env_3240_);
v___x_3244_ = l_Lean_Environment_setExporting(v_env_3240_, v___x_3241_);
lean_inc(v_declHint_3235_);
lean_inc_ref(v___x_3244_);
v___x_3245_ = l_Lean_Environment_contains(v___x_3244_, v_declHint_3235_, v_isExporting_3242_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
lean_dec_ref(v___x_3244_);
lean_dec_ref(v_env_3240_);
lean_dec(v_declHint_3235_);
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_msg_3234_);
return v___x_3246_;
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v_c_3254_; lean_object* v___x_3255_; 
v___x_3247_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3248_ = lean_unsigned_to_nat(32u);
v___x_3249_ = lean_mk_empty_array_with_capacity(v___x_3248_);
lean_dec_ref(v___x_3249_);
v___x_3250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5);
v___x_3251_ = l_Lean_Options_empty;
lean_inc_ref(v___x_3244_);
v___x_3252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3244_);
lean_ctor_set(v___x_3252_, 1, v___x_3247_);
lean_ctor_set(v___x_3252_, 2, v___x_3250_);
lean_ctor_set(v___x_3252_, 3, v___x_3251_);
lean_inc(v_declHint_3235_);
v___x_3253_ = l_Lean_MessageData_ofConstName(v_declHint_3235_, v___x_3241_);
v_c_3254_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3254_, 0, v___x_3252_);
lean_ctor_set(v_c_3254_, 1, v___x_3253_);
v___x_3255_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3244_, v_declHint_3235_);
lean_dec_ref(v___x_3244_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_dec_ref(v_env_3240_);
lean_dec(v_declHint_3235_);
v___x_3256_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v_c_3254_);
v___x_3258_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9);
v___x_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = l_Lean_MessageData_note(v___x_3259_);
v___x_3261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3261_, 0, v_msg_3234_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
return v___x_3262_;
}
else
{
lean_object* v_val_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3297_; 
v_val_3263_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3265_ = v___x_3255_;
v_isShared_3266_ = v_isSharedCheck_3297_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_val_3263_);
lean_dec(v___x_3255_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3297_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3267_; lean_object* v_moduleNames_3268_; lean_object* v_mod_3269_; uint8_t v___x_3270_; 
v___x_3267_ = l_Lean_Environment_header(v_env_3240_);
lean_dec_ref(v_env_3240_);
v_moduleNames_3268_ = lean_ctor_get(v___x_3267_, 4);
lean_inc_ref(v_moduleNames_3268_);
lean_dec_ref(v___x_3267_);
v_mod_3269_ = lean_array_get(v___x_3238_, v_moduleNames_3268_, v_val_3263_);
lean_dec(v_val_3263_);
lean_dec_ref(v_moduleNames_3268_);
v___x_3270_ = l_Lean_isPrivateName(v_declHint_3235_);
lean_dec(v_declHint_3235_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
lean_ctor_set(v___x_3272_, 1, v_c_3254_);
v___x_3273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = l_Lean_MessageData_ofName(v_mod_3269_);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3276_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = l_Lean_MessageData_note(v___x_3278_);
v___x_3280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_msg_3234_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set_tag(v___x_3265_, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3280_);
v___x_3282_ = v___x_3265_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3284_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v_c_3254_);
v___x_3286_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = l_Lean_MessageData_ofName(v_mod_3269_);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = l_Lean_MessageData_note(v___x_3291_);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_msg_3234_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set_tag(v___x_3265_, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3293_);
v___x_3295_ = v___x_3265_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3298_; 
lean_dec_ref(v_env_3240_);
lean_dec(v_declHint_3235_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v_msg_3234_);
return v___x_3298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3299_, lean_object* v_declHint_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3299_, v_declHint_3300_, v___y_3301_);
lean_dec(v___y_3301_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_msg_3304_, lean_object* v_declHint_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3321_; 
v___x_3311_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3304_, v_declHint_3305_, v___y_3309_);
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3321_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3321_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3316_ = l_Lean_unknownIdentifierMessageTag;
v___x_3317_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v_a_3312_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3317_);
v___x_3319_ = v___x_3314_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3322_, lean_object* v_declHint_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_3322_, v_declHint_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_ref_3336_; lean_object* v___x_3337_; lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3346_; 
v_ref_3336_ = lean_ctor_get(v___y_3333_, 2);
v___x_3337_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3346_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3346_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v___x_3344_; 
lean_inc(v_ref_3336_);
v___x_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3342_, 0, v_ref_3336_);
lean_ctor_set(v___x_3342_, 1, v_a_3338_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 1);
lean_ctor_set(v___x_3340_, 0, v___x_3342_);
v___x_3344_ = v___x_3340_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_3354_, lean_object* v_msg_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_toCold_3361_; lean_object* v_currRecDepth_3362_; lean_object* v_ref_3363_; uint16_t v_optionFlags_3364_; uint8_t v_suppressElabErrors_3365_; uint8_t v_checkDeprecated_3366_; uint8_t v_isRecordingDeps_3367_; lean_object* v_ref_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v_toCold_3361_ = lean_ctor_get(v___y_3358_, 0);
v_currRecDepth_3362_ = lean_ctor_get(v___y_3358_, 1);
v_ref_3363_ = lean_ctor_get(v___y_3358_, 2);
v_optionFlags_3364_ = lean_ctor_get_uint16(v___y_3358_, sizeof(void*)*3);
v_suppressElabErrors_3365_ = lean_ctor_get_uint8(v___y_3358_, sizeof(void*)*3 + 2);
v_checkDeprecated_3366_ = lean_ctor_get_uint8(v___y_3358_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3367_ = lean_ctor_get_uint8(v___y_3358_, sizeof(void*)*3 + 4);
v_ref_3368_ = l_Lean_replaceRef(v_ref_3354_, v_ref_3363_);
lean_inc(v_currRecDepth_3362_);
lean_inc_ref(v_toCold_3361_);
v___x_3369_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3369_, 0, v_toCold_3361_);
lean_ctor_set(v___x_3369_, 1, v_currRecDepth_3362_);
lean_ctor_set(v___x_3369_, 2, v_ref_3368_);
lean_ctor_set_uint16(v___x_3369_, sizeof(void*)*3, v_optionFlags_3364_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*3 + 2, v_suppressElabErrors_3365_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*3 + 3, v_checkDeprecated_3366_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*3 + 4, v_isRecordingDeps_3367_);
v___x_3370_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3355_, v___y_3356_, v___y_3357_, v___x_3369_, v___y_3359_);
lean_dec_ref_known(v___x_3369_, 3);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3371_, lean_object* v_msg_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3371_, v_msg_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v_ref_3371_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_3379_, lean_object* v_msg_3380_, lean_object* v_declHint_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v___x_3387_; lean_object* v_a_3388_; lean_object* v___x_3389_; 
v___x_3387_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_3380_, v_declHint_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref(v___x_3387_);
v___x_3389_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3379_, v_a_3388_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3390_, lean_object* v_msg_3391_, lean_object* v_declHint_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3390_, v_msg_3391_, v_declHint_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v_ref_3390_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_3399_, lean_object* v_constName_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; uint8_t v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3406_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1);
v___x_3407_ = 0;
lean_inc(v_constName_3400_);
v___x_3408_ = l_Lean_MessageData_ofConstName(v_constName_3400_, v___x_3407_);
v___x_3409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3406_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3);
v___x_3411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3409_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3399_, v___x_3411_, v_constName_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_3413_, lean_object* v_constName_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3413_, v_constName_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v_ref_3413_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(lean_object* v_constName_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v_ref_3427_; lean_object* v___x_3428_; 
v_ref_3427_ = lean_ctor_get(v___y_3424_, 2);
v___x_3428_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3427_, v_constName_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(lean_object* v_constName_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; lean_object* v_env_3443_; uint8_t v___x_3444_; lean_object* v___x_3445_; 
v___x_3442_ = lean_st_ref_get(v___y_3440_);
v_env_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc_ref(v_env_3443_);
lean_dec(v___x_3442_);
v___x_3444_ = 0;
lean_inc(v_constName_3436_);
v___x_3445_ = l_Lean_Environment_find_x3f(v_env_3443_, v_constName_3436_, v___x_3444_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3446_;
}
else
{
lean_object* v_val_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_constName_3436_);
v_val_3447_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3445_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_val_3447_);
lean_dec(v___x_3445_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
lean_ctor_set_tag(v___x_3449_, 0);
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_val_3447_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1___boxed(lean_object* v_constName_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(v_constName_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(lean_object* v_declName_3465_, uint8_t v_lhs_3466_, lean_object* v___x_3467_, lean_object* v_as_x27_3468_, lean_object* v_b_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
if (lean_obj_tag(v_as_x27_3468_) == 0)
{
lean_object* v___x_3475_; 
v___x_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3475_, 0, v_b_3469_);
return v___x_3475_;
}
else
{
lean_object* v_head_3476_; lean_object* v_tail_3477_; lean_object* v_fst_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; lean_object* v___x_3483_; 
lean_dec_ref(v_b_3469_);
v_head_3476_ = lean_ctor_get(v_as_x27_3468_, 0);
v_tail_3477_ = lean_ctor_get(v_as_x27_3468_, 1);
v_fst_3478_ = lean_ctor_get(v_head_3476_, 0);
v___x_3479_ = lean_box(0);
v___x_3480_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0));
v___x_3481_ = lean_unsigned_to_nat(1u);
v___x_3482_ = lean_nat_dec_le(v___x_3467_, v___x_3481_);
lean_inc(v_fst_3478_);
v___x_3483_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(v_fst_3478_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3516_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3486_ = v___x_3483_;
v_isShared_3487_ = v_isSharedCheck_3516_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3516_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = l_Lean_ConstantInfo_type(v_a_3484_);
lean_dec(v_a_3484_);
v___x_3489_ = l_Lean_Expr_getForallBody(v___x_3488_);
lean_dec_ref(v___x_3488_);
if (lean_obj_tag(v___x_3489_) == 5)
{
lean_object* v_fn_3490_; 
v_fn_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc_ref(v_fn_3490_);
lean_dec_ref_known(v___x_3489_, 2);
if (lean_obj_tag(v_fn_3490_) == 5)
{
lean_object* v_fn_3491_; 
v_fn_3491_ = lean_ctor_get(v_fn_3490_, 0);
lean_inc_ref(v_fn_3491_);
if (lean_obj_tag(v_fn_3491_) == 5)
{
lean_object* v_arg_3492_; lean_object* v_arg_3493_; uint8_t v___y_3495_; uint8_t v___y_3505_; 
v_arg_3492_ = lean_ctor_get(v_fn_3490_, 1);
lean_inc_ref(v_arg_3492_);
lean_dec_ref_known(v_fn_3490_, 2);
v_arg_3493_ = lean_ctor_get(v_fn_3491_, 1);
lean_inc_ref(v_arg_3493_);
lean_dec_ref_known(v_fn_3491_, 2);
if (v_lhs_3466_ == 0)
{
lean_dec_ref(v_arg_3492_);
v___y_3505_ = v___x_3482_;
goto v___jp_3504_;
}
else
{
uint8_t v___x_3508_; 
v___x_3508_ = l_Lean_Expr_isAppOf(v_arg_3492_, v_declName_3465_);
lean_dec_ref(v_arg_3492_);
if (v___x_3508_ == 0)
{
v___y_3505_ = v___x_3508_;
goto v___jp_3504_;
}
else
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec_ref(v_arg_3493_);
lean_del_object(v___x_3486_);
v___x_3509_ = lean_box(v_lhs_3466_);
v___x_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
lean_ctor_set(v___x_3511_, 1, v___x_3479_);
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
return v___x_3512_;
}
}
v___jp_3494_:
{
uint8_t v___x_3496_; 
v___x_3496_ = l_Lean_Expr_isAppOf(v_arg_3493_, v_declName_3465_);
lean_dec_ref(v_arg_3493_);
if (v___x_3496_ == 0)
{
lean_del_object(v___x_3486_);
v_as_x27_3468_ = v_tail_3477_;
v_b_3469_ = v___x_3480_;
goto _start;
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3502_; 
v___x_3498_ = lean_box(v___y_3495_);
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
v___x_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3479_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3500_);
v___x_3502_ = v___x_3486_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
v___jp_3504_:
{
uint8_t v___x_3506_; 
v___x_3506_ = 1;
if (v_lhs_3466_ == 0)
{
v___y_3495_ = v___x_3506_;
goto v___jp_3494_;
}
else
{
if (v___y_3505_ == 0)
{
lean_dec_ref(v_arg_3493_);
lean_del_object(v___x_3486_);
v_as_x27_3468_ = v_tail_3477_;
v_b_3469_ = v___x_3480_;
goto _start;
}
else
{
v___y_3495_ = v___x_3506_;
goto v___jp_3494_;
}
}
}
}
else
{
lean_dec_ref(v_fn_3491_);
lean_dec_ref_known(v_fn_3490_, 2);
lean_del_object(v___x_3486_);
v_as_x27_3468_ = v_tail_3477_;
v_b_3469_ = v___x_3480_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_3490_);
lean_del_object(v___x_3486_);
v_as_x27_3468_ = v_tail_3477_;
v_b_3469_ = v___x_3480_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_3489_);
lean_del_object(v___x_3486_);
v_as_x27_3468_ = v_tail_3477_;
v_b_3469_ = v___x_3480_;
goto _start;
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
v_a_3517_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3483_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3483_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___boxed(lean_object* v_declName_3525_, lean_object* v_lhs_3526_, lean_object* v___x_3527_, lean_object* v_as_x27_3528_, lean_object* v_b_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
uint8_t v_lhs_boxed_3535_; lean_object* v_res_3536_; 
v_lhs_boxed_3535_ = lean_unbox(v_lhs_3526_);
v_res_3536_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3525_, v_lhs_boxed_3535_, v___x_3527_, v_as_x27_3528_, v_b_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v_as_x27_3528_);
lean_dec(v___x_3527_);
lean_dec(v_declName_3525_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(lean_object* v_f_3537_, lean_object* v_maxType_3538_, uint8_t v_lhs_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
if (lean_obj_tag(v_f_3537_) == 4)
{
lean_object* v_declName_3545_; lean_object* v___x_3546_; 
v_declName_3545_ = lean_ctor_get(v_f_3537_, 0);
v___x_3546_ = l_Lean_Expr_getAppFn(v_maxType_3538_);
if (lean_obj_tag(v___x_3546_) == 4)
{
lean_object* v_declName_3547_; lean_object* v_className_3548_; lean_object* v___x_3549_; lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3586_; 
v_declName_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_declName_3547_);
lean_dec_ref_known(v___x_3546_, 2);
v_className_3548_ = l_Lean_Name_getPrefix(v_declName_3545_);
v___x_3549_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3548_, v_a_3543_);
lean_dec(v_className_3548_);
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3586_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3586_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3554_ = l_List_lengthTR___redArg(v_a_3550_);
v___x_3555_ = lean_unsigned_to_nat(1u);
v___x_3556_ = lean_nat_dec_le(v___x_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_del_object(v___x_3552_);
v___x_3557_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0));
v___x_3558_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3547_, v_lhs_3539_, v___x_3554_, v_a_3550_, v___x_3557_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
lean_dec(v_a_3550_);
lean_dec(v___x_3554_);
lean_dec(v_declName_3547_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3572_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3572_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3572_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_fst_3563_; 
v_fst_3563_ = lean_ctor_get(v_a_3559_, 0);
lean_inc(v_fst_3563_);
lean_dec(v_a_3559_);
if (lean_obj_tag(v_fst_3563_) == 0)
{
lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3564_ = lean_box(v___x_3556_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3564_);
v___x_3566_ = v___x_3561_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
else
{
lean_object* v_val_3568_; lean_object* v___x_3570_; 
v_val_3568_ = lean_ctor_get(v_fst_3563_, 0);
lean_inc(v_val_3568_);
lean_dec_ref_known(v_fst_3563_, 1);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v_val_3568_);
v___x_3570_ = v___x_3561_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_val_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
v_a_3573_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3558_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3558_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
else
{
uint8_t v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
lean_dec(v___x_3554_);
lean_dec(v_a_3550_);
lean_dec(v_declName_3547_);
v___x_3581_ = 0;
v___x_3582_ = lean_box(v___x_3581_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v___x_3582_);
v___x_3584_ = v___x_3552_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
uint8_t v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_dec_ref(v___x_3546_);
v___x_3587_ = 0;
v___x_3588_ = lean_box(v___x_3587_);
v___x_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
return v___x_3589_;
}
}
else
{
uint8_t v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = 0;
v___x_3591_ = lean_box(v___x_3590_);
v___x_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
return v___x_3592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances___boxed(lean_object* v_f_3593_, lean_object* v_maxType_3594_, lean_object* v_lhs_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
uint8_t v_lhs_boxed_3601_; lean_object* v_res_3602_; 
v_lhs_boxed_3601_ = lean_unbox(v_lhs_3595_);
v_res_3602_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(v_f_3593_, v_maxType_3594_, v_lhs_boxed_3601_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
lean_dec_ref(v_maxType_3594_);
lean_dec_ref(v_f_3593_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0(lean_object* v_className_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3603_, v___y_3607_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___boxed(lean_object* v_className_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0(v_className_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v_className_3610_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2(lean_object* v_declName_3617_, uint8_t v_lhs_3618_, lean_object* v___x_3619_, lean_object* v_as_3620_, lean_object* v_as_x27_3621_, lean_object* v_b_3622_, lean_object* v_a_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3617_, v_lhs_3618_, v___x_3619_, v_as_x27_3621_, v_b_3622_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___boxed(lean_object* v_declName_3630_, lean_object* v_lhs_3631_, lean_object* v___x_3632_, lean_object* v_as_3633_, lean_object* v_as_x27_3634_, lean_object* v_b_3635_, lean_object* v_a_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
uint8_t v_lhs_boxed_3642_; lean_object* v_res_3643_; 
v_lhs_boxed_3642_ = lean_unbox(v_lhs_3631_);
v_res_3643_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2(v_declName_3630_, v_lhs_boxed_3642_, v___x_3632_, v_as_3633_, v_as_x27_3634_, v_b_3635_, v_a_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v_as_x27_3634_);
lean_dec(v_as_3633_);
lean_dec(v___x_3632_);
lean_dec(v_declName_3630_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2(lean_object* v_00_u03b1_3644_, lean_object* v_constName_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3652_, lean_object* v_constName_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2(v_00_u03b1_3652_, v_constName_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_3660_, lean_object* v_ref_3661_, lean_object* v_constName_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3661_, v_constName_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3669_, lean_object* v_ref_3670_, lean_object* v_constName_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3(v_00_u03b1_3669_, v_ref_3670_, v_constName_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v_ref_3670_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_3678_, lean_object* v_ref_3679_, lean_object* v_msg_3680_, lean_object* v_declHint_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3679_, v_msg_3680_, v_declHint_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3688_, lean_object* v_ref_3689_, lean_object* v_msg_3690_, lean_object* v_declHint_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_3688_, v_ref_3689_, v_msg_3690_, v_declHint_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v_ref_3689_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_3698_, lean_object* v_declHint_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3698_, v_declHint_3699_, v___y_3703_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_3706_, lean_object* v_declHint_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_3706_, v_declHint_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_3714_, lean_object* v_ref_3715_, lean_object* v_msg_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3715_, v_msg_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3723_, lean_object* v_ref_3724_, lean_object* v_msg_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_3723_, v_ref_3724_, v_msg_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v_ref_3724_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_3732_, lean_object* v_msg_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3740_, lean_object* v_msg_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_3740_, v_msg_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(lean_object* v_f_3748_, lean_object* v_maxType_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
lean_object* v_a_3756_; 
if (lean_obj_tag(v_f_3748_) == 4)
{
lean_object* v_declName_3763_; lean_object* v_className_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v_declName_3763_ = lean_ctor_get(v_f_3748_, 0);
v_className_3764_ = l_Lean_Name_getPrefix(v_declName_3763_);
v___x_3765_ = lean_unsigned_to_nat(3u);
v___x_3766_ = lean_mk_empty_array_with_capacity(v___x_3765_);
lean_inc_ref_n(v_maxType_3749_, 2);
v___x_3767_ = lean_array_push(v___x_3766_, v_maxType_3749_);
v___x_3768_ = lean_array_push(v___x_3767_, v_maxType_3749_);
v___x_3769_ = lean_array_push(v___x_3768_, v_maxType_3749_);
v___x_3770_ = l_Lean_Meta_mkAppM(v_className_3764_, v___x_3769_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3772_ = lean_box(0);
v___x_3773_ = l_Lean_Meta_trySynthInstance(v_a_3771_, v___x_3772_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3788_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3776_ = v___x_3773_;
v_isShared_3777_ = v_isSharedCheck_3788_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3773_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3788_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
if (lean_obj_tag(v_a_3774_) == 1)
{
uint8_t v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3781_; 
lean_dec_ref_known(v_a_3774_, 1);
v___x_3778_ = 1;
v___x_3779_ = lean_box(v___x_3778_);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 0, v___x_3779_);
v___x_3781_ = v___x_3776_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
else
{
uint8_t v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
lean_dec(v_a_3774_);
v___x_3783_ = 0;
v___x_3784_ = lean_box(v___x_3783_);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 0, v___x_3784_);
v___x_3786_ = v___x_3776_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v_a_3789_; 
v_a_3789_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3773_, 1);
v_a_3756_ = v_a_3789_;
goto v___jp_3755_;
}
}
else
{
lean_object* v_a_3790_; 
v_a_3790_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3770_, 1);
v_a_3756_ = v_a_3790_;
goto v___jp_3755_;
}
}
else
{
uint8_t v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
lean_dec_ref(v_maxType_3749_);
v___x_3791_ = 0;
v___x_3792_ = lean_box(v___x_3791_);
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
return v___x_3793_;
}
v___jp_3755_:
{
uint8_t v___x_3757_; 
v___x_3757_ = l_Lean_Exception_isInterrupt(v_a_3756_);
if (v___x_3757_ == 0)
{
uint8_t v___x_3758_; 
lean_inc_ref(v_a_3756_);
v___x_3758_ = l_Lean_Exception_isRuntime(v_a_3756_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_dec_ref(v_a_3756_);
v___x_3759_ = lean_box(v___x_3758_);
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
return v___x_3760_;
}
else
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3761_, 0, v_a_3756_);
return v___x_3761_;
}
}
else
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3762_, 0, v_a_3756_);
return v___x_3762_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance___boxed(lean_object* v_f_3794_, lean_object* v_maxType_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(v_f_3794_, v_maxType_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
lean_dec_ref(v_f_3794_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(lean_object* v_cls_3802_, lean_object* v_msg_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_ref_3809_; lean_object* v___x_3810_; lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3856_; 
v_ref_3809_ = lean_ctor_get(v___y_3806_, 2);
v___x_3810_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3856_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3856_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; lean_object* v_traceState_3816_; lean_object* v_env_3817_; lean_object* v_nextMacroScope_3818_; lean_object* v_ngen_3819_; lean_object* v_auxDeclNGen_3820_; lean_object* v_cache_3821_; lean_object* v_recordedDeps_3822_; lean_object* v_messages_3823_; lean_object* v_infoState_3824_; lean_object* v_snapshotTasks_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3855_; 
v___x_3815_ = lean_st_ref_take(v___y_3807_);
v_traceState_3816_ = lean_ctor_get(v___x_3815_, 4);
v_env_3817_ = lean_ctor_get(v___x_3815_, 0);
v_nextMacroScope_3818_ = lean_ctor_get(v___x_3815_, 1);
v_ngen_3819_ = lean_ctor_get(v___x_3815_, 2);
v_auxDeclNGen_3820_ = lean_ctor_get(v___x_3815_, 3);
v_cache_3821_ = lean_ctor_get(v___x_3815_, 5);
v_recordedDeps_3822_ = lean_ctor_get(v___x_3815_, 6);
v_messages_3823_ = lean_ctor_get(v___x_3815_, 7);
v_infoState_3824_ = lean_ctor_get(v___x_3815_, 8);
v_snapshotTasks_3825_ = lean_ctor_get(v___x_3815_, 9);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3827_ = v___x_3815_;
v_isShared_3828_ = v_isSharedCheck_3855_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_snapshotTasks_3825_);
lean_inc(v_infoState_3824_);
lean_inc(v_messages_3823_);
lean_inc(v_recordedDeps_3822_);
lean_inc(v_cache_3821_);
lean_inc(v_traceState_3816_);
lean_inc(v_auxDeclNGen_3820_);
lean_inc(v_ngen_3819_);
lean_inc(v_nextMacroScope_3818_);
lean_inc(v_env_3817_);
lean_dec(v___x_3815_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3855_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
uint64_t v_tid_3829_; lean_object* v_traces_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3854_; 
v_tid_3829_ = lean_ctor_get_uint64(v_traceState_3816_, sizeof(void*)*1);
v_traces_3830_ = lean_ctor_get(v_traceState_3816_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_traceState_3816_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3832_ = v_traceState_3816_;
v_isShared_3833_ = v_isSharedCheck_3854_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_traces_3830_);
lean_dec(v_traceState_3816_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3854_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; double v___x_3836_; uint8_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3834_ = lean_box(0);
v___x_3835_ = lean_box(0);
v___x_3836_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0);
v___x_3837_ = 0;
v___x_3838_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1));
v___x_3839_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3839_, 0, v_cls_3802_);
lean_ctor_set(v___x_3839_, 1, v___x_3835_);
lean_ctor_set(v___x_3839_, 2, v___x_3838_);
lean_ctor_set_float(v___x_3839_, sizeof(void*)*3, v___x_3836_);
lean_ctor_set_float(v___x_3839_, sizeof(void*)*3 + 8, v___x_3836_);
lean_ctor_set_uint8(v___x_3839_, sizeof(void*)*3 + 16, v___x_3837_);
v___x_3840_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2));
v___x_3841_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3839_);
lean_ctor_set(v___x_3841_, 1, v_a_3811_);
lean_ctor_set(v___x_3841_, 2, v___x_3840_);
lean_inc(v_ref_3809_);
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v_ref_3809_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = l_Lean_PersistentArray_push___redArg(v_traces_3830_, v___x_3842_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v___x_3843_);
v___x_3845_ = v___x_3832_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3843_);
lean_ctor_set_uint64(v_reuseFailAlloc_3853_, sizeof(void*)*1, v_tid_3829_);
v___x_3845_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3847_; 
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 4, v___x_3845_);
v___x_3847_ = v___x_3827_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_env_3817_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_nextMacroScope_3818_);
lean_ctor_set(v_reuseFailAlloc_3852_, 2, v_ngen_3819_);
lean_ctor_set(v_reuseFailAlloc_3852_, 3, v_auxDeclNGen_3820_);
lean_ctor_set(v_reuseFailAlloc_3852_, 4, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3852_, 5, v_cache_3821_);
lean_ctor_set(v_reuseFailAlloc_3852_, 6, v_recordedDeps_3822_);
lean_ctor_set(v_reuseFailAlloc_3852_, 7, v_messages_3823_);
lean_ctor_set(v_reuseFailAlloc_3852_, 8, v_infoState_3824_);
lean_ctor_set(v_reuseFailAlloc_3852_, 9, v_snapshotTasks_3825_);
v___x_3847_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3848_; lean_object* v___x_3850_; 
v___x_3848_ = lean_st_ref_put(v___y_3807_, v___x_3847_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 0, v___x_3834_);
v___x_3850_ = v___x_3813_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3834_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg___boxed(lean_object* v_cls_3857_, lean_object* v_msg_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v_cls_3857_, v_msg_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
return v_res_3864_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1(void){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3866_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__0));
v___x_3867_ = l_Lean_stringToMessageData(v___x_3866_);
return v___x_3867_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__2));
v___x_3870_ = l_Lean_stringToMessageData(v___x_3869_);
return v___x_3870_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5(void){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__4));
v___x_3873_ = l_Lean_stringToMessageData(v___x_3872_);
return v___x_3873_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7(void){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__6));
v___x_3876_ = l_Lean_stringToMessageData(v___x_3875_);
return v___x_3876_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9(void){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__8));
v___x_3879_ = l_Lean_stringToMessageData(v___x_3878_);
return v___x_3879_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__0));
v___x_3882_ = l_Lean_stringToMessageData(v___x_3881_);
return v___x_3882_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__2));
v___x_3885_ = l_Lean_stringToMessageData(v___x_3884_);
return v___x_3885_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__5));
v___x_3890_ = l_Lean_MessageData_ofFormat(v___x_3889_);
return v___x_3890_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__7));
v___x_3893_ = l_Lean_stringToMessageData(v___x_3892_);
return v___x_3893_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10(void){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__9));
v___x_3896_ = l_Lean_stringToMessageData(v___x_3895_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(lean_object* v_tree_3899_, lean_object* v_expectedType_x3f_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___x_3929_; 
lean_inc(v_expectedType_x3f_3900_);
lean_inc_ref(v_tree_3899_);
v___x_3929_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v_tree_3899_, v_expectedType_x3f_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_toCold_3930_; lean_object* v_options_3931_; lean_object* v_a_3932_; lean_object* v_inheritedTraceOptions_3933_; uint8_t v_hasTrace_3934_; lean_object* v___x_3935_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3998_; lean_object* v___y_3999_; 
v_toCold_3930_ = lean_ctor_get(v_a_3905_, 0);
v_options_3931_ = lean_ctor_get(v_toCold_3930_, 2);
v_a_3932_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3929_, 1);
v_inheritedTraceOptions_3933_ = lean_ctor_get(v_toCold_3930_, 11);
v_hasTrace_3934_ = lean_ctor_get_uint8(v_options_3931_, sizeof(void*)*1);
v___x_3935_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
if (v_hasTrace_3934_ == 0)
{
v___y_3963_ = v_a_3901_;
v___y_3964_ = v_a_3902_;
v___y_3965_ = v_a_3903_;
v___y_3966_ = v_a_3904_;
v___y_3967_ = v_a_3905_;
v___y_3968_ = v_a_3906_;
goto v___jp_3962_;
}
else
{
lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4010_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4011_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3933_, v_options_3931_, v___x_4010_);
if (v___x_4011_ == 0)
{
v___y_3963_ = v_a_3901_;
v___y_3964_ = v_a_3902_;
v___y_3965_ = v_a_3903_;
v___y_3966_ = v_a_3904_;
v___y_3967_ = v_a_3905_;
v___y_3968_ = v_a_3906_;
goto v___jp_3962_;
}
else
{
lean_object* v_max_x3f_4012_; uint8_t v_hasUncomparable_4013_; uint8_t v_hasUnknown_4014_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___x_4026_; lean_object* v___y_4028_; 
v_max_x3f_4012_ = lean_ctor_get(v_a_3932_, 0);
v_hasUncomparable_4013_ = lean_ctor_get_uint8(v_a_3932_, sizeof(void*)*1);
v_hasUnknown_4014_ = lean_ctor_get_uint8(v_a_3932_, sizeof(void*)*1 + 1);
v___x_4026_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8);
if (v_hasUncomparable_4013_ == 0)
{
lean_object* v___x_4036_; 
v___x_4036_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_4028_ = v___x_4036_;
goto v___jp_4027_;
}
else
{
lean_object* v___x_4037_; 
v___x_4037_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_4028_ = v___x_4037_;
goto v___jp_4027_;
}
v___jp_4015_:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
lean_inc_ref(v___y_4017_);
v___x_4018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___y_4017_);
v___x_4019_ = l_Lean_MessageData_ofFormat(v___x_4018_);
v___x_4020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___y_4016_);
lean_ctor_set(v___x_4020_, 1, v___x_4019_);
v___x_4021_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3);
v___x_4022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4020_);
lean_ctor_set(v___x_4022_, 1, v___x_4021_);
if (lean_obj_tag(v_max_x3f_4012_) == 0)
{
lean_object* v___x_4023_; 
v___x_4023_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6);
v___y_3998_ = v___x_4022_;
v___y_3999_ = v___x_4023_;
goto v___jp_3997_;
}
else
{
lean_object* v_val_4024_; lean_object* v___x_4025_; 
v_val_4024_ = lean_ctor_get(v_max_x3f_4012_, 0);
lean_inc(v_val_4024_);
v___x_4025_ = l_Lean_MessageData_ofExpr(v_val_4024_);
v___y_3998_ = v___x_4022_;
v___y_3999_ = v___x_4025_;
goto v___jp_3997_;
}
}
v___jp_4027_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_inc_ref(v___y_4028_);
v___x_4029_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___y_4028_);
v___x_4030_ = l_Lean_MessageData_ofFormat(v___x_4029_);
v___x_4031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4026_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10);
v___x_4033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4031_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
if (v_hasUnknown_4014_ == 0)
{
lean_object* v___x_4034_; 
v___x_4034_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_4016_ = v___x_4033_;
v___y_4017_ = v___x_4034_;
goto v___jp_4015_;
}
else
{
lean_object* v___x_4035_; 
v___x_4035_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_4016_ = v___x_4033_;
v___y_4017_ = v___x_4035_;
goto v___jp_4015_;
}
}
}
}
v___jp_3936_:
{
lean_object* v_toCold_3944_; lean_object* v_options_3945_; uint8_t v_hasTrace_3946_; 
v_toCold_3944_ = lean_ctor_get(v___y_3942_, 0);
v_options_3945_ = lean_ctor_get(v_toCold_3944_, 2);
v_hasTrace_3946_ = lean_ctor_get_uint8(v_options_3945_, sizeof(void*)*1);
if (v_hasTrace_3946_ == 0)
{
v___y_3920_ = v___y_3937_;
v___y_3921_ = v___y_3938_;
v___y_3922_ = v___y_3939_;
v___y_3923_ = v___y_3940_;
v___y_3924_ = v___y_3941_;
v___y_3925_ = v___y_3942_;
v___y_3926_ = v___y_3943_;
goto v___jp_3919_;
}
else
{
lean_object* v_inheritedTraceOptions_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v_inheritedTraceOptions_3947_ = lean_ctor_get(v_toCold_3944_, 11);
v___x_3948_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_3949_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3947_, v_options_3945_, v___x_3948_);
if (v___x_3949_ == 0)
{
v___y_3920_ = v___y_3937_;
v___y_3921_ = v___y_3938_;
v___y_3922_ = v___y_3939_;
v___y_3923_ = v___y_3940_;
v___y_3924_ = v___y_3941_;
v___y_3925_ = v___y_3942_;
v___y_3926_ = v___y_3943_;
goto v___jp_3919_;
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3950_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1);
lean_inc_ref(v___y_3937_);
v___x_3951_ = l_Lean_MessageData_ofExpr(v___y_3937_);
v___x_3952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3950_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_3935_, v___x_3952_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_dec_ref_known(v___x_3953_, 1);
v___y_3920_ = v___y_3937_;
v___y_3921_ = v___y_3938_;
v___y_3922_ = v___y_3939_;
v___y_3923_ = v___y_3940_;
v___y_3924_ = v___y_3941_;
v___y_3925_ = v___y_3942_;
v___y_3926_ = v___y_3943_;
goto v___jp_3919_;
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec_ref(v___y_3937_);
lean_dec(v_expectedType_x3f_3900_);
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3953_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3953_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
}
}
v___jp_3962_:
{
uint8_t v_hasUncomparable_3969_; 
v_hasUncomparable_3969_ = lean_ctor_get_uint8(v_a_3932_, sizeof(void*)*1);
if (v_hasUncomparable_3969_ == 0)
{
lean_object* v_max_x3f_3970_; 
v_max_x3f_3970_ = lean_ctor_get(v_a_3932_, 0);
lean_inc(v_max_x3f_3970_);
if (lean_obj_tag(v_max_x3f_3970_) == 0)
{
lean_dec(v_a_3932_);
v___y_3909_ = v___y_3965_;
v___y_3910_ = v___y_3964_;
v___y_3911_ = v___y_3968_;
v___y_3912_ = v___y_3967_;
v___y_3913_ = v___y_3963_;
v___y_3914_ = v___y_3966_;
goto v___jp_3908_;
}
else
{
uint8_t v_hasUnknown_3971_; lean_object* v_val_3972_; lean_object* v___x_3973_; 
v_hasUnknown_3971_ = lean_ctor_get_uint8(v_a_3932_, sizeof(void*)*1 + 1);
lean_dec(v_a_3932_);
v_val_3972_ = lean_ctor_get(v_max_x3f_3970_, 0);
lean_inc_n(v_val_3972_, 2);
lean_dec_ref_known(v_max_x3f_3970_, 1);
v___x_3973_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v_tree_3899_, v_val_3972_, v_hasUncomparable_3969_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3975_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_a_3974_);
lean_dec_ref_known(v___x_3973_, 1);
v___x_3975_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_3974_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3975_) == 0)
{
if (v_hasUnknown_3971_ == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3977_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc_n(v_a_3976_, 2);
lean_dec_ref_known(v___x_3975_, 1);
lean_inc(v___y_3968_);
lean_inc_ref(v___y_3967_);
lean_inc(v___y_3966_);
lean_inc_ref(v___y_3965_);
v___x_3977_ = lean_infer_type(v_a_3976_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3979_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref_known(v___x_3977_, 1);
v___x_3979_ = l_Lean_Meta_isExprDefEqGuarded(v_a_3978_, v_val_3972_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_dec_ref_known(v___x_3979_, 1);
v___y_3937_ = v_a_3976_;
v___y_3938_ = v___y_3963_;
v___y_3939_ = v___y_3964_;
v___y_3940_ = v___y_3965_;
v___y_3941_ = v___y_3966_;
v___y_3942_ = v___y_3967_;
v___y_3943_ = v___y_3968_;
goto v___jp_3936_;
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v_a_3976_);
lean_dec(v_expectedType_x3f_3900_);
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3979_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3979_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_dec(v_a_3976_);
lean_dec(v_val_3972_);
lean_dec(v_expectedType_x3f_3900_);
return v___x_3977_;
}
}
else
{
lean_object* v_a_3988_; 
lean_dec(v_val_3972_);
v_a_3988_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v___x_3975_, 1);
v___y_3937_ = v_a_3988_;
v___y_3938_ = v___y_3963_;
v___y_3939_ = v___y_3964_;
v___y_3940_ = v___y_3965_;
v___y_3941_ = v___y_3966_;
v___y_3942_ = v___y_3967_;
v___y_3943_ = v___y_3968_;
goto v___jp_3936_;
}
}
else
{
lean_dec(v_val_3972_);
lean_dec(v_expectedType_x3f_3900_);
return v___x_3975_;
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_dec(v_val_3972_);
lean_dec(v_expectedType_x3f_3900_);
v_a_3989_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3973_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3973_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
else
{
lean_dec(v_a_3932_);
v___y_3909_ = v___y_3965_;
v___y_3910_ = v___y_3964_;
v___y_3911_ = v___y_3968_;
v___y_3912_ = v___y_3967_;
v___y_3913_ = v___y_3963_;
v___y_3914_ = v___y_3966_;
goto v___jp_3908_;
}
}
v___jp_3997_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___y_3998_);
lean_ctor_set(v___x_4000_, 1, v___y_3999_);
v___x_4001_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_3935_, v___x_4000_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_dec_ref_known(v___x_4001_, 1);
v___y_3963_ = v_a_3901_;
v___y_3964_ = v_a_3902_;
v___y_3965_ = v_a_3903_;
v___y_3966_ = v_a_3904_;
v___y_3967_ = v_a_3905_;
v___y_3968_ = v_a_3906_;
goto v___jp_3962_;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec(v_a_3932_);
lean_dec(v_expectedType_x3f_3900_);
lean_dec_ref(v_tree_3899_);
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_4001_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_4001_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v_expectedType_x3f_3900_);
lean_dec_ref(v_tree_3899_);
v_a_4038_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_3929_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_3929_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
v___jp_3908_:
{
lean_object* v___x_3915_; 
v___x_3915_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_tree_3899_, v___y_3913_, v___y_3910_, v___y_3909_, v___y_3914_, v___y_3912_, v___y_3911_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3917_ = lean_box(0);
v___x_3918_ = l_Lean_Elab_Term_ensureHasType(v_expectedType_x3f_3900_, v_a_3916_, v___x_3917_, v___x_3917_, v___y_3913_, v___y_3910_, v___y_3909_, v___y_3914_, v___y_3912_, v___y_3911_);
return v___x_3918_;
}
else
{
lean_dec(v_expectedType_x3f_3900_);
return v___x_3915_;
}
}
v___jp_3919_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = lean_box(0);
v___x_3928_ = l_Lean_Elab_Term_ensureHasType(v_expectedType_x3f_3900_, v___y_3920_, v___x_3927_, v___x_3927_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
return v___x_3928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0(lean_object* v_maxType_4046_, lean_object* v_nested_4047_, lean_object* v_f_x3f_4048_, uint8_t v_lhs_4049_, uint8_t v_isPred_4050_, lean_object* v_macroName_4051_, lean_object* v_stx_4052_, lean_object* v_stx_x27_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4046_, v_nested_4047_, v_f_x3f_4048_, v_lhs_4049_, v_isPred_4050_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4070_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4064_ = v___x_4061_;
v_isShared_4065_ = v_isSharedCheck_4070_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4061_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4070_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4066_; lean_object* v___x_4068_; 
v___x_4066_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4066_, 0, v_macroName_4051_);
lean_ctor_set(v___x_4066_, 1, v_stx_4052_);
lean_ctor_set(v___x_4066_, 2, v_stx_x27_4053_);
lean_ctor_set(v___x_4066_, 3, v_a_4062_);
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 0, v___x_4066_);
v___x_4068_ = v___x_4064_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4066_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
else
{
lean_dec(v_stx_x27_4053_);
lean_dec(v_stx_4052_);
lean_dec(v_macroName_4051_);
return v___x_4061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0___boxed(lean_object* v_maxType_4071_, lean_object* v_nested_4072_, lean_object* v_f_x3f_4073_, lean_object* v_lhs_4074_, lean_object* v_isPred_4075_, lean_object* v_macroName_4076_, lean_object* v_stx_4077_, lean_object* v_stx_x27_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
uint8_t v_lhs_boxed_4086_; uint8_t v_isPred_boxed_4087_; lean_object* v_res_4088_; 
v_lhs_boxed_4086_ = lean_unbox(v_lhs_4074_);
v_isPred_boxed_4087_ = lean_unbox(v_isPred_4075_);
v_res_4088_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0(v_maxType_4071_, v_nested_4072_, v_f_x3f_4073_, v_lhs_boxed_4086_, v_isPred_boxed_4087_, v_macroName_4076_, v_stx_4077_, v_stx_x27_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(lean_object* v_maxType_4089_, lean_object* v_t_4090_, lean_object* v_f_x3f_4091_, uint8_t v_lhs_4092_, uint8_t v_isPred_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
switch(lean_obj_tag(v_t_4090_))
{
case 0:
{
lean_object* v_ref_4101_; lean_object* v_infoTrees_4102_; lean_object* v_val_4103_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v_toCold_4109_; lean_object* v_currRecDepth_4110_; lean_object* v_ref_4111_; uint16_t v_optionFlags_4112_; uint8_t v_suppressElabErrors_4113_; uint8_t v_checkDeprecated_4114_; uint8_t v_isRecordingDeps_4115_; lean_object* v___y_4116_; lean_object* v___x_4138_; 
v_ref_4101_ = lean_ctor_get(v_t_4090_, 0);
v_infoTrees_4102_ = lean_ctor_get(v_t_4090_, 1);
v_val_4103_ = lean_ctor_get(v_t_4090_, 2);
lean_inc(v_a_4099_);
lean_inc_ref(v_a_4098_);
lean_inc(v_a_4097_);
lean_inc_ref(v_a_4096_);
lean_inc_ref(v_val_4103_);
v___x_4138_ = lean_infer_type(v_val_4103_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v___x_4140_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(v_a_4139_, v_a_4097_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_toCold_4141_; lean_object* v_options_4142_; lean_object* v_a_4143_; lean_object* v_inheritedTraceOptions_4144_; uint8_t v_hasTrace_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; 
v_toCold_4141_ = lean_ctor_get(v_a_4098_, 0);
v_options_4142_ = lean_ctor_get(v_toCold_4141_, 2);
v_a_4143_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4140_, 1);
v_inheritedTraceOptions_4144_ = lean_ctor_get(v_toCold_4141_, 11);
v_hasTrace_4145_ = lean_ctor_get_uint8(v_options_4142_, sizeof(void*)*1);
v___x_4146_ = l_Lean_Expr_cleanupAnnotations(v_a_4143_);
v___x_4147_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
if (v_hasTrace_4145_ == 0)
{
v___y_4212_ = v_a_4094_;
v___y_4213_ = v_a_4095_;
v___y_4214_ = v_a_4096_;
v___y_4215_ = v_a_4097_;
v___y_4216_ = v_a_4098_;
v___y_4217_ = v_a_4099_;
goto v___jp_4211_;
}
else
{
lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4239_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4144_, v_options_4142_, v___x_4238_);
if (v___x_4239_ == 0)
{
v___y_4212_ = v_a_4094_;
v___y_4213_ = v_a_4095_;
v___y_4214_ = v_a_4096_;
v___y_4215_ = v_a_4097_;
v___y_4216_ = v_a_4098_;
v___y_4217_ = v_a_4099_;
goto v___jp_4211_;
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4240_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7);
lean_inc_ref(v_val_4103_);
v___x_4241_ = l_Lean_MessageData_ofExpr(v_val_4103_);
v___x_4242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4240_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
v___x_4243_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3);
v___x_4244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4242_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
lean_inc_ref(v___x_4146_);
v___x_4245_ = l_Lean_MessageData_ofExpr(v___x_4146_);
v___x_4246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4244_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9);
v___x_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
lean_inc_ref(v_maxType_4089_);
v___x_4249_ = l_Lean_MessageData_ofExpr(v_maxType_4089_);
v___x_4250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4248_);
lean_ctor_set(v___x_4250_, 1, v___x_4249_);
v___x_4251_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4147_, v___x_4250_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_dec_ref_known(v___x_4251_, 1);
v___y_4212_ = v_a_4094_;
v___y_4213_ = v_a_4095_;
v___y_4214_ = v_a_4096_;
v___y_4215_ = v_a_4097_;
v___y_4216_ = v_a_4098_;
v___y_4217_ = v_a_4099_;
goto v___jp_4211_;
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec_ref(v___x_4146_);
lean_dec_ref_known(v_t_4090_, 3);
lean_dec(v_f_x3f_4091_);
lean_dec_ref(v_maxType_4089_);
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4251_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4251_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
}
v___jp_4148_:
{
lean_object* v___x_4155_; 
lean_inc_ref(v___x_4146_);
lean_inc_ref(v_maxType_4089_);
v___x_4155_ = l_Lean_Meta_isExprDefEqGuarded(v_maxType_4089_, v___x_4146_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4202_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4158_ = v___x_4155_;
v_isShared_4159_ = v_isSharedCheck_4202_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4202_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
uint8_t v___x_4160_; 
v___x_4160_ = lean_unbox(v_a_4156_);
lean_dec(v_a_4156_);
if (v___x_4160_ == 0)
{
lean_object* v_toCold_4161_; lean_object* v_options_4162_; uint8_t v_hasTrace_4163_; 
lean_inc_ref(v_val_4103_);
lean_inc_ref(v_infoTrees_4102_);
lean_inc(v_ref_4101_);
lean_del_object(v___x_4158_);
lean_dec_ref_known(v_t_4090_, 3);
v_toCold_4161_ = lean_ctor_get(v___y_4153_, 0);
v_options_4162_ = lean_ctor_get(v_toCold_4161_, 2);
v_hasTrace_4163_ = lean_ctor_get_uint8(v_options_4162_, sizeof(void*)*1);
if (v_hasTrace_4163_ == 0)
{
lean_object* v_currRecDepth_4164_; lean_object* v_ref_4165_; uint16_t v_optionFlags_4166_; uint8_t v_suppressElabErrors_4167_; uint8_t v_checkDeprecated_4168_; uint8_t v_isRecordingDeps_4169_; 
lean_dec_ref(v___x_4146_);
v_currRecDepth_4164_ = lean_ctor_get(v___y_4153_, 1);
v_ref_4165_ = lean_ctor_get(v___y_4153_, 2);
v_optionFlags_4166_ = lean_ctor_get_uint16(v___y_4153_, sizeof(void*)*3);
v_suppressElabErrors_4167_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*3 + 2);
v_checkDeprecated_4168_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4169_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*3 + 4);
v___y_4105_ = v___y_4149_;
v___y_4106_ = v___y_4150_;
v___y_4107_ = v___y_4151_;
v___y_4108_ = v___y_4152_;
v_toCold_4109_ = v_toCold_4161_;
v_currRecDepth_4110_ = v_currRecDepth_4164_;
v_ref_4111_ = v_ref_4165_;
v_optionFlags_4112_ = v_optionFlags_4166_;
v_suppressElabErrors_4113_ = v_suppressElabErrors_4167_;
v_checkDeprecated_4114_ = v_checkDeprecated_4168_;
v_isRecordingDeps_4115_ = v_isRecordingDeps_4169_;
v___y_4116_ = v___y_4154_;
goto v___jp_4104_;
}
else
{
lean_object* v_currRecDepth_4170_; lean_object* v_ref_4171_; uint16_t v_optionFlags_4172_; uint8_t v_suppressElabErrors_4173_; uint8_t v_checkDeprecated_4174_; uint8_t v_isRecordingDeps_4175_; lean_object* v_inheritedTraceOptions_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; 
v_currRecDepth_4170_ = lean_ctor_get(v___y_4153_, 1);
v_ref_4171_ = lean_ctor_get(v___y_4153_, 2);
v_optionFlags_4172_ = lean_ctor_get_uint16(v___y_4153_, sizeof(void*)*3);
v_suppressElabErrors_4173_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*3 + 2);
v_checkDeprecated_4174_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4175_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*3 + 4);
v_inheritedTraceOptions_4176_ = lean_ctor_get(v_toCold_4161_, 11);
v___x_4177_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4178_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4176_, v_options_4162_, v___x_4177_);
if (v___x_4178_ == 0)
{
lean_dec_ref(v___x_4146_);
v___y_4105_ = v___y_4149_;
v___y_4106_ = v___y_4150_;
v___y_4107_ = v___y_4151_;
v___y_4108_ = v___y_4152_;
v_toCold_4109_ = v_toCold_4161_;
v_currRecDepth_4110_ = v_currRecDepth_4170_;
v_ref_4111_ = v_ref_4171_;
v_optionFlags_4112_ = v_optionFlags_4172_;
v_suppressElabErrors_4113_ = v_suppressElabErrors_4173_;
v_checkDeprecated_4114_ = v_checkDeprecated_4174_;
v_isRecordingDeps_4115_ = v_isRecordingDeps_4175_;
v___y_4116_ = v___y_4154_;
goto v___jp_4104_;
}
else
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4179_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1);
lean_inc_ref(v_val_4103_);
v___x_4180_ = l_Lean_MessageData_ofExpr(v_val_4103_);
v___x_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3);
v___x_4183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4181_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
v___x_4184_ = l_Lean_MessageData_ofExpr(v___x_4146_);
v___x_4185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4183_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
v___x_4186_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5);
v___x_4187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4185_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
lean_inc_ref(v_maxType_4089_);
v___x_4188_ = l_Lean_MessageData_ofExpr(v_maxType_4089_);
v___x_4189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4187_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4147_, v___x_4189_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_dec_ref_known(v___x_4190_, 1);
v___y_4105_ = v___y_4149_;
v___y_4106_ = v___y_4150_;
v___y_4107_ = v___y_4151_;
v___y_4108_ = v___y_4152_;
v_toCold_4109_ = v_toCold_4161_;
v_currRecDepth_4110_ = v_currRecDepth_4170_;
v_ref_4111_ = v_ref_4171_;
v_optionFlags_4112_ = v_optionFlags_4172_;
v_suppressElabErrors_4113_ = v_suppressElabErrors_4173_;
v_checkDeprecated_4114_ = v_checkDeprecated_4174_;
v_isRecordingDeps_4115_ = v_isRecordingDeps_4175_;
v___y_4116_ = v___y_4154_;
goto v___jp_4104_;
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
lean_dec_ref(v_val_4103_);
lean_dec_ref(v_infoTrees_4102_);
lean_dec(v_ref_4101_);
lean_dec_ref(v_maxType_4089_);
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4190_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4190_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
}
}
else
{
lean_object* v___x_4200_; 
lean_dec_ref(v___x_4146_);
lean_dec_ref(v_maxType_4089_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 0, v_t_4090_);
v___x_4200_ = v___x_4158_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_t_4090_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec_ref(v___x_4146_);
lean_dec_ref_known(v_t_4090_, 3);
lean_dec_ref(v_maxType_4089_);
v_a_4203_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4155_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4155_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
v___jp_4211_:
{
uint8_t v___x_4218_; 
v___x_4218_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_4146_);
if (v___x_4218_ == 0)
{
lean_dec(v_f_x3f_4091_);
v___y_4149_ = v___y_4212_;
v___y_4150_ = v___y_4213_;
v___y_4151_ = v___y_4214_;
v___y_4152_ = v___y_4215_;
v___y_4153_ = v___y_4216_;
v___y_4154_ = v___y_4217_;
goto v___jp_4148_;
}
else
{
if (lean_obj_tag(v_f_x3f_4091_) == 1)
{
lean_object* v_val_4219_; lean_object* v___x_4220_; 
v_val_4219_ = lean_ctor_get(v_f_x3f_4091_, 0);
lean_inc(v_val_4219_);
lean_dec_ref_known(v_f_x3f_4091_, 1);
v___x_4220_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(v_val_4219_, v_maxType_4089_, v_lhs_4092_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec(v_val_4219_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4229_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4229_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4229_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
uint8_t v___x_4225_; 
v___x_4225_ = lean_unbox(v_a_4221_);
lean_dec(v_a_4221_);
if (v___x_4225_ == 0)
{
lean_del_object(v___x_4223_);
v___y_4149_ = v___y_4212_;
v___y_4150_ = v___y_4213_;
v___y_4151_ = v___y_4214_;
v___y_4152_ = v___y_4215_;
v___y_4153_ = v___y_4216_;
v___y_4154_ = v___y_4217_;
goto v___jp_4148_;
}
else
{
lean_object* v___x_4227_; 
lean_dec_ref(v___x_4146_);
lean_dec_ref(v_maxType_4089_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v_t_4090_);
v___x_4227_ = v___x_4223_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_t_4090_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec_ref(v___x_4146_);
lean_dec_ref_known(v_t_4090_, 3);
lean_dec_ref(v_maxType_4089_);
v_a_4230_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4220_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4220_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
else
{
lean_dec(v_f_x3f_4091_);
v___y_4149_ = v___y_4212_;
v___y_4150_ = v___y_4213_;
v___y_4151_ = v___y_4214_;
v___y_4152_ = v___y_4215_;
v___y_4153_ = v___y_4216_;
v___y_4154_ = v___y_4217_;
goto v___jp_4148_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec_ref_known(v_t_4090_, 3);
lean_dec(v_f_x3f_4091_);
lean_dec_ref(v_maxType_4089_);
v_a_4260_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4140_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4140_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
lean_dec_ref_known(v_t_4090_, 3);
lean_dec(v_f_x3f_4091_);
lean_dec_ref(v_maxType_4089_);
v_a_4268_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___x_4138_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4138_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
v___jp_4104_:
{
lean_object* v___x_4117_; lean_object* v_ref_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4117_ = lean_box(0);
v_ref_4118_ = l_Lean_replaceRef(v_ref_4101_, v_ref_4111_);
lean_inc(v_currRecDepth_4110_);
lean_inc_ref(v_toCold_4109_);
v___x_4119_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4119_, 0, v_toCold_4109_);
lean_ctor_set(v___x_4119_, 1, v_currRecDepth_4110_);
lean_ctor_set(v___x_4119_, 2, v_ref_4118_);
lean_ctor_set_uint16(v___x_4119_, sizeof(void*)*3, v_optionFlags_4112_);
lean_ctor_set_uint8(v___x_4119_, sizeof(void*)*3 + 2, v_suppressElabErrors_4113_);
lean_ctor_set_uint8(v___x_4119_, sizeof(void*)*3 + 3, v_checkDeprecated_4114_);
lean_ctor_set_uint8(v___x_4119_, sizeof(void*)*3 + 4, v_isRecordingDeps_4115_);
v___x_4120_ = l_Lean_Elab_Term_mkCoe(v_maxType_4089_, v_val_4103_, v___x_4117_, v___x_4117_, v___x_4117_, v___x_4117_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___x_4119_, v___y_4116_);
lean_dec_ref_known(v___x_4119_, 3);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4129_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4123_ = v___x_4120_;
v_isShared_4124_ = v_isSharedCheck_4129_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4120_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4129_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4125_; lean_object* v___x_4127_; 
v___x_4125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4125_, 0, v_ref_4101_);
lean_ctor_set(v___x_4125_, 1, v_infoTrees_4102_);
lean_ctor_set(v___x_4125_, 2, v_a_4121_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 0, v___x_4125_);
v___x_4127_ = v___x_4123_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref(v_infoTrees_4102_);
lean_dec(v_ref_4101_);
v_a_4130_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4120_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4120_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
case 1:
{
lean_object* v_ref_4276_; uint8_t v_kind_4277_; lean_object* v_f_4278_; lean_object* v_lhs_4279_; lean_object* v_rhs_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_f_x3f_4091_);
v_ref_4276_ = lean_ctor_get(v_t_4090_, 0);
v_kind_4277_ = lean_ctor_get_uint8(v_t_4090_, sizeof(void*)*4);
v_f_4278_ = lean_ctor_get(v_t_4090_, 1);
v_lhs_4279_ = lean_ctor_get(v_t_4090_, 2);
v_rhs_4280_ = lean_ctor_get(v_t_4090_, 3);
v_isSharedCheck_4397_ = !lean_is_exclusive(v_t_4090_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4282_ = v_t_4090_;
v_isShared_4283_ = v_isSharedCheck_4397_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_rhs_4280_);
lean_inc(v_lhs_4279_);
lean_inc(v_f_4278_);
lean_inc(v_ref_4276_);
lean_dec(v_t_4090_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4397_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
switch(v_kind_4277_)
{
case 2:
{
lean_object* v___x_4302_; uint8_t v___x_4303_; lean_object* v___x_4304_; 
lean_del_object(v___x_4282_);
v___x_4302_ = lean_box(0);
v___x_4303_ = 0;
v___x_4304_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4089_, v_rhs_4280_, v___x_4302_, v___x_4303_, v___x_4303_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4313_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4307_ = v___x_4304_;
v_isShared_4308_ = v_isSharedCheck_4313_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4304_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4313_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4309_; lean_object* v___x_4311_; 
v___x_4309_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_4309_, 0, v_ref_4276_);
lean_ctor_set(v___x_4309_, 1, v_f_4278_);
lean_ctor_set(v___x_4309_, 2, v_lhs_4279_);
lean_ctor_set(v___x_4309_, 3, v_a_4305_);
lean_ctor_set_uint8(v___x_4309_, sizeof(void*)*4, v_kind_4277_);
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 0, v___x_4309_);
v___x_4311_ = v___x_4307_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
else
{
lean_dec_ref(v_lhs_4279_);
lean_dec_ref(v_f_4278_);
lean_dec(v_ref_4276_);
return v___x_4304_;
}
}
case 3:
{
lean_object* v___x_4314_; uint8_t v___x_4315_; lean_object* v___x_4316_; 
lean_del_object(v___x_4282_);
v___x_4314_ = lean_box(0);
v___x_4315_ = 0;
v___x_4316_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4089_, v_lhs_4279_, v___x_4314_, v___x_4315_, v___x_4315_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4325_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4319_ = v___x_4316_;
v_isShared_4320_ = v_isSharedCheck_4325_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4316_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4325_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4321_; lean_object* v___x_4323_; 
v___x_4321_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_4321_, 0, v_ref_4276_);
lean_ctor_set(v___x_4321_, 1, v_f_4278_);
lean_ctor_set(v___x_4321_, 2, v_a_4317_);
lean_ctor_set(v___x_4321_, 3, v_rhs_4280_);
lean_ctor_set_uint8(v___x_4321_, sizeof(void*)*4, v_kind_4277_);
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 0, v___x_4321_);
v___x_4323_ = v___x_4319_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
else
{
lean_dec_ref(v_rhs_4280_);
lean_dec_ref(v_f_4278_);
lean_dec(v_ref_4276_);
return v___x_4316_;
}
}
default: 
{
if (v_isPred_4093_ == 0)
{
lean_object* v___x_4326_; 
lean_inc_ref(v_maxType_4089_);
v___x_4326_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(v_f_4278_, v_maxType_4089_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; uint8_t v___x_4328_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v___x_4326_, 1);
v___x_4328_ = lean_unbox(v_a_4327_);
lean_dec(v_a_4327_);
if (v___x_4328_ == 0)
{
lean_object* v_toCold_4329_; lean_object* v_currRecDepth_4330_; lean_object* v_ref_4331_; uint16_t v_optionFlags_4332_; uint8_t v_suppressElabErrors_4333_; uint8_t v_checkDeprecated_4334_; uint8_t v_isRecordingDeps_4335_; lean_object* v___x_4336_; lean_object* v_ref_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
lean_del_object(v___x_4282_);
lean_dec_ref(v_maxType_4089_);
v_toCold_4329_ = lean_ctor_get(v_a_4098_, 0);
v_currRecDepth_4330_ = lean_ctor_get(v_a_4098_, 1);
v_ref_4331_ = lean_ctor_get(v_a_4098_, 2);
v_optionFlags_4332_ = lean_ctor_get_uint16(v_a_4098_, sizeof(void*)*3);
v_suppressElabErrors_4333_ = lean_ctor_get_uint8(v_a_4098_, sizeof(void*)*3 + 2);
v_checkDeprecated_4334_ = lean_ctor_get_uint8(v_a_4098_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4335_ = lean_ctor_get_uint8(v_a_4098_, sizeof(void*)*3 + 4);
v___x_4336_ = lean_box(0);
v_ref_4337_ = l_Lean_replaceRef(v_ref_4276_, v_ref_4331_);
lean_inc(v_currRecDepth_4330_);
lean_inc_ref(v_toCold_4329_);
v___x_4338_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4338_, 0, v_toCold_4329_);
lean_ctor_set(v___x_4338_, 1, v_currRecDepth_4330_);
lean_ctor_set(v___x_4338_, 2, v_ref_4337_);
lean_ctor_set_uint16(v___x_4338_, sizeof(void*)*3, v_optionFlags_4332_);
lean_ctor_set_uint8(v___x_4338_, sizeof(void*)*3 + 2, v_suppressElabErrors_4333_);
lean_ctor_set_uint8(v___x_4338_, sizeof(void*)*3 + 3, v_checkDeprecated_4334_);
lean_ctor_set_uint8(v___x_4338_, sizeof(void*)*3 + 4, v_isRecordingDeps_4335_);
v___x_4339_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_lhs_4279_, v___x_4336_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v___x_4338_, v_a_4099_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4341_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
lean_dec_ref_known(v___x_4339_, 1);
v___x_4341_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_rhs_4280_, v___x_4336_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v___x_4338_, v_a_4099_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v_a_4342_; uint8_t v___x_4343_; uint8_t v___x_4344_; lean_object* v___x_4345_; 
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
lean_inc(v_a_4342_);
lean_dec_ref_known(v___x_4341_, 1);
v___x_4343_ = 1;
v___x_4344_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_4277_, v___x_4343_);
v___x_4345_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v___x_4344_, v_f_4278_, v_a_4340_, v_a_4342_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v___x_4338_, v_a_4099_);
lean_dec_ref_known(v___x_4338_, 3);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; lean_object* v___x_4347_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
lean_inc(v_a_4346_);
lean_dec_ref_known(v___x_4345_, 1);
v___x_4347_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v_a_4099_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4356_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4350_ = v___x_4347_;
v_isShared_4351_ = v_isSharedCheck_4356_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4347_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4356_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; lean_object* v___x_4354_; 
v___x_4352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4352_, 0, v_ref_4276_);
lean_ctor_set(v___x_4352_, 1, v_a_4348_);
lean_ctor_set(v___x_4352_, 2, v_a_4346_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v___x_4352_);
v___x_4354_ = v___x_4350_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4352_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v_a_4346_);
lean_dec(v_ref_4276_);
v_a_4357_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4347_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4347_);
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
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec(v_ref_4276_);
v_a_4365_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4345_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4345_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v_a_4340_);
lean_dec_ref_known(v___x_4338_, 3);
lean_dec_ref(v_f_4278_);
lean_dec(v_ref_4276_);
v_a_4373_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4341_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4341_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec_ref_known(v___x_4338_, 3);
lean_dec_ref(v_rhs_4280_);
lean_dec_ref(v_f_4278_);
lean_dec(v_ref_4276_);
v_a_4381_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4339_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4339_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
else
{
goto v___jp_4284_;
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_del_object(v___x_4282_);
lean_dec_ref(v_rhs_4280_);
lean_dec_ref(v_lhs_4279_);
lean_dec_ref(v_f_4278_);
lean_dec(v_ref_4276_);
lean_dec_ref(v_maxType_4089_);
v_a_4389_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4326_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4326_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
else
{
goto v___jp_4284_;
}
}
}
v___jp_4284_:
{
uint8_t v___x_4285_; lean_object* v___x_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; 
v___x_4285_ = 1;
lean_inc_ref(v_f_4278_);
v___x_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4286_, 0, v_f_4278_);
v___x_4287_ = 0;
lean_inc_ref(v___x_4286_);
lean_inc_ref(v_maxType_4089_);
v___x_4288_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4089_, v_lhs_4279_, v___x_4286_, v___x_4285_, v___x_4287_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4290_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v___x_4288_, 1);
v___x_4290_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4089_, v_rhs_4280_, v___x_4286_, v___x_4287_, v___x_4287_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4301_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4293_ = v___x_4290_;
v_isShared_4294_ = v_isSharedCheck_4301_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4290_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4301_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 3, v_a_4291_);
lean_ctor_set(v___x_4282_, 2, v_a_4289_);
v___x_4296_ = v___x_4282_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_ref_4276_);
lean_ctor_set(v_reuseFailAlloc_4300_, 1, v_f_4278_);
lean_ctor_set(v_reuseFailAlloc_4300_, 2, v_a_4289_);
lean_ctor_set(v_reuseFailAlloc_4300_, 3, v_a_4291_);
lean_ctor_set_uint8(v_reuseFailAlloc_4300_, sizeof(void*)*4, v_kind_4277_);
v___x_4296_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v___x_4298_; 
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 0, v___x_4296_);
v___x_4298_ = v___x_4293_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4296_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_dec(v_a_4289_);
lean_del_object(v___x_4282_);
lean_dec_ref(v_f_4278_);
lean_dec(v_ref_4276_);
return v___x_4290_;
}
}
else
{
lean_dec_ref_known(v___x_4286_, 1);
lean_del_object(v___x_4282_);
lean_dec_ref(v_rhs_4280_);
lean_dec_ref(v_f_4278_);
lean_dec(v_ref_4276_);
lean_dec_ref(v_maxType_4089_);
return v___x_4288_;
}
}
}
}
case 2:
{
lean_object* v_ref_4398_; lean_object* v_f_4399_; lean_object* v_arg_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_f_x3f_4091_);
v_ref_4398_ = lean_ctor_get(v_t_4090_, 0);
v_f_4399_ = lean_ctor_get(v_t_4090_, 1);
v_arg_4400_ = lean_ctor_get(v_t_4090_, 2);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_t_4090_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4402_ = v_t_4090_;
v_isShared_4403_ = v_isSharedCheck_4418_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_arg_4400_);
lean_inc(v_f_4399_);
lean_inc(v_ref_4398_);
lean_dec(v_t_4090_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4418_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; uint8_t v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = lean_box(0);
v___x_4405_ = 0;
v___x_4406_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4089_, v_arg_4400_, v___x_4404_, v___x_4405_, v___x_4405_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4417_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4409_ = v___x_4406_;
v_isShared_4410_ = v_isSharedCheck_4417_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4406_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4417_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 2, v_a_4407_);
v___x_4412_ = v___x_4402_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_ref_4398_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_f_4399_);
lean_ctor_set(v_reuseFailAlloc_4416_, 2, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
lean_object* v___x_4414_; 
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4412_);
v___x_4414_ = v___x_4409_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4412_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
else
{
lean_del_object(v___x_4402_);
lean_dec_ref(v_f_4399_);
lean_dec(v_ref_4398_);
return v___x_4406_;
}
}
}
default: 
{
lean_object* v_macroName_4419_; lean_object* v_stx_4420_; lean_object* v_stx_x27_4421_; lean_object* v_nested_4422_; lean_object* v_toCold_4423_; lean_object* v_currRecDepth_4424_; lean_object* v_ref_4425_; uint16_t v_optionFlags_4426_; uint8_t v_suppressElabErrors_4427_; uint8_t v_checkDeprecated_4428_; uint8_t v_isRecordingDeps_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___f_4432_; lean_object* v_ref_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_macroName_4419_ = lean_ctor_get(v_t_4090_, 0);
lean_inc(v_macroName_4419_);
v_stx_4420_ = lean_ctor_get(v_t_4090_, 1);
lean_inc_n(v_stx_4420_, 2);
v_stx_x27_4421_ = lean_ctor_get(v_t_4090_, 2);
lean_inc_n(v_stx_x27_4421_, 2);
v_nested_4422_ = lean_ctor_get(v_t_4090_, 3);
lean_inc_ref(v_nested_4422_);
lean_dec_ref_known(v_t_4090_, 4);
v_toCold_4423_ = lean_ctor_get(v_a_4098_, 0);
v_currRecDepth_4424_ = lean_ctor_get(v_a_4098_, 1);
v_ref_4425_ = lean_ctor_get(v_a_4098_, 2);
v_optionFlags_4426_ = lean_ctor_get_uint16(v_a_4098_, sizeof(void*)*3);
v_suppressElabErrors_4427_ = lean_ctor_get_uint8(v_a_4098_, sizeof(void*)*3 + 2);
v_checkDeprecated_4428_ = lean_ctor_get_uint8(v_a_4098_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4429_ = lean_ctor_get_uint8(v_a_4098_, sizeof(void*)*3 + 4);
v___x_4430_ = lean_box(v_lhs_4092_);
v___x_4431_ = lean_box(v_isPred_4093_);
v___f_4432_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4432_, 0, v_maxType_4089_);
lean_closure_set(v___f_4432_, 1, v_nested_4422_);
lean_closure_set(v___f_4432_, 2, v_f_x3f_4091_);
lean_closure_set(v___f_4432_, 3, v___x_4430_);
lean_closure_set(v___f_4432_, 4, v___x_4431_);
lean_closure_set(v___f_4432_, 5, v_macroName_4419_);
lean_closure_set(v___f_4432_, 6, v_stx_4420_);
lean_closure_set(v___f_4432_, 7, v_stx_x27_4421_);
v_ref_4433_ = l_Lean_replaceRef(v_stx_4420_, v_ref_4425_);
lean_inc(v_currRecDepth_4424_);
lean_inc_ref(v_toCold_4423_);
v___x_4434_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4434_, 0, v_toCold_4423_);
lean_ctor_set(v___x_4434_, 1, v_currRecDepth_4424_);
lean_ctor_set(v___x_4434_, 2, v_ref_4433_);
lean_ctor_set_uint16(v___x_4434_, sizeof(void*)*3, v_optionFlags_4426_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*3 + 2, v_suppressElabErrors_4427_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*3 + 3, v_checkDeprecated_4428_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*3 + 4, v_isRecordingDeps_4429_);
v___x_4435_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_stx_4420_, v_stx_x27_4421_, v___f_4432_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v___x_4434_, v_a_4099_);
lean_dec_ref_known(v___x_4434_, 3);
return v___x_4435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(lean_object* v_t_4436_, lean_object* v_maxType_4437_, uint8_t v_isPred_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v___x_4446_; uint8_t v___x_4447_; lean_object* v___x_4448_; 
v___x_4446_ = lean_box(0);
v___x_4447_ = 0;
v___x_4448_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4437_, v_t_4436_, v___x_4446_, v___x_4447_, v_isPred_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe___boxed(lean_object* v_t_4449_, lean_object* v_maxType_4450_, lean_object* v_isPred_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_){
_start:
{
uint8_t v_isPred_boxed_4459_; lean_object* v_res_4460_; 
v_isPred_boxed_4459_ = lean_unbox(v_isPred_4451_);
v_res_4460_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v_t_4449_, v_maxType_4450_, v_isPred_boxed_4459_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_);
lean_dec(v_a_4457_);
lean_dec_ref(v_a_4456_);
lean_dec(v_a_4455_);
lean_dec_ref(v_a_4454_);
lean_dec(v_a_4453_);
lean_dec_ref(v_a_4452_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___boxed(lean_object* v_tree_4461_, lean_object* v_expectedType_x3f_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_tree_4461_, v_expectedType_x3f_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___boxed(lean_object* v_maxType_4471_, lean_object* v_t_4472_, lean_object* v_f_x3f_4473_, lean_object* v_lhs_4474_, lean_object* v_isPred_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
uint8_t v_lhs_boxed_4483_; uint8_t v_isPred_boxed_4484_; lean_object* v_res_4485_; 
v_lhs_boxed_4483_ = lean_unbox(v_lhs_4474_);
v_isPred_boxed_4484_ = lean_unbox(v_isPred_4475_);
v_res_4485_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4471_, v_t_4472_, v_f_x3f_4473_, v_lhs_boxed_4483_, v_isPred_boxed_4484_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr_spec__2(lean_object* v_msg_4486_){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = l_Lean_instInhabitedExpr;
v___x_4488_ = lean_panic_fn_borrowed(v___x_4487_, v_msg_4486_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0(lean_object* v_cls_4489_, lean_object* v_msg_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v_cls_4489_, v_msg_4490_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___boxed(lean_object* v_cls_4499_, lean_object* v_msg_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0(v_cls_4499_, v_msg_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp(lean_object* v_stx_4509_, lean_object* v_expectedType_x3f_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v___x_4518_; 
v___x_4518_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v_stx_4509_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v___x_4520_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
lean_dec_ref_known(v___x_4518_, 1);
v___x_4520_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_a_4519_, v_expectedType_x3f_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
return v___x_4520_;
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_dec(v_expectedType_x3f_4510_);
v_a_4521_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4518_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4518_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp___boxed(lean_object* v_stx_4529_, lean_object* v_expectedType_x3f_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Lean_Elab_Term_Op_elabOp(v_stx_4529_, v_expectedType_x3f_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp(lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Lean_Elab_Term_Op_elabOp(v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp___boxed(lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_Elab_Term_Op_elabBinOp(v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
lean_dec(v_a_4556_);
lean_dec_ref(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_a_4553_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1(){
_start:
{
lean_object* v___f_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___f_4568_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4569_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4570_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1));
v___x_4571_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2));
v___x_4572_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4569_, v___x_4570_, v___x_4571_, v___f_4568_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___boxed(lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1();
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3(){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4601_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2));
v___x_4602_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__6));
v___x_4603_ = l_Lean_addBuiltinDeclarationRanges(v___x_4601_, v___x_4602_);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___boxed(lean_object* v_a_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3();
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy(lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
lean_object* v___x_4615_; 
v___x_4615_ = l_Lean_Elab_Term_Op_elabOp(v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy___boxed(lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Lean_Elab_Term_Op_elabBinOpLazy(v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
lean_dec(v_a_4619_);
lean_dec_ref(v_a_4618_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1(){
_start:
{
lean_object* v___f_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___f_4634_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4635_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4636_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3));
v___x_4637_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1));
v___x_4638_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4635_, v___x_4636_, v___x_4637_, v___f_4634_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___boxed(lean_object* v_a_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1();
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3(){
_start:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4667_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1));
v___x_4668_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__6));
v___x_4669_ = l_Lean_addBuiltinDeclarationRanges(v___x_4667_, v___x_4668_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___boxed(lean_object* v_a_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3();
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact(lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_){
_start:
{
lean_object* v___x_4681_; 
v___x_4681_ = l_Lean_Elab_Term_Op_elabOp(v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact___boxed(lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Lean_Elab_Term_Op_elabLeftact(v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec_ref(v_a_4686_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1(){
_start:
{
lean_object* v___f_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___f_4700_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4701_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4702_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7));
v___x_4703_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1));
v___x_4704_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4701_, v___x_4702_, v___x_4703_, v___f_4700_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___boxed(lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1();
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3(){
_start:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4733_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1));
v___x_4734_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__6));
v___x_4735_ = l_Lean_addBuiltinDeclarationRanges(v___x_4733_, v___x_4734_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___boxed(lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3();
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact(lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l_Lean_Elab_Term_Op_elabOp(v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact___boxed(lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_Elab_Term_Op_elabRightact(v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1(){
_start:
{
lean_object* v___f_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; 
v___f_4766_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4767_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4768_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9));
v___x_4769_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1));
v___x_4770_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4767_, v___x_4768_, v___x_4769_, v___f_4766_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___boxed(lean_object* v_a_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1();
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3(){
_start:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4799_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1));
v___x_4800_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__6));
v___x_4801_ = l_Lean_addBuiltinDeclarationRanges(v___x_4799_, v___x_4800_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___boxed(lean_object* v_a_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3();
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp(lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = l_Lean_Elab_Term_Op_elabOp(v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp___boxed(lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l_Lean_Elab_Term_Op_elabUnOp(v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_);
lean_dec(v_a_4821_);
lean_dec_ref(v_a_4820_);
lean_dec(v_a_4819_);
lean_dec_ref(v_a_4818_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1(){
_start:
{
lean_object* v___f_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___f_4832_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4833_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4834_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5));
v___x_4835_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1));
v___x_4836_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4833_, v___x_4834_, v___x_4835_, v___f_4832_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___boxed(lean_object* v_a_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1();
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3(){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4865_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1));
v___x_4866_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__6));
v___x_4867_ = l_Lean_addBuiltinDeclarationRanges(v___x_4865_, v___x_4866_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___boxed(lean_object* v_a_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3();
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0(lean_object* v_k_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v___x_4878_; 
lean_inc(v___y_4872_);
lean_inc_ref(v___y_4871_);
v___x_4878_ = lean_apply_7(v_k_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, lean_box(0));
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0___boxed(lean_object* v_k_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0(v_k_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
lean_dec(v___y_4881_);
lean_dec_ref(v___y_4880_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(lean_object* v_k_4888_, uint8_t v_allowLevelAssignments_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
lean_object* v___f_4897_; lean_object* v___x_4898_; 
lean_inc(v___y_4891_);
lean_inc_ref(v___y_4890_);
v___f_4897_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4897_, 0, v_k_4888_);
lean_closure_set(v___f_4897_, 1, v___y_4890_);
lean_closure_set(v___f_4897_, 2, v___y_4891_);
v___x_4898_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_4889_, v___f_4897_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
if (lean_obj_tag(v___x_4898_) == 0)
{
return v___x_4898_;
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___boxed(lean_object* v_k_4907_, lean_object* v_allowLevelAssignments_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4916_; lean_object* v_res_4917_; 
v_allowLevelAssignments_boxed_4916_ = lean_unbox(v_allowLevelAssignments_4908_);
v_res_4917_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v_k_4907_, v_allowLevelAssignments_boxed_4916_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_);
lean_dec(v___y_4914_);
lean_dec_ref(v___y_4913_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0(lean_object* v_00_u03b1_4918_, lean_object* v_k_4919_, uint8_t v_allowLevelAssignments_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v_k_4919_, v_allowLevelAssignments_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___boxed(lean_object* v_00_u03b1_4929_, lean_object* v_k_4930_, lean_object* v_allowLevelAssignments_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4939_; lean_object* v_res_4940_; 
v_allowLevelAssignments_boxed_4939_ = lean_unbox(v_allowLevelAssignments_4931_);
v_res_4940_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0(v_00_u03b1_4929_, v_k_4930_, v_allowLevelAssignments_boxed_4939_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0(lean_object* v_a_4941_, lean_object* v___x_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = l_Lean_Meta_isExprDefEq(v_a_4941_, v___x_4942_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0___boxed(lean_object* v_a_4951_, lean_object* v___x_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0(v_a_4951_, v___x_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
return v_res_4960_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0(void){
_start:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4961_ = lean_box(0);
v___x_4962_ = l_Lean_mkSort(v___x_4961_);
return v___x_4962_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3(void){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4966_ = lean_box(0);
v___x_4967_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__2));
v___x_4968_ = l_Lean_mkConst(v___x_4967_, v___x_4966_);
return v___x_4968_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4(void){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4969_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3);
v___x_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4969_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(uint8_t v_noProp_4971_, lean_object* v_e_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_){
_start:
{
if (v_noProp_4971_ == 0)
{
lean_object* v___x_4980_; 
v___x_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4980_, 0, v_e_4972_);
return v___x_4980_;
}
else
{
lean_object* v___x_4981_; 
lean_inc(v_a_4978_);
lean_inc_ref(v_a_4977_);
lean_inc(v_a_4976_);
lean_inc_ref(v_a_4975_);
lean_inc_ref(v_e_4972_);
v___x_4981_ = lean_infer_type(v_e_4972_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4983_; lean_object* v___f_4984_; uint8_t v___x_4985_; lean_object* v___x_4986_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_a_4982_);
lean_dec_ref_known(v___x_4981_, 1);
v___x_4983_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0);
v___f_4984_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4984_, 0, v_a_4982_);
lean_closure_set(v___f_4984_, 1, v___x_4983_);
v___x_4985_ = 0;
v___x_4986_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v___f_4984_, v___x_4985_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4998_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4989_ = v___x_4986_;
v_isShared_4990_ = v_isSharedCheck_4998_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4986_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4998_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
uint8_t v___x_4991_; 
v___x_4991_ = lean_unbox(v_a_4987_);
lean_dec(v_a_4987_);
if (v___x_4991_ == 0)
{
lean_object* v___x_4993_; 
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 0, v_e_4972_);
v___x_4993_ = v___x_4989_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_e_4972_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
else
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
lean_del_object(v___x_4989_);
v___x_4995_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4);
v___x_4996_ = lean_box(0);
v___x_4997_ = l_Lean_Elab_Term_ensureHasType(v___x_4995_, v_e_4972_, v___x_4996_, v___x_4996_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_);
return v___x_4997_;
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec_ref(v_e_4972_);
v_a_4999_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4986_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4986_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
else
{
lean_dec_ref(v_e_4972_);
return v___x_4981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___boxed(lean_object* v_noProp_5007_, lean_object* v_e_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_){
_start:
{
uint8_t v_noProp_boxed_5016_; lean_object* v_res_5017_; 
v_noProp_boxed_5016_ = lean_unbox(v_noProp_5007_);
v_res_5017_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_boxed_5016_, v_e_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
lean_dec(v_a_5014_);
lean_dec_ref(v_a_5013_);
lean_dec(v_a_5012_);
lean_dec_ref(v_a_5011_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0(lean_object* v_val_5018_, lean_object* v___x_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
lean_object* v___x_5027_; 
v___x_5027_ = l_Lean_Meta_isExprDefEq(v_val_5018_, v___x_5019_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0___boxed(lean_object* v_val_5028_, lean_object* v___x_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Lean_Elab_Term_Op_elabBinRelCore___lam__0(v_val_5028_, v___x_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v___y_5031_);
lean_dec_ref(v___y_5030_);
return v_res_5037_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2(void){
_start:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5042_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
v___x_5043_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2));
v___x_5044_ = l_Lean_Name_append(v___x_5043_, v___x_5042_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1(lean_object* v___x_5045_, lean_object* v___x_5046_, lean_object* v_stx_5047_, lean_object* v_val_5048_, uint8_t v_noProp_5049_, lean_object* v___x_5050_, lean_object* v_expectedType_x3f_5051_, uint8_t v___x_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v_toCold_5060_; lean_object* v_currRecDepth_5061_; lean_object* v_ref_5062_; uint16_t v_optionFlags_5063_; uint8_t v_suppressElabErrors_5064_; uint8_t v_checkDeprecated_5065_; uint8_t v_isRecordingDeps_5066_; lean_object* v_ref_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
v_toCold_5060_ = lean_ctor_get(v___y_5057_, 0);
v_currRecDepth_5061_ = lean_ctor_get(v___y_5057_, 1);
v_ref_5062_ = lean_ctor_get(v___y_5057_, 2);
v_optionFlags_5063_ = lean_ctor_get_uint16(v___y_5057_, sizeof(void*)*3);
v_suppressElabErrors_5064_ = lean_ctor_get_uint8(v___y_5057_, sizeof(void*)*3 + 2);
v_checkDeprecated_5065_ = lean_ctor_get_uint8(v___y_5057_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5066_ = lean_ctor_get_uint8(v___y_5057_, sizeof(void*)*3 + 4);
v_ref_5067_ = l_Lean_replaceRef(v___x_5045_, v_ref_5062_);
lean_inc(v_currRecDepth_5061_);
lean_inc_ref(v_toCold_5060_);
v___x_5068_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5068_, 0, v_toCold_5060_);
lean_ctor_set(v___x_5068_, 1, v_currRecDepth_5061_);
lean_ctor_set(v___x_5068_, 2, v_ref_5067_);
lean_ctor_set_uint16(v___x_5068_, sizeof(void*)*3, v_optionFlags_5063_);
lean_ctor_set_uint8(v___x_5068_, sizeof(void*)*3 + 2, v_suppressElabErrors_5064_);
lean_ctor_set_uint8(v___x_5068_, sizeof(void*)*3 + 3, v_checkDeprecated_5065_);
lean_ctor_set_uint8(v___x_5068_, sizeof(void*)*3 + 4, v_isRecordingDeps_5066_);
lean_inc(v___x_5045_);
v___x_5069_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v___x_5045_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___x_5068_, v___y_5058_);
lean_dec_ref_known(v___x_5068_, 3);
if (lean_obj_tag(v___x_5069_) == 0)
{
lean_object* v_a_5070_; lean_object* v_ref_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v_a_5070_ = lean_ctor_get(v___x_5069_, 0);
lean_inc(v_a_5070_);
lean_dec_ref_known(v___x_5069_, 1);
v_ref_5071_ = l_Lean_replaceRef(v___x_5046_, v_ref_5062_);
lean_inc(v_currRecDepth_5061_);
lean_inc_ref(v_toCold_5060_);
v___x_5072_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5072_, 0, v_toCold_5060_);
lean_ctor_set(v___x_5072_, 1, v_currRecDepth_5061_);
lean_ctor_set(v___x_5072_, 2, v_ref_5071_);
lean_ctor_set_uint16(v___x_5072_, sizeof(void*)*3, v_optionFlags_5063_);
lean_ctor_set_uint8(v___x_5072_, sizeof(void*)*3 + 2, v_suppressElabErrors_5064_);
lean_ctor_set_uint8(v___x_5072_, sizeof(void*)*3 + 3, v_checkDeprecated_5065_);
lean_ctor_set_uint8(v___x_5072_, sizeof(void*)*3 + 4, v_isRecordingDeps_5066_);
lean_inc(v___x_5046_);
v___x_5073_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v___x_5046_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___x_5072_, v___y_5058_);
lean_dec_ref_known(v___x_5072_, 3);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v_a_5074_; uint8_t v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___x_5134_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc_n(v_a_5074_, 2);
lean_dec_ref_known(v___x_5073_, 1);
v___x_5075_ = 0;
lean_inc(v_a_5070_);
lean_inc_ref(v_val_5048_);
v___x_5076_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_5076_, 0, v_stx_5047_);
lean_ctor_set(v___x_5076_, 1, v_val_5048_);
lean_ctor_set(v___x_5076_, 2, v_a_5070_);
lean_ctor_set(v___x_5076_, 3, v_a_5074_);
lean_ctor_set_uint8(v___x_5076_, sizeof(void*)*4, v___x_5075_);
v___x_5077_ = lean_box(0);
lean_inc_ref(v___x_5076_);
v___x_5134_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v___x_5076_, v___x_5077_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_options_5135_; lean_object* v_a_5136_; lean_object* v_inheritedTraceOptions_5137_; uint8_t v_hasTrace_5138_; lean_object* v___x_5139_; uint8_t v___y_5141_; lean_object* v_maxType_5142_; lean_object* v___y_5143_; lean_object* v___y_5144_; lean_object* v___y_5145_; lean_object* v___y_5146_; lean_object* v___y_5147_; lean_object* v___y_5148_; lean_object* v___y_5188_; lean_object* v___y_5189_; lean_object* v___y_5190_; lean_object* v___y_5191_; lean_object* v___y_5192_; lean_object* v___y_5193_; lean_object* v___y_5213_; lean_object* v___y_5214_; 
v_options_5135_ = lean_ctor_get(v_toCold_5060_, 2);
v_a_5136_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5136_);
lean_dec_ref_known(v___x_5134_, 1);
v_inheritedTraceOptions_5137_ = lean_ctor_get(v_toCold_5060_, 11);
v_hasTrace_5138_ = lean_ctor_get_uint8(v_options_5135_, sizeof(void*)*1);
v___x_5139_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
if (v_hasTrace_5138_ == 0)
{
v___y_5188_ = v___y_5053_;
v___y_5189_ = v___y_5054_;
v___y_5190_ = v___y_5055_;
v___y_5191_ = v___y_5056_;
v___y_5192_ = v___y_5057_;
v___y_5193_ = v___y_5058_;
goto v___jp_5187_;
}
else
{
lean_object* v___x_5225_; uint8_t v___x_5226_; 
v___x_5225_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2, &l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2_once, _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2);
v___x_5226_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5137_, v_options_5135_, v___x_5225_);
if (v___x_5226_ == 0)
{
v___y_5188_ = v___y_5053_;
v___y_5189_ = v___y_5054_;
v___y_5190_ = v___y_5055_;
v___y_5191_ = v___y_5056_;
v___y_5192_ = v___y_5057_;
v___y_5193_ = v___y_5058_;
goto v___jp_5187_;
}
else
{
lean_object* v_max_x3f_5227_; uint8_t v_hasUncomparable_5228_; uint8_t v_hasUnknown_5229_; lean_object* v___y_5231_; lean_object* v___y_5232_; lean_object* v___x_5241_; lean_object* v___y_5243_; 
v_max_x3f_5227_ = lean_ctor_get(v_a_5136_, 0);
v_hasUncomparable_5228_ = lean_ctor_get_uint8(v_a_5136_, sizeof(void*)*1);
v_hasUnknown_5229_ = lean_ctor_get_uint8(v_a_5136_, sizeof(void*)*1 + 1);
v___x_5241_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8);
if (v_hasUncomparable_5228_ == 0)
{
lean_object* v___x_5251_; 
v___x_5251_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_5243_ = v___x_5251_;
goto v___jp_5242_;
}
else
{
lean_object* v___x_5252_; 
v___x_5252_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_5243_ = v___x_5252_;
goto v___jp_5242_;
}
v___jp_5230_:
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
lean_inc_ref(v___y_5232_);
v___x_5233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5233_, 0, v___y_5232_);
v___x_5234_ = l_Lean_MessageData_ofFormat(v___x_5233_);
v___x_5235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5235_, 0, v___y_5231_);
lean_ctor_set(v___x_5235_, 1, v___x_5234_);
v___x_5236_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3);
v___x_5237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5235_);
lean_ctor_set(v___x_5237_, 1, v___x_5236_);
if (lean_obj_tag(v_max_x3f_5227_) == 0)
{
lean_object* v___x_5238_; 
v___x_5238_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6);
v___y_5213_ = v___x_5237_;
v___y_5214_ = v___x_5238_;
goto v___jp_5212_;
}
else
{
lean_object* v_val_5239_; lean_object* v___x_5240_; 
v_val_5239_ = lean_ctor_get(v_max_x3f_5227_, 0);
lean_inc(v_val_5239_);
v___x_5240_ = l_Lean_MessageData_ofExpr(v_val_5239_);
v___y_5213_ = v___x_5237_;
v___y_5214_ = v___x_5240_;
goto v___jp_5212_;
}
}
v___jp_5242_:
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; 
lean_inc_ref(v___y_5243_);
v___x_5244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5244_, 0, v___y_5243_);
v___x_5245_ = l_Lean_MessageData_ofFormat(v___x_5244_);
v___x_5246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5246_, 0, v___x_5241_);
lean_ctor_set(v___x_5246_, 1, v___x_5245_);
v___x_5247_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10);
v___x_5248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5246_);
lean_ctor_set(v___x_5248_, 1, v___x_5247_);
if (v_hasUnknown_5229_ == 0)
{
lean_object* v___x_5249_; 
v___x_5249_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_5231_ = v___x_5248_;
v___y_5232_ = v___x_5249_;
goto v___jp_5230_;
}
else
{
lean_object* v___x_5250_; 
v___x_5250_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_5231_ = v___x_5248_;
v___y_5232_ = v___x_5250_;
goto v___jp_5230_;
}
}
}
}
v___jp_5140_:
{
lean_object* v___x_5149_; 
v___x_5149_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v___x_5076_, v_maxType_5142_, v___y_5141_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; lean_object* v___x_5151_; 
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_a_5150_);
lean_dec_ref_known(v___x_5149_, 1);
v___x_5151_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5150_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_toCold_5152_; lean_object* v_options_5153_; uint8_t v_hasTrace_5154_; 
v_toCold_5152_ = lean_ctor_get(v___y_5147_, 0);
v_options_5153_ = lean_ctor_get(v_toCold_5152_, 2);
v_hasTrace_5154_ = lean_ctor_get_uint8(v_options_5153_, sizeof(void*)*1);
if (v_hasTrace_5154_ == 0)
{
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
return v___x_5151_;
}
else
{
lean_object* v_a_5155_; lean_object* v_inheritedTraceOptions_5156_; lean_object* v___x_5157_; uint8_t v___x_5158_; 
v_a_5155_ = lean_ctor_get(v___x_5151_, 0);
v_inheritedTraceOptions_5156_ = lean_ctor_get(v_toCold_5152_, 11);
v___x_5157_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2, &l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2_once, _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2);
v___x_5158_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5156_, v_options_5153_, v___x_5157_);
if (v___x_5158_ == 0)
{
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
return v___x_5151_;
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
lean_inc_n(v_a_5155_, 2);
lean_dec_ref_known(v___x_5151_, 1);
v___x_5159_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1);
v___x_5160_ = l_Lean_MessageData_ofExpr(v_a_5155_);
v___x_5161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5159_);
lean_ctor_set(v___x_5161_, 1, v___x_5160_);
v___x_5162_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_5139_, v___x_5161_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5169_; 
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5169_ == 0)
{
lean_object* v_unused_5170_; 
v_unused_5170_ = lean_ctor_get(v___x_5162_, 0);
lean_dec(v_unused_5170_);
v___x_5164_ = v___x_5162_;
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
else
{
lean_dec(v___x_5162_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5167_; 
if (v_isShared_5165_ == 0)
{
lean_ctor_set(v___x_5164_, 0, v_a_5155_);
v___x_5167_ = v___x_5164_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5155_);
v___x_5167_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
return v___x_5167_;
}
}
}
else
{
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5178_; 
lean_dec(v_a_5155_);
v_a_5171_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5173_ = v___x_5162_;
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5162_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5176_; 
if (v_isShared_5174_ == 0)
{
v___x_5176_ = v___x_5173_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
return v___x_5176_;
}
}
}
}
}
}
else
{
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
return v___x_5151_;
}
}
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
v_a_5179_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5149_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5149_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
v___jp_5187_:
{
uint8_t v_hasUncomparable_5194_; 
v_hasUncomparable_5194_ = lean_ctor_get_uint8(v_a_5136_, sizeof(void*)*1);
if (v_hasUncomparable_5194_ == 0)
{
lean_object* v_max_x3f_5195_; 
v_max_x3f_5195_ = lean_ctor_get(v_a_5136_, 0);
lean_inc(v_max_x3f_5195_);
lean_dec(v_a_5136_);
if (lean_obj_tag(v_max_x3f_5195_) == 0)
{
lean_dec_ref_known(v___x_5076_, 4);
v___y_5079_ = v___y_5191_;
v___y_5080_ = v___y_5193_;
v___y_5081_ = v___y_5192_;
v___y_5082_ = v___y_5188_;
v___y_5083_ = v___y_5190_;
v___y_5084_ = v___y_5189_;
goto v___jp_5078_;
}
else
{
lean_object* v_val_5196_; uint8_t v___x_5197_; 
lean_dec(v_a_5074_);
lean_dec(v_a_5070_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
lean_dec(v___x_5046_);
lean_dec(v___x_5045_);
v_val_5196_ = lean_ctor_get(v_max_x3f_5195_, 0);
lean_inc(v_val_5196_);
lean_dec_ref_known(v_max_x3f_5195_, 1);
v___x_5197_ = 1;
if (v_noProp_5049_ == 0)
{
v___y_5141_ = v___x_5197_;
v_maxType_5142_ = v_val_5196_;
v___y_5143_ = v___y_5188_;
v___y_5144_ = v___y_5189_;
v___y_5145_ = v___y_5190_;
v___y_5146_ = v___y_5191_;
v___y_5147_ = v___y_5192_;
v___y_5148_ = v___y_5193_;
goto v___jp_5140_;
}
else
{
lean_object* v___x_5198_; lean_object* v___f_5199_; lean_object* v___x_5200_; 
v___x_5198_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0);
lean_inc(v_val_5196_);
v___f_5199_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5199_, 0, v_val_5196_);
lean_closure_set(v___f_5199_, 1, v___x_5198_);
v___x_5200_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v___f_5199_, v___x_5052_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5201_; uint8_t v___x_5202_; 
v_a_5201_ = lean_ctor_get(v___x_5200_, 0);
lean_inc(v_a_5201_);
lean_dec_ref_known(v___x_5200_, 1);
v___x_5202_ = lean_unbox(v_a_5201_);
lean_dec(v_a_5201_);
if (v___x_5202_ == 0)
{
v___y_5141_ = v___x_5197_;
v_maxType_5142_ = v_val_5196_;
v___y_5143_ = v___y_5188_;
v___y_5144_ = v___y_5189_;
v___y_5145_ = v___y_5190_;
v___y_5146_ = v___y_5191_;
v___y_5147_ = v___y_5192_;
v___y_5148_ = v___y_5193_;
goto v___jp_5140_;
}
else
{
lean_object* v___x_5203_; 
lean_dec(v_val_5196_);
v___x_5203_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3);
v___y_5141_ = v___x_5197_;
v_maxType_5142_ = v___x_5203_;
v___y_5143_ = v___y_5188_;
v___y_5144_ = v___y_5189_;
v___y_5145_ = v___y_5190_;
v___y_5146_ = v___y_5191_;
v___y_5147_ = v___y_5192_;
v___y_5148_ = v___y_5193_;
goto v___jp_5140_;
}
}
else
{
lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5211_; 
lean_dec(v_val_5196_);
lean_dec(v___y_5193_);
lean_dec_ref(v___y_5192_);
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
lean_dec_ref_known(v___x_5076_, 4);
v_a_5204_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5211_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5211_ == 0)
{
v___x_5206_ = v___x_5200_;
v_isShared_5207_ = v_isSharedCheck_5211_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v___x_5200_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5211_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5209_; 
if (v_isShared_5207_ == 0)
{
v___x_5209_ = v___x_5206_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v_a_5204_);
v___x_5209_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
return v___x_5209_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5136_);
lean_dec_ref_known(v___x_5076_, 4);
v___y_5079_ = v___y_5191_;
v___y_5080_ = v___y_5193_;
v___y_5081_ = v___y_5192_;
v___y_5082_ = v___y_5188_;
v___y_5083_ = v___y_5190_;
v___y_5084_ = v___y_5189_;
goto v___jp_5078_;
}
}
v___jp_5212_:
{
lean_object* v___x_5215_; lean_object* v___x_5216_; 
v___x_5215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5215_, 0, v___y_5213_);
lean_ctor_set(v___x_5215_, 1, v___y_5214_);
v___x_5216_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_5139_, v___x_5215_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_dec_ref_known(v___x_5216_, 1);
v___y_5188_ = v___y_5053_;
v___y_5189_ = v___y_5054_;
v___y_5190_ = v___y_5055_;
v___y_5191_ = v___y_5056_;
v___y_5192_ = v___y_5057_;
v___y_5193_ = v___y_5058_;
goto v___jp_5187_;
}
else
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5224_; 
lean_dec(v_a_5136_);
lean_dec_ref_known(v___x_5076_, 4);
lean_dec(v_a_5074_);
lean_dec(v_a_5070_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
lean_dec(v___x_5046_);
lean_dec(v___x_5045_);
v_a_5217_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5219_ = v___x_5216_;
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_a_5217_);
lean_dec(v___x_5216_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5222_; 
if (v_isShared_5220_ == 0)
{
v___x_5222_ = v___x_5219_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
}
else
{
lean_object* v_a_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5260_; 
lean_dec_ref_known(v___x_5076_, 4);
lean_dec(v_a_5074_);
lean_dec(v_a_5070_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
lean_dec(v___x_5046_);
lean_dec(v___x_5045_);
v_a_5253_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5260_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5260_ == 0)
{
v___x_5255_ = v___x_5134_;
v_isShared_5256_ = v_isSharedCheck_5260_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_a_5253_);
lean_dec(v___x_5134_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5260_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
lean_object* v___x_5258_; 
if (v_isShared_5256_ == 0)
{
v___x_5258_ = v___x_5255_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v_a_5253_);
v___x_5258_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
return v___x_5258_;
}
}
}
v___jp_5078_:
{
lean_object* v___x_5085_; 
v___x_5085_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5070_, v___y_5082_, v___y_5084_, v___y_5083_, v___y_5079_, v___y_5081_, v___y_5080_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5087_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref_known(v___x_5085_, 1);
v___x_5087_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5074_, v___y_5082_, v___y_5084_, v___y_5083_, v___y_5079_, v___y_5081_, v___y_5080_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v_toCold_5089_; lean_object* v_currRecDepth_5090_; lean_object* v_ref_5091_; uint16_t v_optionFlags_5092_; uint8_t v_suppressElabErrors_5093_; uint8_t v_checkDeprecated_5094_; uint8_t v_isRecordingDeps_5095_; lean_object* v_ref_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5088_);
lean_dec_ref_known(v___x_5087_, 1);
v_toCold_5089_ = lean_ctor_get(v___y_5081_, 0);
v_currRecDepth_5090_ = lean_ctor_get(v___y_5081_, 1);
v_ref_5091_ = lean_ctor_get(v___y_5081_, 2);
v_optionFlags_5092_ = lean_ctor_get_uint16(v___y_5081_, sizeof(void*)*3);
v_suppressElabErrors_5093_ = lean_ctor_get_uint8(v___y_5081_, sizeof(void*)*3 + 2);
v_checkDeprecated_5094_ = lean_ctor_get_uint8(v___y_5081_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5095_ = lean_ctor_get_uint8(v___y_5081_, sizeof(void*)*3 + 4);
v_ref_5096_ = l_Lean_replaceRef(v___x_5045_, v_ref_5091_);
lean_dec(v___x_5045_);
lean_inc(v_currRecDepth_5090_);
lean_inc_ref(v_toCold_5089_);
v___x_5097_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5097_, 0, v_toCold_5089_);
lean_ctor_set(v___x_5097_, 1, v_currRecDepth_5090_);
lean_ctor_set(v___x_5097_, 2, v_ref_5096_);
lean_ctor_set_uint16(v___x_5097_, sizeof(void*)*3, v_optionFlags_5092_);
lean_ctor_set_uint8(v___x_5097_, sizeof(void*)*3 + 2, v_suppressElabErrors_5093_);
lean_ctor_set_uint8(v___x_5097_, sizeof(void*)*3 + 3, v_checkDeprecated_5094_);
lean_ctor_set_uint8(v___x_5097_, sizeof(void*)*3 + 4, v_isRecordingDeps_5095_);
v___x_5098_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_5049_, v_a_5086_, v___y_5082_, v___y_5084_, v___y_5083_, v___y_5079_, v___x_5097_, v___y_5080_);
lean_dec_ref_known(v___x_5097_, 3);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v_a_5099_; lean_object* v_ref_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; 
v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5098_, 1);
v_ref_5100_ = l_Lean_replaceRef(v___x_5046_, v_ref_5091_);
lean_dec(v___x_5046_);
lean_inc(v_currRecDepth_5090_);
lean_inc_ref(v_toCold_5089_);
v___x_5101_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5101_, 0, v_toCold_5089_);
lean_ctor_set(v___x_5101_, 1, v_currRecDepth_5090_);
lean_ctor_set(v___x_5101_, 2, v_ref_5100_);
lean_ctor_set_uint16(v___x_5101_, sizeof(void*)*3, v_optionFlags_5092_);
lean_ctor_set_uint8(v___x_5101_, sizeof(void*)*3 + 2, v_suppressElabErrors_5093_);
lean_ctor_set_uint8(v___x_5101_, sizeof(void*)*3 + 3, v_checkDeprecated_5094_);
lean_ctor_set_uint8(v___x_5101_, sizeof(void*)*3 + 4, v_isRecordingDeps_5095_);
v___x_5102_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_5049_, v_a_5088_, v___y_5082_, v___y_5084_, v___y_5083_, v___y_5079_, v___x_5101_, v___y_5080_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5133_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5105_ = v___x_5102_;
v_isShared_5106_ = v_isSharedCheck_5133_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5102_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5133_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5107_; 
lean_inc(v___y_5080_);
lean_inc_ref(v___y_5081_);
lean_inc(v___y_5079_);
lean_inc_ref(v___y_5083_);
lean_inc(v_a_5099_);
v___x_5107_ = lean_infer_type(v_a_5099_, v___y_5083_, v___y_5079_, v___y_5081_, v___y_5080_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5132_; 
v_a_5108_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5110_ = v___x_5107_;
v_isShared_5111_ = v_isSharedCheck_5132_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_5107_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5132_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
if (v_isShared_5111_ == 0)
{
lean_ctor_set_tag(v___x_5110_, 1);
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5108_);
v___x_5113_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
lean_object* v___x_5114_; 
v___x_5114_ = l_Lean_Elab_Term_ensureHasType(v___x_5113_, v_a_5103_, v___x_5077_, v___x_5077_, v___y_5082_, v___y_5084_, v___y_5083_, v___y_5079_, v___x_5101_, v___y_5080_);
lean_dec_ref_known(v___x_5101_, 3);
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5130_; 
v_a_5115_ = lean_ctor_get(v___x_5114_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5114_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5117_ = v___x_5114_;
v_isShared_5118_ = v_isSharedCheck_5130_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5114_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5130_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5119_; lean_object* v___x_5121_; 
v___x_5119_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
if (v_isShared_5118_ == 0)
{
lean_ctor_set_tag(v___x_5117_, 1);
lean_ctor_set(v___x_5117_, 0, v_a_5099_);
v___x_5121_ = v___x_5117_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5099_);
v___x_5121_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
lean_object* v___x_5123_; 
if (v_isShared_5106_ == 0)
{
lean_ctor_set_tag(v___x_5105_, 1);
lean_ctor_set(v___x_5105_, 0, v_a_5115_);
v___x_5123_ = v___x_5105_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5115_);
v___x_5123_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5124_ = lean_mk_empty_array_with_capacity(v___x_5050_);
v___x_5125_ = lean_array_push(v___x_5124_, v___x_5121_);
v___x_5126_ = lean_array_push(v___x_5125_, v___x_5123_);
v___x_5127_ = l_Lean_Elab_Term_elabAppArgs(v_val_5048_, v___x_5119_, v___x_5126_, v_expectedType_x3f_5051_, v___x_5052_, v___x_5052_, v___x_5052_, v___y_5082_, v___y_5084_, v___y_5083_, v___y_5079_, v___y_5081_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5079_);
lean_dec_ref(v___y_5083_);
return v___x_5127_;
}
}
}
}
else
{
lean_del_object(v___x_5105_);
lean_dec(v_a_5099_);
lean_dec_ref(v___y_5083_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec(v___y_5079_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
return v___x_5114_;
}
}
}
}
else
{
lean_del_object(v___x_5105_);
lean_dec(v_a_5103_);
lean_dec_ref_known(v___x_5101_, 3);
lean_dec(v_a_5099_);
lean_dec_ref(v___y_5083_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec(v___y_5079_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
return v___x_5107_;
}
}
}
else
{
lean_dec_ref_known(v___x_5101_, 3);
lean_dec(v_a_5099_);
lean_dec_ref(v___y_5083_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec(v___y_5079_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
return v___x_5102_;
}
}
else
{
lean_dec(v_a_5088_);
lean_dec_ref(v___y_5083_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec(v___y_5079_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
lean_dec(v___x_5046_);
return v___x_5098_;
}
}
else
{
lean_dec(v_a_5086_);
lean_dec_ref(v___y_5083_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec(v___y_5079_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
lean_dec(v___x_5046_);
lean_dec(v___x_5045_);
return v___x_5087_;
}
}
else
{
lean_dec_ref(v___y_5083_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec(v___y_5079_);
lean_dec(v_a_5074_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
lean_dec(v___x_5046_);
lean_dec(v___x_5045_);
return v___x_5085_;
}
}
}
else
{
lean_object* v_a_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5268_; 
lean_dec(v_a_5070_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
lean_dec(v_stx_5047_);
lean_dec(v___x_5046_);
lean_dec(v___x_5045_);
v_a_5261_ = lean_ctor_get(v___x_5073_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5073_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5263_ = v___x_5073_;
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_a_5261_);
lean_dec(v___x_5073_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v___x_5266_; 
if (v_isShared_5264_ == 0)
{
v___x_5266_ = v___x_5263_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
}
else
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v_expectedType_x3f_5051_);
lean_dec_ref(v_val_5048_);
lean_dec(v_stx_5047_);
lean_dec(v___x_5046_);
lean_dec(v___x_5045_);
v_a_5269_ = lean_ctor_get(v___x_5069_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_5069_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5069_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___boxed(lean_object* v___x_5277_, lean_object* v___x_5278_, lean_object* v_stx_5279_, lean_object* v_val_5280_, lean_object* v_noProp_5281_, lean_object* v___x_5282_, lean_object* v_expectedType_x3f_5283_, lean_object* v___x_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
uint8_t v_noProp_boxed_5292_; uint8_t v___x_11471__boxed_5293_; lean_object* v_res_5294_; 
v_noProp_boxed_5292_ = lean_unbox(v_noProp_5281_);
v___x_11471__boxed_5293_ = lean_unbox(v___x_5284_);
v_res_5294_ = l_Lean_Elab_Term_Op_elabBinRelCore___lam__1(v___x_5277_, v___x_5278_, v_stx_5279_, v_val_5280_, v_noProp_boxed_5292_, v___x_5282_, v_expectedType_x3f_5283_, v___x_11471__boxed_5293_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___x_5282_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore(uint8_t v_noProp_5295_, lean_object* v_stx_5296_, lean_object* v_expectedType_x3f_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_){
_start:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; uint8_t v___x_5308_; lean_object* v___x_5309_; 
v___x_5305_ = lean_unsigned_to_nat(1u);
v___x_5306_ = l_Lean_Syntax_getArg(v_stx_5296_, v___x_5305_);
v___x_5307_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_5308_ = 0;
lean_inc(v___x_5306_);
v___x_5309_ = l_Lean_Elab_Term_resolveId_x3f(v___x_5306_, v___x_5307_, v___x_5308_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
lean_inc(v_a_5310_);
lean_dec_ref_known(v___x_5309_, 1);
if (lean_obj_tag(v_a_5310_) == 0)
{
lean_object* v___x_5311_; lean_object* v___x_5312_; 
lean_dec(v_expectedType_x3f_5297_);
lean_dec(v_stx_5296_);
v___x_5311_ = l_Lean_Syntax_getId(v___x_5306_);
v___x_5312_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v___x_5306_, v___x_5311_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
lean_dec(v___x_5306_);
return v___x_5312_;
}
else
{
lean_object* v_val_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___f_5320_; lean_object* v___x_5321_; 
lean_dec(v___x_5306_);
v_val_5313_ = lean_ctor_get(v_a_5310_, 0);
lean_inc(v_val_5313_);
lean_dec_ref_known(v_a_5310_, 1);
v___x_5314_ = lean_unsigned_to_nat(2u);
v___x_5315_ = l_Lean_Syntax_getArg(v_stx_5296_, v___x_5314_);
v___x_5316_ = lean_unsigned_to_nat(3u);
v___x_5317_ = l_Lean_Syntax_getArg(v_stx_5296_, v___x_5316_);
v___x_5318_ = lean_box(v_noProp_5295_);
v___x_5319_ = lean_box(v___x_5308_);
v___f_5320_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___boxed), 15, 8);
lean_closure_set(v___f_5320_, 0, v___x_5315_);
lean_closure_set(v___f_5320_, 1, v___x_5317_);
lean_closure_set(v___f_5320_, 2, v_stx_5296_);
lean_closure_set(v___f_5320_, 3, v_val_5313_);
lean_closure_set(v___f_5320_, 4, v___x_5318_);
lean_closure_set(v___f_5320_, 5, v___x_5314_);
lean_closure_set(v___f_5320_, 6, v_expectedType_x3f_5297_);
lean_closure_set(v___f_5320_, 7, v___x_5319_);
v___x_5321_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_box(0), v___f_5320_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
return v___x_5321_;
}
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5329_; 
lean_dec(v___x_5306_);
lean_dec(v_expectedType_x3f_5297_);
lean_dec(v_stx_5296_);
v_a_5322_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5324_ = v___x_5309_;
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5309_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5327_; 
if (v_isShared_5325_ == 0)
{
v___x_5327_ = v___x_5324_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5322_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___boxed(lean_object* v_noProp_5330_, lean_object* v_stx_5331_, lean_object* v_expectedType_x3f_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_){
_start:
{
uint8_t v_noProp_boxed_5340_; lean_object* v_res_5341_; 
v_noProp_boxed_5340_ = lean_unbox(v_noProp_5330_);
v_res_5341_ = l_Lean_Elab_Term_Op_elabBinRelCore(v_noProp_boxed_5340_, v_stx_5331_, v_expectedType_x3f_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_);
lean_dec(v_a_5338_);
lean_dec_ref(v_a_5337_);
lean_dec(v_a_5336_);
lean_dec_ref(v_a_5335_);
lean_dec(v_a_5334_);
lean_dec_ref(v_a_5333_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel(lean_object* v_stx_5342_, lean_object* v_expectedType_x3f_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_){
_start:
{
uint8_t v___x_5351_; lean_object* v___x_5352_; 
v___x_5351_ = 0;
v___x_5352_ = l_Lean_Elab_Term_Op_elabBinRelCore(v___x_5351_, v_stx_5342_, v_expectedType_x3f_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_);
return v___x_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel___boxed(lean_object* v_stx_5353_, lean_object* v_expectedType_x3f_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_){
_start:
{
lean_object* v_res_5362_; 
v_res_5362_ = l_Lean_Elab_Term_Op_elabBinRel(v_stx_5353_, v_expectedType_x3f_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_);
lean_dec(v_a_5360_);
lean_dec_ref(v_a_5359_);
lean_dec(v_a_5358_);
lean_dec_ref(v_a_5357_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
return v_res_5362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1(){
_start:
{
lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; 
v___x_5376_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5377_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0));
v___x_5378_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2));
v___x_5379_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRel___boxed), 9, 0);
v___x_5380_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5376_, v___x_5377_, v___x_5378_, v___x_5379_);
return v___x_5380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___boxed(lean_object* v_a_5381_){
_start:
{
lean_object* v_res_5382_; 
v_res_5382_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1();
return v_res_5382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3(){
_start:
{
lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___x_5409_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2));
v___x_5410_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__6));
v___x_5411_ = l_Lean_addBuiltinDeclarationRanges(v___x_5409_, v___x_5410_);
return v___x_5411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___boxed(lean_object* v_a_5412_){
_start:
{
lean_object* v_res_5413_; 
v_res_5413_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3();
return v_res_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp(lean_object* v_stx_5414_, lean_object* v_expectedType_x3f_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_){
_start:
{
uint8_t v___x_5423_; lean_object* v___x_5424_; 
v___x_5423_ = 1;
v___x_5424_ = l_Lean_Elab_Term_Op_elabBinRelCore(v___x_5423_, v_stx_5414_, v_expectedType_x3f_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp___boxed(lean_object* v_stx_5425_, lean_object* v_expectedType_x3f_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_Lean_Elab_Term_Op_elabBinRelNoProp(v_stx_5425_, v_expectedType_x3f_5426_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
lean_dec(v_a_5432_);
lean_dec_ref(v_a_5431_);
lean_dec(v_a_5430_);
lean_dec_ref(v_a_5429_);
lean_dec(v_a_5428_);
lean_dec_ref(v_a_5427_);
return v_res_5434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1(){
_start:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5449_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5450_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1));
v___x_5451_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3));
v___x_5452_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelNoProp___boxed), 9, 0);
v___x_5453_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5449_, v___x_5450_, v___x_5451_, v___x_5452_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___boxed(lean_object* v_a_5454_){
_start:
{
lean_object* v_res_5455_; 
v_res_5455_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1();
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3(){
_start:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; 
v___x_5482_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3));
v___x_5483_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__6));
v___x_5484_ = l_Lean_addBuiltinDeclarationRanges(v___x_5482_, v___x_5483_);
return v___x_5484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___boxed(lean_object* v_a_5485_){
_start:
{
lean_object* v_res_5486_; 
v_res_5486_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3();
return v_res_5486_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1(void){
_start:
{
lean_object* v___x_5488_; lean_object* v___x_5489_; 
v___x_5488_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__0));
v___x_5489_ = l_Lean_stringToMessageData(v___x_5488_);
return v___x_5489_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3(void){
_start:
{
lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5491_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__2));
v___x_5492_ = l_Lean_stringToMessageData(v___x_5491_);
return v___x_5492_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7(void){
_start:
{
lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___x_5497_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__6));
v___x_5498_ = l_Lean_stringToMessageData(v___x_5497_);
return v___x_5498_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11(void){
_start:
{
lean_object* v___x_5503_; lean_object* v___x_5504_; 
v___x_5503_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__10));
v___x_5504_ = l_Lean_stringToMessageData(v___x_5503_);
return v___x_5504_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13(void){
_start:
{
lean_object* v___x_5506_; lean_object* v___x_5507_; 
v___x_5506_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__12));
v___x_5507_ = l_Lean_stringToMessageData(v___x_5506_);
return v___x_5507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty(lean_object* v_stx_5508_, lean_object* v_expectedType_x3f_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_){
_start:
{
lean_object* v___x_5517_; 
lean_inc(v_expectedType_x3f_5509_);
v___x_5517_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
if (lean_obj_tag(v___x_5517_) == 0)
{
lean_dec_ref_known(v___x_5517_, 1);
if (lean_obj_tag(v_expectedType_x3f_5509_) == 0)
{
lean_object* v___x_5518_; lean_object* v___x_5519_; 
v___x_5518_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1);
v___x_5519_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_5518_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
return v___x_5519_;
}
else
{
lean_object* v_val_5520_; lean_object* v___x_5521_; 
v_val_5520_ = lean_ctor_get(v_expectedType_x3f_5509_, 0);
lean_inc_n(v_val_5520_, 2);
lean_dec_ref_known(v_expectedType_x3f_5509_, 1);
v___x_5521_ = l_Lean_Meta_mkDefault(v_val_5520_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
if (lean_obj_tag(v___x_5521_) == 0)
{
lean_dec(v_val_5520_);
return v___x_5521_;
}
else
{
lean_object* v_a_5522_; uint8_t v___x_5523_; 
v_a_5522_ = lean_ctor_get(v___x_5521_, 0);
v___x_5523_ = l_Lean_Exception_isInterrupt(v_a_5522_);
if (v___x_5523_ == 0)
{
uint8_t v___x_5524_; 
lean_inc(v_a_5522_);
v___x_5524_ = l_Lean_Exception_isRuntime(v_a_5522_);
if (v___x_5524_ == 0)
{
lean_object* v___x_5525_; 
lean_dec_ref_known(v___x_5521_, 1);
lean_inc(v_val_5520_);
v___x_5525_ = l_Lean_Meta_mkOfNonempty(v_val_5520_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
if (lean_obj_tag(v___x_5525_) == 0)
{
lean_dec(v_val_5520_);
return v___x_5525_;
}
else
{
lean_object* v_a_5526_; uint8_t v___x_5527_; 
v_a_5526_ = lean_ctor_get(v___x_5525_, 0);
v___x_5527_ = l_Lean_Exception_isInterrupt(v_a_5526_);
if (v___x_5527_ == 0)
{
uint8_t v___x_5528_; 
lean_inc(v_a_5526_);
v___x_5528_ = l_Lean_Exception_isRuntime(v_a_5526_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5529_; lean_object* v___x_5530_; uint8_t v___x_5531_; 
lean_dec_ref_known(v___x_5525_, 1);
v___x_5529_ = lean_unsigned_to_nat(1u);
v___x_5530_ = l_Lean_Syntax_getArg(v_stx_5508_, v___x_5529_);
v___x_5531_ = l_Lean_Syntax_isNone(v___x_5530_);
lean_dec(v___x_5530_);
if (v___x_5531_ == 0)
{
uint8_t v___x_5532_; lean_object* v___x_5533_; 
v___x_5532_ = 1;
v___x_5533_ = l_Lean_Meta_mkLabeledSorry(v_val_5520_, v___x_5531_, v___x_5532_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
return v___x_5533_;
}
else
{
lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; 
v___x_5534_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3);
v___x_5535_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__5));
v___x_5536_ = l_Lean_MessageData_ofConstName(v___x_5535_, v___x_5528_);
v___x_5537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5534_);
lean_ctor_set(v___x_5537_, 1, v___x_5536_);
v___x_5538_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7);
v___x_5539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5539_, 0, v___x_5537_);
lean_ctor_set(v___x_5539_, 1, v___x_5538_);
v___x_5540_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__9));
v___x_5541_ = l_Lean_MessageData_ofConstName(v___x_5540_, v___x_5528_);
v___x_5542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5539_);
lean_ctor_set(v___x_5542_, 1, v___x_5541_);
v___x_5543_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11);
v___x_5544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5542_);
lean_ctor_set(v___x_5544_, 1, v___x_5543_);
v___x_5545_ = l_Lean_indentExpr(v_val_5520_);
v___x_5546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5544_);
lean_ctor_set(v___x_5546_, 1, v___x_5545_);
v___x_5547_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13);
v___x_5548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5548_, 0, v___x_5546_);
lean_ctor_set(v___x_5548_, 1, v___x_5547_);
v___x_5549_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_5548_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
return v___x_5549_;
}
}
else
{
lean_dec(v_val_5520_);
return v___x_5525_;
}
}
else
{
lean_dec(v_val_5520_);
return v___x_5525_;
}
}
}
else
{
lean_dec(v_val_5520_);
return v___x_5521_;
}
}
else
{
lean_dec(v_val_5520_);
return v___x_5521_;
}
}
}
}
else
{
lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5557_; 
lean_dec(v_expectedType_x3f_5509_);
v_a_5550_ = lean_ctor_get(v___x_5517_, 0);
v_isSharedCheck_5557_ = !lean_is_exclusive(v___x_5517_);
if (v_isSharedCheck_5557_ == 0)
{
v___x_5552_ = v___x_5517_;
v_isShared_5553_ = v_isSharedCheck_5557_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_dec(v___x_5517_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5557_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
lean_object* v___x_5555_; 
if (v_isShared_5553_ == 0)
{
v___x_5555_ = v___x_5552_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_a_5550_);
v___x_5555_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
return v___x_5555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___boxed(lean_object* v_stx_5558_, lean_object* v_expectedType_x3f_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_, lean_object* v_a_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_){
_start:
{
lean_object* v_res_5567_; 
v_res_5567_ = l_Lean_Elab_Term_Op_elabDefaultOrNonempty(v_stx_5558_, v_expectedType_x3f_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec_ref(v_a_5560_);
lean_dec(v_stx_5558_);
return v_res_5567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1(){
_start:
{
lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; 
v___x_5582_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5583_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1));
v___x_5584_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3));
v___x_5585_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___boxed), 9, 0);
v___x_5586_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5582_, v___x_5583_, v___x_5584_, v___x_5585_);
return v___x_5586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___boxed(lean_object* v_a_5587_){
_start:
{
lean_object* v_res_5588_; 
v_res_5588_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1();
return v_res_5588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3(){
_start:
{
lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; 
v___x_5615_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3));
v___x_5616_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__6));
v___x_5617_ = l_Lean_addBuiltinDeclarationRanges(v___x_5615_, v___x_5616_);
return v___x_5617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___boxed(lean_object* v_a_5618_){
_start:
{
lean_object* v_res_5619_; 
v_res_5619_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3();
return v_res_5619_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; 
v___x_5666_ = lean_unsigned_to_nat(2859506122u);
v___x_5667_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__17_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_5668_ = l_Lean_Name_num___override(v___x_5667_, v___x_5666_);
return v___x_5668_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; 
v___x_5670_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__19_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_5671_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5672_ = l_Lean_Name_str___override(v___x_5671_, v___x_5670_);
return v___x_5672_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; 
v___x_5674_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__21_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_5675_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5676_ = l_Lean_Name_str___override(v___x_5675_, v___x_5674_);
return v___x_5676_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; 
v___x_5677_ = lean_unsigned_to_nat(2u);
v___x_5678_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5679_ = l_Lean_Name_num___override(v___x_5678_, v___x_5677_);
return v___x_5679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5681_; uint8_t v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; 
v___x_5681_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_5682_ = 0;
v___x_5683_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5684_ = l_Lean_registerTraceClass(v___x_5681_, v___x_5682_, v___x_5683_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v___x_5685_; lean_object* v___x_5686_; 
lean_dec_ref_known(v___x_5684_, 1);
v___x_5685_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
v___x_5686_ = l_Lean_registerTraceClass(v___x_5685_, v___x_5682_, v___x_5683_);
return v___x_5686_;
}
else
{
return v___x_5684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2____boxed(lean_object* v_a_5687_){
_start:
{
lean_object* v_res_5688_; 
v_res_5688_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_();
return v_res_5688_;
}
}
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn_x27___regBuiltin_Lean_Elab_Term_elabForIn_x27_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_App(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Extra(builtin);
}
#ifdef __cplusplus
}
#endif
