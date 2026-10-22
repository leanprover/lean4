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
lean_object* v_declName_x3f_1062_; lean_object* v_macroStack_1063_; uint8_t v_mayPostpone_1064_; uint8_t v_errToSorry_1065_; lean_object* v_autoBoundImplicitContext_1066_; lean_object* v_autoBoundImplicitForbidden_1067_; lean_object* v_sectionVars_1068_; lean_object* v_sectionFVars_1069_; uint8_t v_implicitLambda_1070_; uint8_t v_heedElabAsElim_1071_; uint8_t v_isNoncomputableSection_1072_; uint8_t v_isMetaSection_1073_; uint8_t v_ignoreTCFailures_1074_; uint8_t v_inPattern_1075_; lean_object* v_tacSnap_x3f_1076_; uint8_t v_saveRecAppSyntax_1077_; uint8_t v_holesAsSyntheticOpaque_1078_; uint8_t v_checkDeprecated_1079_; lean_object* v_fixedTermElabs_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
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
v_checkDeprecated_1079_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1080_ = lean_ctor_get(v___y_1055_, 7);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_beforeStx_1052_);
lean_ctor_set(v___x_1081_, 1, v_afterStx_1053_);
lean_inc(v_macroStack_1063_);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v_macroStack_1063_);
lean_inc_ref(v_fixedTermElabs_1080_);
lean_inc(v_tacSnap_x3f_1076_);
lean_inc(v_sectionFVars_1069_);
lean_inc(v_sectionVars_1068_);
lean_inc_ref(v_autoBoundImplicitForbidden_1067_);
lean_inc(v_autoBoundImplicitContext_1066_);
lean_inc(v_declName_x3f_1062_);
v___x_1083_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1083_, 0, v_declName_x3f_1062_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
lean_ctor_set(v___x_1083_, 2, v_autoBoundImplicitContext_1066_);
lean_ctor_set(v___x_1083_, 3, v_autoBoundImplicitForbidden_1067_);
lean_ctor_set(v___x_1083_, 4, v_sectionVars_1068_);
lean_ctor_set(v___x_1083_, 5, v_sectionFVars_1069_);
lean_ctor_set(v___x_1083_, 6, v_tacSnap_x3f_1076_);
lean_ctor_set(v___x_1083_, 7, v_fixedTermElabs_1080_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8, v_mayPostpone_1064_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 1, v_errToSorry_1065_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 2, v_implicitLambda_1070_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 3, v_heedElabAsElim_1071_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1072_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 5, v_isMetaSection_1073_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 6, v_ignoreTCFailures_1074_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 7, v_inPattern_1075_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1077_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1078_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*8 + 10, v_checkDeprecated_1079_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
v___x_1084_ = lean_apply_7(v_x_1054_, v___x_1083_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, lean_box(0));
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg___boxed(lean_object* v_beforeStx_1085_, lean_object* v_afterStx_1086_, lean_object* v_x_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_beforeStx_1085_, v_afterStx_1086_, v_x_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0(lean_object* v_00_u03b1_1096_, lean_object* v_beforeStx_1097_, lean_object* v_afterStx_1098_, lean_object* v_x_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_beforeStx_1097_, v_afterStx_1098_, v_x_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___boxed(lean_object* v_00_u03b1_1108_, lean_object* v_beforeStx_1109_, lean_object* v_afterStx_1110_, lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0(v_00_u03b1_1108_, v_beforeStx_1109_, v_afterStx_1110_, v_x_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
lean_ctor_set(v___x_1126_, 2, v___x_1125_);
lean_ctor_set(v___x_1126_, 3, v___x_1125_);
lean_ctor_set(v___x_1126_, 4, v___x_1124_);
lean_ctor_set(v___x_1126_, 5, v___x_1124_);
lean_ctor_set(v___x_1126_, 6, v___x_1124_);
lean_ctor_set(v___x_1126_, 7, v___x_1124_);
lean_ctor_set(v___x_1126_, 8, v___x_1124_);
lean_ctor_set(v___x_1126_, 9, v___x_1124_);
lean_ctor_set(v___x_1126_, 10, v___x_1124_);
lean_ctor_set(v___x_1126_, 11, v___x_1123_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(32u);
v___x_1128_ = lean_mk_empty_array_with_capacity(v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1130_ = ((size_t)5ULL);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_unsigned_to_nat(32u);
v___x_1133_ = lean_mk_empty_array_with_capacity(v___x_1132_);
v___x_1134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3);
v___x_1135_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v___x_1133_);
lean_ctor_set(v___x_1135_, 2, v___x_1131_);
lean_ctor_set(v___x_1135_, 3, v___x_1131_);
lean_ctor_set_usize(v___x_1135_, 4, v___x_1130_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1136_ = lean_box(1);
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4);
v___x_1138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_1139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v___x_1137_);
lean_ctor_set(v___x_1139_, 2, v___x_1136_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__6));
v___x_1142_ = l_Lean_stringToMessageData(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__8));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__10));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__12));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__14));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18));
v___x_1160_ = l_Lean_stringToMessageData(v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(lean_object* v_msg_1161_, lean_object* v_declHint_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_env_1167_; uint8_t v___x_1168_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_st_ref_get(v___y_1163_);
v_env_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc_ref(v_env_1167_);
lean_dec(v___x_1166_);
v___x_1168_ = l_Lean_Name_isAnonymous(v_declHint_1162_);
if (v___x_1168_ == 0)
{
uint8_t v_isExporting_1169_; 
v_isExporting_1169_ = lean_ctor_get_uint8(v_env_1167_, sizeof(void*)*13);
if (v_isExporting_1169_ == 0)
{
lean_object* v___x_1170_; 
lean_dec_ref(v_env_1167_);
lean_dec(v_declHint_1162_);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_msg_1161_);
return v___x_1170_;
}
else
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
lean_inc_ref(v_env_1167_);
v___x_1171_ = l_Lean_Environment_setExporting(v_env_1167_, v___x_1168_);
lean_inc(v_declHint_1162_);
lean_inc_ref(v___x_1171_);
v___x_1172_ = l_Lean_Environment_contains(v___x_1171_, v_declHint_1162_, v_isExporting_1169_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec_ref(v___x_1171_);
lean_dec_ref(v_env_1167_);
lean_dec(v_declHint_1162_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_msg_1161_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_c_1179_; lean_object* v___x_1180_; 
v___x_1174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_1175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5);
v___x_1176_ = l_Lean_Options_empty;
v___x_1177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1171_);
lean_ctor_set(v___x_1177_, 1, v___x_1174_);
lean_ctor_set(v___x_1177_, 2, v___x_1175_);
lean_ctor_set(v___x_1177_, 3, v___x_1176_);
lean_inc(v_declHint_1162_);
v___x_1178_ = l_Lean_MessageData_ofConstName(v_declHint_1162_, v___x_1168_);
v_c_1179_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1179_, 0, v___x_1177_);
lean_ctor_set(v_c_1179_, 1, v___x_1178_);
v___x_1180_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1167_, v_declHint_1162_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec_ref(v_env_1167_);
lean_dec(v_declHint_1162_);
v___x_1181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v_c_1179_);
v___x_1183_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_MessageData_note(v___x_1184_);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v_msg_1161_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
else
{
lean_object* v_val_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1222_; 
v_val_1188_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1190_ = v___x_1180_;
v_isShared_1191_ = v_isSharedCheck_1222_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_val_1188_);
lean_dec(v___x_1180_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1222_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v_moduleNames_1193_; lean_object* v_mod_1194_; uint8_t v___x_1195_; 
v___x_1192_ = l_Lean_Environment_header(v_env_1167_);
lean_dec_ref(v_env_1167_);
v_moduleNames_1193_ = lean_ctor_get(v___x_1192_, 4);
lean_inc_ref(v_moduleNames_1193_);
lean_dec_ref(v___x_1192_);
v_mod_1194_ = lean_array_get(v___x_1165_, v_moduleNames_1193_, v_val_1188_);
lean_dec(v_val_1188_);
lean_dec_ref(v_moduleNames_1193_);
v___x_1195_ = l_Lean_isPrivateName(v_declHint_1162_);
lean_dec(v_declHint_1162_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1196_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v_c_1179_);
v___x_1198_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_MessageData_ofName(v_mod_1194_);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = l_Lean_MessageData_note(v___x_1203_);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v_msg_1161_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set_tag(v___x_1190_, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1205_);
v___x_1207_ = v___x_1190_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1209_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v_c_1179_);
v___x_1211_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = l_Lean_MessageData_ofName(v_mod_1194_);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19);
v___x_1216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = l_Lean_MessageData_note(v___x_1216_);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_msg_1161_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set_tag(v___x_1190_, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1218_);
v___x_1220_ = v___x_1190_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1223_; 
lean_dec_ref(v_env_1167_);
lean_dec(v_declHint_1162_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_msg_1161_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1224_, lean_object* v_declHint_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1224_, v_declHint_1225_, v___y_1226_);
lean_dec(v___y_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(lean_object* v_msg_1229_, lean_object* v_declHint_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1248_; 
v___x_1238_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1229_, v_declHint_1230_, v___y_1236_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1248_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1248_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1243_ = l_Lean_unknownIdentifierMessageTag;
v___x_1244_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v_a_1239_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1244_);
v___x_1246_ = v___x_1241_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4___boxed(lean_object* v_msg_1249_, lean_object* v_declHint_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(v_msg_1249_, v_declHint_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_1259_, lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_toCold_1268_; lean_object* v_currRecDepth_1269_; lean_object* v_ref_1270_; uint16_t v_optionFlags_1271_; uint8_t v_suppressElabErrors_1272_; uint8_t v_isRecordingDeps_1273_; lean_object* v_ref_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_toCold_1268_ = lean_ctor_get(v___y_1265_, 0);
v_currRecDepth_1269_ = lean_ctor_get(v___y_1265_, 1);
v_ref_1270_ = lean_ctor_get(v___y_1265_, 2);
v_optionFlags_1271_ = lean_ctor_get_uint16(v___y_1265_, sizeof(void*)*3);
v_suppressElabErrors_1272_ = lean_ctor_get_uint8(v___y_1265_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1273_ = lean_ctor_get_uint8(v___y_1265_, sizeof(void*)*3 + 3);
v_ref_1274_ = l_Lean_replaceRef(v_ref_1259_, v_ref_1270_);
lean_inc(v_currRecDepth_1269_);
lean_inc_ref(v_toCold_1268_);
v___x_1275_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1275_, 0, v_toCold_1268_);
lean_ctor_set(v___x_1275_, 1, v_currRecDepth_1269_);
lean_ctor_set(v___x_1275_, 2, v_ref_1274_);
lean_ctor_set_uint16(v___x_1275_, sizeof(void*)*3, v_optionFlags_1271_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*3 + 2, v_suppressElabErrors_1272_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*3 + 3, v_isRecordingDeps_1273_);
v___x_1276_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v_msg_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___x_1275_, v___y_1266_);
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
lean_object* v_toCold_1513_; lean_object* v_currRecDepth_1514_; lean_object* v_ref_1515_; uint16_t v_optionFlags_1516_; uint8_t v_suppressElabErrors_1517_; uint8_t v_isRecordingDeps_1518_; lean_object* v_ref_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_toCold_1513_ = lean_ctor_get(v_a_1498_, 0);
v_currRecDepth_1514_ = lean_ctor_get(v_a_1498_, 1);
v_ref_1515_ = lean_ctor_get(v_a_1498_, 2);
v_optionFlags_1516_ = lean_ctor_get_uint16(v_a_1498_, sizeof(void*)*3);
v_suppressElabErrors_1517_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1518_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 3);
v_ref_1519_ = l_Lean_replaceRef(v_s_1493_, v_ref_1515_);
lean_inc(v_currRecDepth_1514_);
lean_inc_ref(v_toCold_1513_);
v___x_1520_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1520_, 0, v_toCold_1513_);
lean_ctor_set(v___x_1520_, 1, v_currRecDepth_1514_);
lean_ctor_set(v___x_1520_, 2, v_ref_1519_);
lean_ctor_set_uint16(v___x_1520_, sizeof(void*)*3, v_optionFlags_1516_);
lean_ctor_set_uint8(v___x_1520_, sizeof(void*)*3 + 2, v_suppressElabErrors_1517_);
lean_ctor_set_uint8(v___x_1520_, sizeof(void*)*3 + 3, v_isRecordingDeps_1518_);
lean_inc(v_s_1493_);
v___x_1521_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1520_, v_a_1499_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
if (lean_obj_tag(v_a_1522_) == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1520_, v_a_1499_);
lean_dec_ref_known(v___x_1520_, 3);
return v___x_1523_;
}
else
{
lean_object* v_val_1524_; lean_object* v_fst_1525_; lean_object* v_snd_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; 
v_val_1524_ = lean_ctor_get(v_a_1522_, 0);
lean_inc(v_val_1524_);
lean_dec_ref_known(v_a_1522_, 1);
v_fst_1525_ = lean_ctor_get(v_val_1524_, 0);
lean_inc(v_fst_1525_);
v_snd_1526_ = lean_ctor_get(v_val_1524_, 1);
lean_inc_n(v_snd_1526_, 2);
lean_dec(v_val_1524_);
lean_inc(v_s_1493_);
v___f_1527_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1527_, 0, v_snd_1526_);
lean_closure_set(v___f_1527_, 1, v_fst_1525_);
lean_closure_set(v___f_1527_, 2, v_s_1493_);
v___x_1528_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1493_, v_snd_1526_, v___f_1527_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1520_, v_a_1499_);
lean_dec_ref_known(v___x_1520_, 3);
return v___x_1528_;
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec_ref_known(v___x_1520_, 3);
lean_dec(v_s_1493_);
v_a_1529_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1521_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1521_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1537_);
v___x_1539_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13));
lean_inc(v___x_1538_);
v___x_1540_ = l_Lean_Syntax_isOfKind(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v_toCold_1541_; lean_object* v_currRecDepth_1542_; lean_object* v_ref_1543_; uint16_t v_optionFlags_1544_; uint8_t v_suppressElabErrors_1545_; uint8_t v_isRecordingDeps_1546_; lean_object* v_ref_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v___x_1538_);
v_toCold_1541_ = lean_ctor_get(v_a_1498_, 0);
v_currRecDepth_1542_ = lean_ctor_get(v_a_1498_, 1);
v_ref_1543_ = lean_ctor_get(v_a_1498_, 2);
v_optionFlags_1544_ = lean_ctor_get_uint16(v_a_1498_, sizeof(void*)*3);
v_suppressElabErrors_1545_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1546_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 3);
v_ref_1547_ = l_Lean_replaceRef(v_s_1493_, v_ref_1543_);
lean_inc(v_currRecDepth_1542_);
lean_inc_ref(v_toCold_1541_);
v___x_1548_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1548_, 0, v_toCold_1541_);
lean_ctor_set(v___x_1548_, 1, v_currRecDepth_1542_);
lean_ctor_set(v___x_1548_, 2, v_ref_1547_);
lean_ctor_set_uint16(v___x_1548_, sizeof(void*)*3, v_optionFlags_1544_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*3 + 2, v_suppressElabErrors_1545_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*3 + 3, v_isRecordingDeps_1546_);
lean_inc(v_s_1493_);
v___x_1549_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1548_, v_a_1499_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
if (lean_obj_tag(v_a_1550_) == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1548_, v_a_1499_);
lean_dec_ref_known(v___x_1548_, 3);
return v___x_1551_;
}
else
{
lean_object* v_val_1552_; lean_object* v_fst_1553_; lean_object* v_snd_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; 
v_val_1552_ = lean_ctor_get(v_a_1550_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v_a_1550_, 1);
v_fst_1553_ = lean_ctor_get(v_val_1552_, 0);
lean_inc(v_fst_1553_);
v_snd_1554_ = lean_ctor_get(v_val_1552_, 1);
lean_inc_n(v_snd_1554_, 2);
lean_dec(v_val_1552_);
lean_inc(v_s_1493_);
v___f_1555_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1555_, 0, v_snd_1554_);
lean_closure_set(v___f_1555_, 1, v_fst_1553_);
lean_closure_set(v___f_1555_, 2, v_s_1493_);
v___x_1556_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1493_, v_snd_1554_, v___f_1555_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1548_, v_a_1499_);
lean_dec_ref_known(v___x_1548_, 3);
return v___x_1556_;
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref_known(v___x_1548_, 3);
lean_dec(v_s_1493_);
v_a_1557_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1549_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1549_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v___x_1565_; lean_object* v_h_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
v_h_1566_ = l_Lean_Syntax_getArg(v___x_1538_, v___x_1565_);
lean_dec(v___x_1538_);
v___x_1567_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__15));
lean_inc(v_h_1566_);
v___x_1568_ = l_Lean_Syntax_isOfKind(v_h_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v_toCold_1569_; lean_object* v_currRecDepth_1570_; lean_object* v_ref_1571_; uint16_t v_optionFlags_1572_; uint8_t v_suppressElabErrors_1573_; uint8_t v_isRecordingDeps_1574_; lean_object* v_ref_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec(v_h_1566_);
v_toCold_1569_ = lean_ctor_get(v_a_1498_, 0);
v_currRecDepth_1570_ = lean_ctor_get(v_a_1498_, 1);
v_ref_1571_ = lean_ctor_get(v_a_1498_, 2);
v_optionFlags_1572_ = lean_ctor_get_uint16(v_a_1498_, sizeof(void*)*3);
v_suppressElabErrors_1573_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1574_ = lean_ctor_get_uint8(v_a_1498_, sizeof(void*)*3 + 3);
v_ref_1575_ = l_Lean_replaceRef(v_s_1493_, v_ref_1571_);
lean_inc(v_currRecDepth_1570_);
lean_inc_ref(v_toCold_1569_);
v___x_1576_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1576_, 0, v_toCold_1569_);
lean_ctor_set(v___x_1576_, 1, v_currRecDepth_1570_);
lean_ctor_set(v___x_1576_, 2, v_ref_1575_);
lean_ctor_set_uint16(v___x_1576_, sizeof(void*)*3, v_optionFlags_1572_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*3 + 2, v_suppressElabErrors_1573_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*3 + 3, v_isRecordingDeps_1574_);
lean_inc(v_s_1493_);
v___x_1577_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1576_, v_a_1499_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
if (lean_obj_tag(v_a_1578_) == 0)
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1576_, v_a_1499_);
lean_dec_ref_known(v___x_1576_, 3);
return v___x_1579_;
}
else
{
lean_object* v_val_1580_; lean_object* v_fst_1581_; lean_object* v_snd_1582_; lean_object* v___f_1583_; lean_object* v___x_1584_; 
v_val_1580_ = lean_ctor_get(v_a_1578_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v_a_1578_, 1);
v_fst_1581_ = lean_ctor_get(v_val_1580_, 0);
lean_inc(v_fst_1581_);
v_snd_1582_ = lean_ctor_get(v_val_1580_, 1);
lean_inc_n(v_snd_1582_, 2);
lean_dec(v_val_1580_);
lean_inc(v_s_1493_);
v___f_1583_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1583_, 0, v_snd_1582_);
lean_closure_set(v___f_1583_, 1, v_fst_1581_);
lean_closure_set(v___f_1583_, 2, v_s_1493_);
v___x_1584_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1493_, v_snd_1582_, v___f_1583_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v___x_1576_, v_a_1499_);
lean_dec_ref_known(v___x_1576_, 3);
return v___x_1584_;
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref_known(v___x_1576_, 3);
lean_dec(v_s_1493_);
v_a_1585_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1577_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1577_);
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
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1593_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1565_);
v___x_1594_ = l_Lean_TSyntax_getHygieneInfo(v_h_1566_);
lean_dec(v_h_1566_);
v___x_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_inc(v___x_1593_);
v___x_1596_ = l_Lean_Elab_Term_hasCDot(v___x_1593_, v___x_1595_);
lean_dec_ref_known(v___x_1595_, 1);
if (v___x_1596_ == 0)
{
lean_dec(v_s_1493_);
v_s_1493_ = v___x_1593_;
goto _start;
}
else
{
lean_object* v___x_1598_; 
lean_dec(v___x_1593_);
v___x_1598_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1598_;
}
}
}
}
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; lean_object* v___x_1606_; 
v___x_1599_ = lean_unsigned_to_nat(1u);
v___x_1600_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1599_);
v___x_1601_ = lean_unsigned_to_nat(2u);
v___x_1602_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1601_);
v___x_1603_ = lean_unsigned_to_nat(3u);
v___x_1604_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1603_);
v___x_1605_ = 3;
v___x_1606_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1493_, v___x_1605_, v___x_1600_, v___x_1602_, v___x_1604_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1606_;
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1607_ = lean_unsigned_to_nat(1u);
v___x_1608_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1607_);
v___x_1609_ = lean_unsigned_to_nat(2u);
v___x_1610_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1609_);
v___x_1611_ = lean_unsigned_to_nat(3u);
v___x_1612_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1611_);
v___x_1613_ = 2;
v___x_1614_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1493_, v___x_1613_, v___x_1608_, v___x_1610_, v___x_1612_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1614_;
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1615_);
v___x_1617_ = lean_unsigned_to_nat(2u);
v___x_1618_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1617_);
v___x_1619_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(v_s_1493_, v___x_1616_, v___x_1618_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1619_;
}
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; 
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1620_);
v___x_1622_ = lean_unsigned_to_nat(2u);
v___x_1623_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1622_);
v___x_1624_ = lean_unsigned_to_nat(3u);
v___x_1625_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1624_);
v___x_1626_ = 1;
v___x_1627_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1493_, v___x_1626_, v___x_1621_, v___x_1623_, v___x_1625_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1627_;
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; 
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1628_);
v___x_1630_ = lean_unsigned_to_nat(2u);
v___x_1631_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1630_);
v___x_1632_ = lean_unsigned_to_nat(3u);
v___x_1633_ = l_Lean_Syntax_getArg(v_s_1493_, v___x_1632_);
v___x_1634_ = 0;
v___x_1635_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1493_, v___x_1634_, v___x_1629_, v___x_1631_, v___x_1633_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0(lean_object* v_snd_1636_, lean_object* v_fst_1637_, lean_object* v_s_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; 
lean_inc(v_snd_1636_);
v___x_1646_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_snd_1636_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
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
v___x_1651_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1651_, 0, v_fst_1637_);
lean_ctor_set(v___x_1651_, 1, v_s_1638_);
lean_ctor_set(v___x_1651_, 2, v_snd_1636_);
lean_ctor_set(v___x_1651_, 3, v_a_1647_);
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
lean_dec(v_s_1638_);
lean_dec(v_fst_1637_);
lean_dec(v_snd_1636_);
return v___x_1646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___boxed(lean_object* v_ref_1656_, lean_object* v_f_1657_, lean_object* v_arg_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(v_ref_1656_, v_f_1657_, v_arg_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp___boxed(lean_object* v_ref_1667_, lean_object* v_kind_1668_, lean_object* v_f_1669_, lean_object* v_lhs_1670_, lean_object* v_rhs_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
uint8_t v_kind_boxed_1679_; lean_object* v_res_1680_; 
v_kind_boxed_1679_ = lean_unbox(v_kind_1668_);
v_res_1680_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_ref_1667_, v_kind_boxed_1679_, v_f_1669_, v_lhs_1670_, v_rhs_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed(lean_object* v_s_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_s_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2(lean_object* v_00_u03b1_1690_, lean_object* v_ref_1691_, lean_object* v_constName_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_ref_1691_, v_constName_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___boxed(lean_object* v_00_u03b1_1701_, lean_object* v_ref_1702_, lean_object* v_constName_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2(v_00_u03b1_1701_, v_ref_1702_, v_constName_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v_ref_1702_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2(lean_object* v_00_u03b1_1712_, lean_object* v_ref_1713_, lean_object* v_msg_1714_, lean_object* v_declHint_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_1713_, v_msg_1714_, v_declHint_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_ref_1725_, lean_object* v_msg_1726_, lean_object* v_declHint_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2(v_00_u03b1_1724_, v_ref_1725_, v_msg_1726_, v_declHint_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v_ref_1725_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5(lean_object* v_msg_1736_, lean_object* v_declHint_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1736_, v_declHint_1737_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1746_, lean_object* v_declHint_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5(v_msg_1746_, v_declHint_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_1756_, lean_object* v_ref_1757_, lean_object* v_msg_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_1757_, v_msg_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_1767_, lean_object* v_ref_1768_, lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5(v_00_u03b1_1767_, v_ref_1768_, v_msg_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v_ref_1768_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(lean_object* v_s_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_s_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; uint8_t v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v___x_1788_ = 0;
v___x_1789_ = 0;
v___x_1790_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1788_, v___x_1789_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v___x_1790_, 0);
lean_dec(v_unused_1798_);
v___x_1792_ = v___x_1790_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_dec(v___x_1790_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v_a_1787_);
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1787_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_a_1787_);
v_a_1799_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1790_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1790_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree___boxed(lean_object* v_s_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v_s_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0(lean_object* v_toType_1816_, uint8_t v___x_1817_, lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_Meta_coerceSimple_x3f(v_x_1818_, v_toType_1816_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1840_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
if (lean_obj_tag(v_a_1827_) == 1)
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
lean_dec_ref_known(v_a_1827_, 1);
v___x_1831_ = lean_box(v___x_1817_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
else
{
uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_dec(v_a_1827_);
v___x_1835_ = 0;
v___x_1836_ = lean_box(v___x_1835_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1836_);
v___x_1838_ = v___x_1829_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_a_1841_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1826_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1826_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0___boxed(lean_object* v_toType_1849_, lean_object* v___x_1850_, lean_object* v_x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___x_1720__boxed_1859_; lean_object* v_res_1860_; 
v___x_1720__boxed_1859_ = lean_unbox(v___x_1850_);
v_res_1860_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0(v_toType_1849_, v___x_1720__boxed_1859_, v_x_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v_b_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; 
lean_inc(v___y_1868_);
lean_inc_ref(v___y_1867_);
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
v___x_1870_ = lean_apply_8(v_k_1861_, v_b_1864_, v___y_1862_, v___y_1863_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, lean_box(0));
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v_b_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0(v_k_1871_, v___y_1872_, v___y_1873_, v_b_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(lean_object* v_name_1881_, uint8_t v_bi_1882_, lean_object* v_type_1883_, lean_object* v_k_1884_, uint8_t v_kind_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___f_1893_; lean_object* v___x_1894_; 
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
v___f_1893_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1893_, 0, v_k_1884_);
lean_closure_set(v___f_1893_, 1, v___y_1886_);
lean_closure_set(v___f_1893_, 2, v___y_1887_);
v___x_1894_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1881_, v_bi_1882_, v_type_1883_, v___f_1893_, v_kind_1885_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1894_) == 0)
{
return v___x_1894_;
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___boxed(lean_object* v_name_1903_, lean_object* v_bi_1904_, lean_object* v_type_1905_, lean_object* v_k_1906_, lean_object* v_kind_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
uint8_t v_bi_boxed_1915_; uint8_t v_kind_boxed_1916_; lean_object* v_res_1917_; 
v_bi_boxed_1915_ = lean_unbox(v_bi_1904_);
v_kind_boxed_1916_ = lean_unbox(v_kind_1907_);
v_res_1917_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_1903_, v_bi_boxed_1915_, v_type_1905_, v_k_1906_, v_kind_boxed_1916_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(lean_object* v_name_1918_, lean_object* v_type_1919_, lean_object* v_k_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v___x_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = 0;
v___x_1929_ = 0;
v___x_1930_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_1918_, v___x_1928_, v_type_1919_, v_k_1920_, v___x_1929_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg___boxed(lean_object* v_name_1931_, lean_object* v_type_1932_, lean_object* v_k_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v_name_1931_, v_type_1932_, v_k_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(lean_object* v_fromType_1948_, lean_object* v_toType_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v_env_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; uint8_t v___x_1961_; 
v___x_1957_ = lean_st_ref_get(v_a_1955_);
v_env_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc_ref(v_env_1958_);
lean_dec(v___x_1957_);
v___x_1959_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__1));
v___x_1960_ = 1;
v___x_1961_ = l_Lean_Environment_contains(v_env_1958_, v___x_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec_ref(v_toType_1949_);
lean_dec_ref(v_fromType_1948_);
v___x_1962_ = lean_box(v___x_1961_);
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
else
{
lean_object* v___x_1964_; lean_object* v___f_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1964_ = lean_box(v___x_1960_);
v___f_1965_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1965_, 0, v_toType_1949_);
lean_closure_set(v___f_1965_, 1, v___x_1964_);
v___x_1966_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__3));
v___x_1967_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v___x_1966_, v_fromType_1948_, v___f_1965_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___boxed(lean_object* v_fromType_1968_, lean_object* v_toType_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v_fromType_1968_, v_toType_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0(lean_object* v_00_u03b1_1978_, lean_object* v_name_1979_, uint8_t v_bi_1980_, lean_object* v_type_1981_, lean_object* v_k_1982_, uint8_t v_kind_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_1979_, v_bi_1980_, v_type_1981_, v_k_1982_, v_kind_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1992_, lean_object* v_name_1993_, lean_object* v_bi_1994_, lean_object* v_type_1995_, lean_object* v_k_1996_, lean_object* v_kind_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v_bi_boxed_2005_; uint8_t v_kind_boxed_2006_; lean_object* v_res_2007_; 
v_bi_boxed_2005_ = lean_unbox(v_bi_1994_);
v_kind_boxed_2006_ = lean_unbox(v_kind_1997_);
v_res_2007_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0(v_00_u03b1_1992_, v_name_1993_, v_bi_boxed_2005_, v_type_1995_, v_k_1996_, v_kind_boxed_2006_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0(lean_object* v_00_u03b1_2008_, lean_object* v_name_2009_, lean_object* v_type_2010_, lean_object* v_k_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v_name_2009_, v_type_2010_, v_k_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_name_2021_, lean_object* v_type_2022_, lean_object* v_k_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0(v_00_u03b1_2020_, v_name_2021_, v_type_2022_, v_k_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v_res_2031_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(lean_object* v_x_2032_){
_start:
{
switch(lean_obj_tag(v_x_2032_))
{
case 2:
{
uint8_t v___x_2033_; 
v___x_2033_ = 1;
return v___x_2033_;
}
case 5:
{
lean_object* v_fn_2034_; 
v_fn_2034_ = lean_ctor_get(v_x_2032_, 0);
v_x_2032_ = v_fn_2034_;
goto _start;
}
case 8:
{
lean_object* v_body_2036_; 
v_body_2036_ = lean_ctor_get(v_x_2032_, 3);
v_x_2032_ = v_body_2036_;
goto _start;
}
case 10:
{
lean_object* v_expr_2038_; 
v_expr_2038_ = lean_ctor_get(v_x_2032_, 1);
v_x_2032_ = v_expr_2038_;
goto _start;
}
default: 
{
uint8_t v___x_2040_; 
v___x_2040_ = 0;
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown___boxed(lean_object* v_x_2041_){
_start:
{
uint8_t v_res_2042_; lean_object* v_r_2043_; 
v_res_2042_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v_x_2041_);
lean_dec_ref(v_x_2041_);
v_r_2043_ = lean_box(v_res_2042_);
return v_r_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(lean_object* v_e_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v___x_2047_; 
v___x_2047_ = l_Lean_Expr_hasMVar(v_e_2044_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_e_2044_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; lean_object* v_mctx_2050_; lean_object* v___x_2051_; lean_object* v_fst_2052_; lean_object* v_snd_2053_; lean_object* v___x_2054_; lean_object* v_cache_2055_; lean_object* v_zetaDeltaFVarIds_2056_; lean_object* v_postponed_2057_; lean_object* v_diag_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2067_; 
v___x_2049_ = lean_st_ref_get(v___y_2045_);
v_mctx_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc_ref(v_mctx_2050_);
lean_dec(v___x_2049_);
v___x_2051_ = l_Lean_instantiateMVarsCore(v_mctx_2050_, v_e_2044_);
v_fst_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_fst_2052_);
v_snd_2053_ = lean_ctor_get(v___x_2051_, 1);
lean_inc(v_snd_2053_);
lean_dec_ref(v___x_2051_);
v___x_2054_ = lean_st_ref_take(v___y_2045_);
v_cache_2055_ = lean_ctor_get(v___x_2054_, 1);
v_zetaDeltaFVarIds_2056_ = lean_ctor_get(v___x_2054_, 2);
v_postponed_2057_ = lean_ctor_get(v___x_2054_, 3);
v_diag_2058_ = lean_ctor_get(v___x_2054_, 4);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; 
v_unused_2068_ = lean_ctor_get(v___x_2054_, 0);
lean_dec(v_unused_2068_);
v___x_2060_ = v___x_2054_;
v_isShared_2061_ = v_isSharedCheck_2067_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_diag_2058_);
lean_inc(v_postponed_2057_);
lean_inc(v_zetaDeltaFVarIds_2056_);
lean_inc(v_cache_2055_);
lean_dec(v___x_2054_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2067_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v_snd_2053_);
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_snd_2053_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_cache_2055_);
lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_zetaDeltaFVarIds_2056_);
lean_ctor_set(v_reuseFailAlloc_2066_, 3, v_postponed_2057_);
lean_ctor_set(v_reuseFailAlloc_2066_, 4, v_diag_2058_);
v___x_2063_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_st_ref_put(v___y_2045_, v___x_2063_);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_fst_2052_);
return v___x_2065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg___boxed(lean_object* v_e_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_e_2069_, v___y_2070_);
lean_dec(v___y_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0(lean_object* v_e_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_e_2073_, v___y_2078_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___boxed(lean_object* v_e_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0(v_e_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0(lean_object* v_k_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
lean_inc(v___y_2096_);
lean_inc_ref(v___y_2095_);
lean_inc(v___y_2094_);
v___x_2102_ = lean_apply_8(v_k_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, lean_box(0));
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0(v_k_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(lean_object* v_k_2113_, uint8_t v_allowLevelAssignments_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___f_2123_; lean_object* v___x_2124_; 
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
v___f_2123_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2123_, 0, v_k_2113_);
lean_closure_set(v___f_2123_, 1, v___y_2115_);
lean_closure_set(v___f_2123_, 2, v___y_2116_);
lean_closure_set(v___f_2123_, 3, v___y_2117_);
v___x_2124_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2114_, v___f_2123_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2124_) == 0)
{
return v___x_2124_;
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___boxed(lean_object* v_k_2133_, lean_object* v_allowLevelAssignments_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2143_; lean_object* v_res_2144_; 
v_allowLevelAssignments_boxed_2143_ = lean_unbox(v_allowLevelAssignments_2134_);
v_res_2144_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v_k_2133_, v_allowLevelAssignments_boxed_2143_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1(lean_object* v_00_u03b1_2145_, lean_object* v_k_2146_, uint8_t v_allowLevelAssignments_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v_k_2146_, v_allowLevelAssignments_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___boxed(lean_object* v_00_u03b1_2157_, lean_object* v_k_2158_, lean_object* v_allowLevelAssignments_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2168_; lean_object* v_res_2169_; 
v_allowLevelAssignments_boxed_2168_ = lean_unbox(v_allowLevelAssignments_2159_);
v_res_2169_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1(v_00_u03b1_2157_, v_k_2158_, v_allowLevelAssignments_boxed_2168_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0(uint8_t v___x_2170_, lean_object* v_val_2171_, lean_object* v___x_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; uint8_t v_foApprox_2182_; uint8_t v_ctxApprox_2183_; uint8_t v_quasiPatternApprox_2184_; uint8_t v_constApprox_2185_; uint8_t v_unificationHints_2186_; uint8_t v_proofIrrelevance_2187_; uint8_t v_assignSyntheticOpaque_2188_; uint8_t v_offsetCnstrs_2189_; uint8_t v_transparency_2190_; uint8_t v_etaStruct_2191_; uint8_t v_univApprox_2192_; uint8_t v_iota_2193_; uint8_t v_beta_2194_; uint8_t v_proj_2195_; uint8_t v_zeta_2196_; uint8_t v_zetaDelta_2197_; uint8_t v_zetaUnused_2198_; uint8_t v_zetaHave_2199_; uint8_t v_canUnfoldPredicateConfig_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2221_; 
v___x_2181_ = l_Lean_Meta_Context_config(v___y_2176_);
v_foApprox_2182_ = lean_ctor_get_uint8(v___x_2181_, 0);
v_ctxApprox_2183_ = lean_ctor_get_uint8(v___x_2181_, 1);
v_quasiPatternApprox_2184_ = lean_ctor_get_uint8(v___x_2181_, 2);
v_constApprox_2185_ = lean_ctor_get_uint8(v___x_2181_, 3);
v_unificationHints_2186_ = lean_ctor_get_uint8(v___x_2181_, 5);
v_proofIrrelevance_2187_ = lean_ctor_get_uint8(v___x_2181_, 6);
v_assignSyntheticOpaque_2188_ = lean_ctor_get_uint8(v___x_2181_, 7);
v_offsetCnstrs_2189_ = lean_ctor_get_uint8(v___x_2181_, 8);
v_transparency_2190_ = lean_ctor_get_uint8(v___x_2181_, 9);
v_etaStruct_2191_ = lean_ctor_get_uint8(v___x_2181_, 10);
v_univApprox_2192_ = lean_ctor_get_uint8(v___x_2181_, 11);
v_iota_2193_ = lean_ctor_get_uint8(v___x_2181_, 12);
v_beta_2194_ = lean_ctor_get_uint8(v___x_2181_, 13);
v_proj_2195_ = lean_ctor_get_uint8(v___x_2181_, 14);
v_zeta_2196_ = lean_ctor_get_uint8(v___x_2181_, 15);
v_zetaDelta_2197_ = lean_ctor_get_uint8(v___x_2181_, 16);
v_zetaUnused_2198_ = lean_ctor_get_uint8(v___x_2181_, 17);
v_zetaHave_2199_ = lean_ctor_get_uint8(v___x_2181_, 18);
v_canUnfoldPredicateConfig_2200_ = lean_ctor_get_uint8(v___x_2181_, 19);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2202_ = v___x_2181_;
v_isShared_2203_ = v_isSharedCheck_2221_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v___x_2181_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2221_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
uint8_t v_trackZetaDelta_2204_; lean_object* v_zetaDeltaSet_2205_; lean_object* v_lctx_2206_; lean_object* v_localInstances_2207_; lean_object* v_defEqCtx_x3f_2208_; lean_object* v_synthPendingDepth_2209_; lean_object* v_customCanUnfoldPredicate_x3f_2210_; uint8_t v_univApprox_2211_; uint8_t v_inTypeClassResolution_2212_; uint8_t v_cacheInferType_2213_; lean_object* v___x_2215_; 
v_trackZetaDelta_2204_ = lean_ctor_get_uint8(v___y_2176_, sizeof(void*)*7);
v_zetaDeltaSet_2205_ = lean_ctor_get(v___y_2176_, 1);
v_lctx_2206_ = lean_ctor_get(v___y_2176_, 2);
v_localInstances_2207_ = lean_ctor_get(v___y_2176_, 3);
v_defEqCtx_x3f_2208_ = lean_ctor_get(v___y_2176_, 4);
v_synthPendingDepth_2209_ = lean_ctor_get(v___y_2176_, 5);
v_customCanUnfoldPredicate_x3f_2210_ = lean_ctor_get(v___y_2176_, 6);
v_univApprox_2211_ = lean_ctor_get_uint8(v___y_2176_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2212_ = lean_ctor_get_uint8(v___y_2176_, sizeof(void*)*7 + 2);
v_cacheInferType_2213_ = lean_ctor_get_uint8(v___y_2176_, sizeof(void*)*7 + 3);
if (v_isShared_2203_ == 0)
{
v___x_2215_ = v___x_2202_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 0, v_foApprox_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 1, v_ctxApprox_2183_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 2, v_quasiPatternApprox_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 3, v_constApprox_2185_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 5, v_unificationHints_2186_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 6, v_proofIrrelevance_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 7, v_assignSyntheticOpaque_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 8, v_offsetCnstrs_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 9, v_transparency_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 10, v_etaStruct_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 11, v_univApprox_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 12, v_iota_2193_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 13, v_beta_2194_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 14, v_proj_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 15, v_zeta_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 16, v_zetaDelta_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 17, v_zetaUnused_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 18, v_zetaHave_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, 19, v_canUnfoldPredicateConfig_2200_);
v___x_2215_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
uint64_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_ctor_set_uint8(v___x_2215_, 4, v___x_2170_);
v___x_2216_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2215_);
v___x_2217_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set_uint64(v___x_2217_, sizeof(void*)*1, v___x_2216_);
lean_inc(v_customCanUnfoldPredicate_x3f_2210_);
lean_inc(v_synthPendingDepth_2209_);
lean_inc(v_defEqCtx_x3f_2208_);
lean_inc_ref(v_localInstances_2207_);
lean_inc_ref(v_lctx_2206_);
lean_inc(v_zetaDeltaSet_2205_);
v___x_2218_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v_zetaDeltaSet_2205_);
lean_ctor_set(v___x_2218_, 2, v_lctx_2206_);
lean_ctor_set(v___x_2218_, 3, v_localInstances_2207_);
lean_ctor_set(v___x_2218_, 4, v_defEqCtx_x3f_2208_);
lean_ctor_set(v___x_2218_, 5, v_synthPendingDepth_2209_);
lean_ctor_set(v___x_2218_, 6, v_customCanUnfoldPredicate_x3f_2210_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*7, v_trackZetaDelta_2204_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*7 + 1, v_univApprox_2211_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2212_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*7 + 3, v_cacheInferType_2213_);
v___x_2219_ = l_Lean_Meta_isExprDefEqGuarded(v_val_2171_, v___x_2172_, v___x_2218_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec_ref_known(v___x_2218_, 7);
return v___x_2219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0___boxed(lean_object* v___x_2222_, lean_object* v_val_2223_, lean_object* v___x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v___x_14784__boxed_2233_; lean_object* v_res_2234_; 
v___x_14784__boxed_2233_ = lean_unbox(v___x_2222_);
v_res_2234_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0(v___x_14784__boxed_2233_, v_val_2223_, v___x_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
return v_res_2234_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2235_; double v___x_2236_; 
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = lean_float_of_nat(v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(lean_object* v_cls_2240_, lean_object* v_msg_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_ref_2247_; lean_object* v___x_2248_; lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2294_; 
v_ref_2247_ = lean_ctor_get(v___y_2244_, 2);
v___x_2248_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2294_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2294_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v_traceState_2254_; lean_object* v_env_2255_; lean_object* v_nextMacroScope_2256_; lean_object* v_ngen_2257_; lean_object* v_auxDeclNGen_2258_; lean_object* v_cache_2259_; lean_object* v_recordedDeps_2260_; lean_object* v_messages_2261_; lean_object* v_infoState_2262_; lean_object* v_snapshotTasks_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2293_; 
v___x_2253_ = lean_st_ref_take(v___y_2245_);
v_traceState_2254_ = lean_ctor_get(v___x_2253_, 4);
v_env_2255_ = lean_ctor_get(v___x_2253_, 0);
v_nextMacroScope_2256_ = lean_ctor_get(v___x_2253_, 1);
v_ngen_2257_ = lean_ctor_get(v___x_2253_, 2);
v_auxDeclNGen_2258_ = lean_ctor_get(v___x_2253_, 3);
v_cache_2259_ = lean_ctor_get(v___x_2253_, 5);
v_recordedDeps_2260_ = lean_ctor_get(v___x_2253_, 6);
v_messages_2261_ = lean_ctor_get(v___x_2253_, 7);
v_infoState_2262_ = lean_ctor_get(v___x_2253_, 8);
v_snapshotTasks_2263_ = lean_ctor_get(v___x_2253_, 9);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2265_ = v___x_2253_;
v_isShared_2266_ = v_isSharedCheck_2293_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_snapshotTasks_2263_);
lean_inc(v_infoState_2262_);
lean_inc(v_messages_2261_);
lean_inc(v_recordedDeps_2260_);
lean_inc(v_cache_2259_);
lean_inc(v_traceState_2254_);
lean_inc(v_auxDeclNGen_2258_);
lean_inc(v_ngen_2257_);
lean_inc(v_nextMacroScope_2256_);
lean_inc(v_env_2255_);
lean_dec(v___x_2253_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2293_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
uint64_t v_tid_2267_; lean_object* v_traces_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2292_; 
v_tid_2267_ = lean_ctor_get_uint64(v_traceState_2254_, sizeof(void*)*1);
v_traces_2268_ = lean_ctor_get(v_traceState_2254_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_traceState_2254_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2270_ = v_traceState_2254_;
v_isShared_2271_ = v_isSharedCheck_2292_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_traces_2268_);
lean_dec(v_traceState_2254_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2292_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; double v___x_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0);
v___x_2275_ = 0;
v___x_2276_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1));
v___x_2277_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2277_, 0, v_cls_2240_);
lean_ctor_set(v___x_2277_, 1, v___x_2273_);
lean_ctor_set(v___x_2277_, 2, v___x_2276_);
lean_ctor_set_float(v___x_2277_, sizeof(void*)*3, v___x_2274_);
lean_ctor_set_float(v___x_2277_, sizeof(void*)*3 + 8, v___x_2274_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*3 + 16, v___x_2275_);
v___x_2278_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2));
v___x_2279_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set(v___x_2279_, 1, v_a_2249_);
lean_ctor_set(v___x_2279_, 2, v___x_2278_);
lean_inc(v_ref_2247_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v_ref_2247_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = l_Lean_PersistentArray_push___redArg(v_traces_2268_, v___x_2280_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2281_);
v___x_2283_ = v___x_2270_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2281_);
lean_ctor_set_uint64(v_reuseFailAlloc_2291_, sizeof(void*)*1, v_tid_2267_);
v___x_2283_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2285_; 
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 4, v___x_2283_);
v___x_2285_ = v___x_2265_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_env_2255_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_nextMacroScope_2256_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_ngen_2257_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_auxDeclNGen_2258_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2290_, 5, v_cache_2259_);
lean_ctor_set(v_reuseFailAlloc_2290_, 6, v_recordedDeps_2260_);
lean_ctor_set(v_reuseFailAlloc_2290_, 7, v_messages_2261_);
lean_ctor_set(v_reuseFailAlloc_2290_, 8, v_infoState_2262_);
lean_ctor_set(v_reuseFailAlloc_2290_, 9, v_snapshotTasks_2263_);
v___x_2285_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_st_ref_put(v___y_2245_, v___x_2285_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2272_);
v___x_2288_ = v___x_2251_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2272_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___boxed(lean_object* v_cls_2295_, lean_object* v_msg_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v_cls_2295_, v_msg_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
return v_res_2302_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_2310_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2));
v___x_2311_ = l_Lean_Name_append(v___x_2310_, v___x_2309_);
return v___x_2311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__4));
v___x_2314_ = l_Lean_stringToMessageData(v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__6));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(lean_object* v_t_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v___x_2327_; uint8_t v_hasUncomparable_2328_; 
v___x_2327_ = lean_st_ref_get(v_a_2319_);
v_hasUncomparable_2328_ = lean_ctor_get_uint8(v___x_2327_, sizeof(void*)*1);
lean_dec(v___x_2327_);
if (v_hasUncomparable_2328_ == 0)
{
switch(lean_obj_tag(v_t_2318_))
{
case 0:
{
lean_object* v_val_2329_; uint8_t v___x_2330_; lean_object* v___y_2332_; lean_object* v___x_2346_; 
v_val_2329_ = lean_ctor_get(v_t_2318_, 2);
lean_inc_ref(v_val_2329_);
lean_dec_ref_known(v_t_2318_, 3);
v___x_2330_ = 1;
lean_inc(v_a_2325_);
lean_inc_ref(v_a_2324_);
lean_inc(v_a_2323_);
lean_inc_ref(v_a_2322_);
v___x_2346_ = lean_infer_type(v_val_2329_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2348_; lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2483_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2348_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_a_2347_, v_a_2323_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2483_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2483_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = l_Lean_Expr_cleanupAnnotations(v_a_2349_);
v___x_2354_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v_max_x3f_2356_; 
v___x_2355_ = lean_st_ref_get(v_a_2319_);
v_max_x3f_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_max_x3f_2356_);
lean_dec(v___x_2355_);
if (lean_obj_tag(v_max_x3f_2356_) == 0)
{
lean_object* v___x_2357_; uint8_t v_hasUncomparable_2358_; uint8_t v_hasUnknown_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2372_; 
v___x_2357_ = lean_st_ref_take(v_a_2319_);
v_hasUncomparable_2358_ = lean_ctor_get_uint8(v___x_2357_, sizeof(void*)*1);
v_hasUnknown_2359_ = lean_ctor_get_uint8(v___x_2357_, sizeof(void*)*1 + 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v___x_2357_, 0);
lean_dec(v_unused_2373_);
v___x_2361_ = v___x_2357_;
v_isShared_2362_ = v_isSharedCheck_2372_;
goto v_resetjp_2360_;
}
else
{
lean_dec(v___x_2357_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2372_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2353_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2364_);
v___x_2366_ = v___x_2361_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2364_);
lean_ctor_set_uint8(v_reuseFailAlloc_2371_, sizeof(void*)*1, v_hasUncomparable_2358_);
lean_ctor_set_uint8(v_reuseFailAlloc_2371_, sizeof(void*)*1 + 1, v_hasUnknown_2359_);
v___x_2366_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_st_ref_put(v_a_2319_, v___x_2366_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2363_);
v___x_2369_ = v___x_2351_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2363_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v_val_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2467_; 
lean_del_object(v___x_2351_);
v_val_2374_ = lean_ctor_get(v_max_x3f_2356_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_max_x3f_2356_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2376_ = v_max_x3f_2356_;
v_isShared_2377_ = v_isSharedCheck_2467_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_val_2374_);
lean_dec(v_max_x3f_2356_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2467_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___f_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_box(v___x_2330_);
lean_inc_ref(v___x_2353_);
lean_inc(v_val_2374_);
v___f_2379_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2379_, 0, v___x_2378_);
lean_closure_set(v___f_2379_, 1, v_val_2374_);
lean_closure_set(v___f_2379_, 2, v___x_2353_);
v___x_2380_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v___f_2379_, v___x_2354_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2458_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2383_ = v___x_2380_;
v_isShared_2384_ = v_isSharedCheck_2458_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2458_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
uint8_t v___x_2385_; 
v___x_2385_ = lean_unbox(v_a_2381_);
lean_dec(v_a_2381_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; 
lean_del_object(v___x_2383_);
lean_inc(v_val_2374_);
lean_inc_ref(v___x_2353_);
v___x_2386_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v___x_2353_, v_val_2374_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2445_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2445_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2445_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_unbox(v_a_2387_);
lean_dec(v_a_2387_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
lean_del_object(v___x_2389_);
lean_inc_ref(v___x_2353_);
lean_inc(v_val_2374_);
v___x_2392_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v_val_2374_, v___x_2353_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2432_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2432_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2432_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
uint8_t v___x_2397_; 
v___x_2397_ = lean_unbox(v_a_2393_);
lean_dec(v_a_2393_);
if (v___x_2397_ == 0)
{
lean_object* v_toCold_2398_; lean_object* v_options_2399_; uint8_t v_hasTrace_2400_; 
lean_del_object(v___x_2395_);
lean_del_object(v___x_2376_);
v_toCold_2398_ = lean_ctor_get(v_a_2324_, 0);
v_options_2399_ = lean_ctor_get(v_toCold_2398_, 2);
v_hasTrace_2400_ = lean_ctor_get_uint8(v_options_2399_, sizeof(void*)*1);
if (v_hasTrace_2400_ == 0)
{
lean_dec(v_val_2374_);
lean_dec_ref(v___x_2353_);
v___y_2332_ = v_a_2319_;
goto v___jp_2331_;
}
else
{
lean_object* v_inheritedTraceOptions_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v_inheritedTraceOptions_2401_ = lean_ctor_get(v_toCold_2398_, 11);
v___x_2402_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_2403_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_2404_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2401_, v_options_2399_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_dec(v_val_2374_);
lean_dec_ref(v___x_2353_);
v___y_2332_ = v_a_2319_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2405_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5);
v___x_2406_ = l_Lean_MessageData_ofExpr(v_val_2374_);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = l_Lean_MessageData_ofExpr(v___x_2353_);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v___x_2402_, v___x_2411_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_dec_ref_known(v___x_2412_, 1);
v___y_2332_ = v_a_2319_;
goto v___jp_2331_;
}
else
{
return v___x_2412_;
}
}
}
}
else
{
lean_object* v___x_2413_; uint8_t v_hasUncomparable_2414_; uint8_t v_hasUnknown_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v_val_2374_);
v___x_2413_ = lean_st_ref_take(v_a_2319_);
v_hasUncomparable_2414_ = lean_ctor_get_uint8(v___x_2413_, sizeof(void*)*1);
v_hasUnknown_2415_ = lean_ctor_get_uint8(v___x_2413_, sizeof(void*)*1 + 1);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v___x_2413_, 0);
lean_dec(v_unused_2431_);
v___x_2417_ = v___x_2413_;
v_isShared_2418_ = v_isSharedCheck_2430_;
goto v_resetjp_2416_;
}
else
{
lean_dec(v___x_2413_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2430_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = lean_box(0);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2353_);
v___x_2421_ = v___x_2376_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2353_);
v___x_2421_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2423_; 
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2421_);
v___x_2423_ = v___x_2417_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*1, v_hasUncomparable_2414_);
lean_ctor_set_uint8(v_reuseFailAlloc_2428_, sizeof(void*)*1 + 1, v_hasUnknown_2415_);
v___x_2423_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2424_ = lean_st_ref_put(v_a_2319_, v___x_2423_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2419_);
v___x_2426_ = v___x_2395_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2419_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_del_object(v___x_2376_);
lean_dec(v_val_2374_);
lean_dec_ref(v___x_2353_);
v_a_2433_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2392_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2392_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
lean_del_object(v___x_2376_);
lean_dec(v_val_2374_);
lean_dec_ref(v___x_2353_);
v___x_2441_ = lean_box(0);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2441_);
v___x_2443_ = v___x_2389_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_del_object(v___x_2376_);
lean_dec(v_val_2374_);
lean_dec_ref(v___x_2353_);
v_a_2446_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2386_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2386_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_del_object(v___x_2376_);
lean_dec(v_val_2374_);
lean_dec_ref(v___x_2353_);
v___x_2454_ = lean_box(0);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2454_);
v___x_2456_ = v___x_2383_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_del_object(v___x_2376_);
lean_dec(v_val_2374_);
lean_dec_ref(v___x_2353_);
v_a_2459_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2380_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2380_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
}
else
{
lean_object* v___x_2468_; lean_object* v_max_x3f_2469_; uint8_t v_hasUncomparable_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v___x_2353_);
v___x_2468_ = lean_st_ref_take(v_a_2319_);
v_max_x3f_2469_ = lean_ctor_get(v___x_2468_, 0);
v_hasUncomparable_2470_ = lean_ctor_get_uint8(v___x_2468_, sizeof(void*)*1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2472_ = v___x_2468_;
v_isShared_2473_ = v_isSharedCheck_2482_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_max_x3f_2469_);
lean_dec(v___x_2468_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2482_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2474_ = lean_box(0);
if (v_isShared_2473_ == 0)
{
v___x_2476_ = v___x_2472_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_max_x3f_2469_);
lean_ctor_set_uint8(v_reuseFailAlloc_2481_, sizeof(void*)*1, v_hasUncomparable_2470_);
v___x_2476_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_ctor_set_uint8(v___x_2476_, sizeof(void*)*1 + 1, v___x_2330_);
v___x_2477_ = lean_st_ref_put(v_a_2319_, v___x_2476_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2474_);
v___x_2479_ = v___x_2351_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_a_2484_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2346_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2346_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
v___jp_2331_:
{
lean_object* v___x_2333_; lean_object* v_max_x3f_2334_; uint8_t v_hasUnknown_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2345_; 
v___x_2333_ = lean_st_ref_take(v___y_2332_);
v_max_x3f_2334_ = lean_ctor_get(v___x_2333_, 0);
v_hasUnknown_2335_ = lean_ctor_get_uint8(v___x_2333_, sizeof(void*)*1 + 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2337_ = v___x_2333_;
v_isShared_2338_ = v_isSharedCheck_2345_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_max_x3f_2334_);
lean_dec(v___x_2333_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2345_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2339_ = lean_box(0);
if (v_isShared_2338_ == 0)
{
v___x_2341_ = v___x_2337_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_max_x3f_2334_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, sizeof(void*)*1 + 1, v_hasUnknown_2335_);
v___x_2341_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*1, v___x_2330_);
v___x_2342_ = lean_st_ref_put(v___y_2332_, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2339_);
return v___x_2343_;
}
}
}
}
case 1:
{
uint8_t v_kind_2492_; 
v_kind_2492_ = lean_ctor_get_uint8(v_t_2318_, sizeof(void*)*4);
switch(v_kind_2492_)
{
case 2:
{
lean_object* v_rhs_2493_; 
v_rhs_2493_ = lean_ctor_get(v_t_2318_, 3);
lean_inc_ref(v_rhs_2493_);
lean_dec_ref_known(v_t_2318_, 4);
v_t_2318_ = v_rhs_2493_;
goto _start;
}
case 3:
{
lean_object* v_lhs_2495_; 
v_lhs_2495_ = lean_ctor_get(v_t_2318_, 2);
lean_inc_ref(v_lhs_2495_);
lean_dec_ref_known(v_t_2318_, 4);
v_t_2318_ = v_lhs_2495_;
goto _start;
}
default: 
{
lean_object* v_lhs_2497_; lean_object* v_rhs_2498_; lean_object* v___x_2499_; 
v_lhs_2497_ = lean_ctor_get(v_t_2318_, 2);
lean_inc_ref(v_lhs_2497_);
v_rhs_2498_ = lean_ctor_get(v_t_2318_, 3);
lean_inc_ref(v_rhs_2498_);
lean_dec_ref_known(v_t_2318_, 4);
v___x_2499_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_lhs_2497_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_dec_ref_known(v___x_2499_, 1);
v_t_2318_ = v_rhs_2498_;
goto _start;
}
else
{
lean_dec_ref(v_rhs_2498_);
return v___x_2499_;
}
}
}
}
case 2:
{
lean_object* v_arg_2501_; 
v_arg_2501_ = lean_ctor_get(v_t_2318_, 2);
lean_inc_ref(v_arg_2501_);
lean_dec_ref_known(v_t_2318_, 3);
v_t_2318_ = v_arg_2501_;
goto _start;
}
default: 
{
lean_object* v_nested_2503_; 
v_nested_2503_ = lean_ctor_get(v_t_2318_, 3);
lean_inc_ref(v_nested_2503_);
lean_dec_ref_known(v_t_2318_, 4);
v_t_2318_ = v_nested_2503_;
goto _start;
}
}
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v_t_2318_);
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___boxed(lean_object* v_t_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_t_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2(lean_object* v_cls_2517_, lean_object* v_msg_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v_cls_2517_, v_msg_2518_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___boxed(lean_object* v_cls_2528_, lean_object* v_msg_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2(v_cls_2528_, v_msg_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(lean_object* v_e_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = l_Lean_Expr_hasMVar(v_e_2539_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_e_2539_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v_mctx_2545_; lean_object* v___x_2546_; lean_object* v_fst_2547_; lean_object* v_snd_2548_; lean_object* v___x_2549_; lean_object* v_cache_2550_; lean_object* v_zetaDeltaFVarIds_2551_; lean_object* v_postponed_2552_; lean_object* v_diag_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2562_; 
v___x_2544_ = lean_st_ref_get(v___y_2540_);
v_mctx_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_ref(v_mctx_2545_);
lean_dec(v___x_2544_);
v___x_2546_ = l_Lean_instantiateMVarsCore(v_mctx_2545_, v_e_2539_);
v_fst_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_fst_2547_);
v_snd_2548_ = lean_ctor_get(v___x_2546_, 1);
lean_inc(v_snd_2548_);
lean_dec_ref(v___x_2546_);
v___x_2549_ = lean_st_ref_take(v___y_2540_);
v_cache_2550_ = lean_ctor_get(v___x_2549_, 1);
v_zetaDeltaFVarIds_2551_ = lean_ctor_get(v___x_2549_, 2);
v_postponed_2552_ = lean_ctor_get(v___x_2549_, 3);
v_diag_2553_ = lean_ctor_get(v___x_2549_, 4);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2549_, 0);
lean_dec(v_unused_2563_);
v___x_2555_ = v___x_2549_;
v_isShared_2556_ = v_isSharedCheck_2562_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_diag_2553_);
lean_inc(v_postponed_2552_);
lean_inc(v_zetaDeltaFVarIds_2551_);
lean_inc(v_cache_2550_);
lean_dec(v___x_2549_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2562_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v_snd_2548_);
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_snd_2548_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_cache_2550_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_zetaDeltaFVarIds_2551_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_postponed_2552_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_diag_2553_);
v___x_2558_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_st_ref_put(v___y_2540_, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_fst_2547_);
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg___boxed(lean_object* v_e_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(v_e_2564_, v___y_2565_);
lean_dec(v___y_2565_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0(lean_object* v_e_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(v_e_2568_, v___y_2572_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___boxed(lean_object* v_e_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0(v_e_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(lean_object* v_t_2586_, lean_object* v_expectedType_x3f_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_max_x3f_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; 
if (lean_obj_tag(v_expectedType_x3f_2587_) == 0)
{
v_max_x3f_2596_ = v_expectedType_x3f_2587_;
v___y_2597_ = v_a_2588_;
v___y_2598_ = v_a_2589_;
v___y_2599_ = v_a_2590_;
v___y_2600_ = v_a_2591_;
v___y_2601_ = v_a_2592_;
v___y_2602_ = v_a_2593_;
goto v___jp_2595_;
}
else
{
lean_object* v_val_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2637_; 
v_val_2625_ = lean_ctor_get(v_expectedType_x3f_2587_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_expectedType_x3f_2587_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2627_ = v_expectedType_x3f_2587_;
v_isShared_2628_ = v_isSharedCheck_2637_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_val_2625_);
lean_dec(v_expectedType_x3f_2587_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2637_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v_a_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2629_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(v_val_2625_, v_a_2591_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref(v___x_2629_);
v___x_2631_ = l_Lean_Expr_cleanupAnnotations(v_a_2630_);
v___x_2632_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2634_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2631_);
v___x_2634_ = v___x_2627_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2631_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
v_max_x3f_2596_ = v___x_2634_;
v___y_2597_ = v_a_2588_;
v___y_2598_ = v_a_2589_;
v___y_2599_ = v_a_2590_;
v___y_2600_ = v_a_2591_;
v___y_2601_ = v_a_2592_;
v___y_2602_ = v_a_2593_;
goto v___jp_2595_;
}
}
else
{
lean_object* v___x_2636_; 
lean_dec_ref(v___x_2631_);
lean_del_object(v___x_2627_);
v___x_2636_ = lean_box(0);
v_max_x3f_2596_ = v___x_2636_;
v___y_2597_ = v_a_2588_;
v___y_2598_ = v_a_2589_;
v___y_2599_ = v_a_2590_;
v___y_2600_ = v_a_2591_;
v___y_2601_ = v_a_2592_;
v___y_2602_ = v_a_2593_;
goto v___jp_2595_;
}
}
}
v___jp_2595_:
{
uint8_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2603_ = 0;
v___x_2604_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2604_, 0, v_max_x3f_2596_);
lean_ctor_set_uint8(v___x_2604_, sizeof(void*)*1, v___x_2603_);
lean_ctor_set_uint8(v___x_2604_, sizeof(void*)*1 + 1, v___x_2603_);
v___x_2605_ = lean_st_mk_ref(v___x_2604_);
v___x_2606_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_t_2586_, v___x_2605_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2615_; 
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; 
v_unused_2616_ = lean_ctor_get(v___x_2606_, 0);
lean_dec(v_unused_2616_);
v___x_2608_ = v___x_2606_;
v_isShared_2609_ = v_isSharedCheck_2615_;
goto v_resetjp_2607_;
}
else
{
lean_dec(v___x_2606_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2615_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2610_ = lean_st_ref_get(v___x_2605_);
v___x_2611_ = lean_st_ref_get(v___x_2605_);
lean_dec(v___x_2605_);
lean_dec(v___x_2611_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2610_);
v___x_2613_ = v___x_2608_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2610_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v___x_2605_);
v_a_2617_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2606_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2606_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze___boxed(lean_object* v_t_2638_, lean_object* v_expectedType_x3f_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v_t_2638_, v_expectedType_x3f_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(uint8_t v_lazy_2650_, lean_object* v_f_2651_, lean_object* v_lhs_2652_, lean_object* v_rhs_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_rhs_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; 
if (v_lazy_2650_ == 0)
{
v_rhs_2662_ = v_rhs_2653_;
v___y_2663_ = v_a_2654_;
v___y_2664_ = v_a_2655_;
v___y_2665_ = v_a_2656_;
v___y_2666_ = v_a_2657_;
v___y_2667_ = v_a_2658_;
v___y_2668_ = v_a_2659_;
goto v___jp_2661_;
}
else
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_Meta_mkFunUnit___redArg(v_rhs_2653_, v_a_2658_, v_a_2659_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v_rhs_2662_ = v_a_2680_;
v___y_2663_ = v_a_2654_;
v___y_2664_ = v_a_2655_;
v___y_2665_ = v_a_2656_;
v___y_2666_ = v_a_2657_;
v___y_2667_ = v_a_2658_;
v___y_2668_ = v_a_2659_;
goto v___jp_2661_;
}
else
{
lean_dec_ref(v_lhs_2652_);
lean_dec_ref(v_f_2651_);
return v___x_2679_;
}
}
v___jp_2661_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; lean_object* v___x_2678_; 
v___x_2669_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
v___x_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_lhs_2652_);
v___x_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_rhs_2662_);
v___x_2672_ = lean_unsigned_to_nat(2u);
v___x_2673_ = lean_mk_empty_array_with_capacity(v___x_2672_);
v___x_2674_ = lean_array_push(v___x_2673_, v___x_2670_);
v___x_2675_ = lean_array_push(v___x_2674_, v___x_2671_);
v___x_2676_ = lean_box(0);
v___x_2677_ = 0;
v___x_2678_ = l_Lean_Elab_Term_elabAppArgs(v_f_2651_, v___x_2669_, v___x_2675_, v___x_2676_, v___x_2677_, v___x_2677_, v___x_2677_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___boxed(lean_object* v_lazy_2681_, lean_object* v_f_2682_, lean_object* v_lhs_2683_, lean_object* v_rhs_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
uint8_t v_lazy_boxed_2692_; lean_object* v_res_2693_; 
v_lazy_boxed_2692_ = lean_unbox(v_lazy_2681_);
v_res_2693_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v_lazy_boxed_2692_, v_f_2682_, v_lhs_2683_, v_rhs_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(lean_object* v_f_2694_, lean_object* v_arg_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; lean_object* v___x_2710_; 
v___x_2703_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v_arg_2695_);
v___x_2705_ = lean_unsigned_to_nat(1u);
v___x_2706_ = lean_mk_empty_array_with_capacity(v___x_2705_);
v___x_2707_ = lean_array_push(v___x_2706_, v___x_2704_);
v___x_2708_ = lean_box(0);
v___x_2709_ = 0;
v___x_2710_ = l_Lean_Elab_Term_elabAppArgs(v_f_2694_, v___x_2703_, v___x_2707_, v___x_2708_, v___x_2709_, v___x_2709_, v___x_2709_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp___boxed(lean_object* v_f_2711_, lean_object* v_arg_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(v_f_2711_, v_arg_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___y_2721_, lean_object* v_mkInfoTree_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v_a_2728_, lean_object* v_a_x3f_2729_){
_start:
{
lean_object* v___x_2731_; lean_object* v_infoState_2732_; lean_object* v_trees_2733_; lean_object* v___x_2734_; 
v___x_2731_ = lean_st_ref_get(v___y_2721_);
v_infoState_2732_ = lean_ctor_get(v___x_2731_, 8);
lean_inc_ref(v_infoState_2732_);
lean_dec(v___x_2731_);
v_trees_2733_ = lean_ctor_get(v_infoState_2732_, 2);
lean_inc_ref(v_trees_2733_);
lean_dec_ref(v_infoState_2732_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2727_);
lean_inc(v___y_2726_);
lean_inc_ref(v___y_2725_);
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2723_);
v___x_2734_ = lean_apply_8(v_mkInfoTree_2722_, v_trees_2733_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2721_, lean_box(0));
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2774_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2774_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2774_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v_infoState_2740_; lean_object* v_env_2741_; lean_object* v_nextMacroScope_2742_; lean_object* v_ngen_2743_; lean_object* v_auxDeclNGen_2744_; lean_object* v_traceState_2745_; lean_object* v_cache_2746_; lean_object* v_recordedDeps_2747_; lean_object* v_messages_2748_; lean_object* v_snapshotTasks_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2773_; 
v___x_2739_ = lean_st_ref_take(v___y_2721_);
v_infoState_2740_ = lean_ctor_get(v___x_2739_, 8);
v_env_2741_ = lean_ctor_get(v___x_2739_, 0);
v_nextMacroScope_2742_ = lean_ctor_get(v___x_2739_, 1);
v_ngen_2743_ = lean_ctor_get(v___x_2739_, 2);
v_auxDeclNGen_2744_ = lean_ctor_get(v___x_2739_, 3);
v_traceState_2745_ = lean_ctor_get(v___x_2739_, 4);
v_cache_2746_ = lean_ctor_get(v___x_2739_, 5);
v_recordedDeps_2747_ = lean_ctor_get(v___x_2739_, 6);
v_messages_2748_ = lean_ctor_get(v___x_2739_, 7);
v_snapshotTasks_2749_ = lean_ctor_get(v___x_2739_, 9);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2751_ = v___x_2739_;
v_isShared_2752_ = v_isSharedCheck_2773_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_snapshotTasks_2749_);
lean_inc(v_infoState_2740_);
lean_inc(v_messages_2748_);
lean_inc(v_recordedDeps_2747_);
lean_inc(v_cache_2746_);
lean_inc(v_traceState_2745_);
lean_inc(v_auxDeclNGen_2744_);
lean_inc(v_ngen_2743_);
lean_inc(v_nextMacroScope_2742_);
lean_inc(v_env_2741_);
lean_dec(v___x_2739_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2773_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
uint8_t v_enabled_2753_; lean_object* v_assignment_2754_; lean_object* v_lazyAssignment_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2771_; 
v_enabled_2753_ = lean_ctor_get_uint8(v_infoState_2740_, sizeof(void*)*3);
v_assignment_2754_ = lean_ctor_get(v_infoState_2740_, 0);
v_lazyAssignment_2755_ = lean_ctor_get(v_infoState_2740_, 1);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_infoState_2740_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v_infoState_2740_, 2);
lean_dec(v_unused_2772_);
v___x_2757_ = v_infoState_2740_;
v_isShared_2758_ = v_isSharedCheck_2771_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_lazyAssignment_2755_);
lean_inc(v_assignment_2754_);
lean_dec(v_infoState_2740_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2771_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2759_ = lean_box(0);
v___x_2760_ = l_Lean_PersistentArray_push___redArg(v_a_2728_, v_a_2735_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 2, v___x_2760_);
v___x_2762_ = v___x_2757_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_assignment_2754_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_lazyAssignment_2755_);
lean_ctor_set(v_reuseFailAlloc_2770_, 2, v___x_2760_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, sizeof(void*)*3, v_enabled_2753_);
v___x_2762_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2764_; 
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 8, v___x_2762_);
v___x_2764_ = v___x_2751_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_env_2741_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_nextMacroScope_2742_);
lean_ctor_set(v_reuseFailAlloc_2769_, 2, v_ngen_2743_);
lean_ctor_set(v_reuseFailAlloc_2769_, 3, v_auxDeclNGen_2744_);
lean_ctor_set(v_reuseFailAlloc_2769_, 4, v_traceState_2745_);
lean_ctor_set(v_reuseFailAlloc_2769_, 5, v_cache_2746_);
lean_ctor_set(v_reuseFailAlloc_2769_, 6, v_recordedDeps_2747_);
lean_ctor_set(v_reuseFailAlloc_2769_, 7, v_messages_2748_);
lean_ctor_set(v_reuseFailAlloc_2769_, 8, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2769_, 9, v_snapshotTasks_2749_);
v___x_2764_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2765_ = lean_st_ref_put(v___y_2721_, v___x_2764_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2759_);
v___x_2767_ = v___x_2737_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2759_);
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
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec_ref(v_a_2728_);
v_a_2775_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2734_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2734_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_2783_, lean_object* v_mkInfoTree_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v_a_2790_, lean_object* v_a_x3f_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_2783_, v_mkInfoTree_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v_a_2790_, v_a_x3f_2791_);
lean_dec(v_a_x3f_2791_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2783_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2794_, lean_object* v_mkInfoTree_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___x_2803_; lean_object* v_infoState_2804_; uint8_t v_enabled_2805_; 
v___x_2803_ = lean_st_ref_get(v___y_2801_);
v_infoState_2804_ = lean_ctor_get(v___x_2803_, 8);
lean_inc_ref(v_infoState_2804_);
lean_dec(v___x_2803_);
v_enabled_2805_ = lean_ctor_get_uint8(v_infoState_2804_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2804_);
if (v_enabled_2805_ == 0)
{
lean_object* v___x_2806_; 
lean_dec_ref(v_mkInfoTree_2795_);
lean_inc(v___y_2801_);
lean_inc_ref(v___y_2800_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
v___x_2806_ = lean_apply_7(v_x_2794_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, lean_box(0));
return v___x_2806_;
}
else
{
lean_object* v___x_2807_; lean_object* v_a_2808_; lean_object* v_r_2809_; 
v___x_2807_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v___y_2801_);
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref(v___x_2807_);
lean_inc(v___y_2801_);
lean_inc_ref(v___y_2800_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
v_r_2809_ = lean_apply_7(v_x_2794_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, lean_box(0));
if (lean_obj_tag(v_r_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2834_; 
v_a_2810_ = lean_ctor_get(v_r_2809_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_r_2809_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2812_ = v_r_2809_;
v_isShared_2813_ = v_isSharedCheck_2834_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v_r_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2834_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
lean_inc(v_a_2810_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set_tag(v___x_2812_, 1);
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_2801_, v_mkInfoTree_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v_a_2808_, v___x_2815_);
lean_dec_ref(v___x_2815_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2816_, 0);
lean_dec(v_unused_2824_);
v___x_2818_ = v___x_2816_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v___x_2816_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_a_2810_);
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2810_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_a_2810_);
v_a_2825_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2816_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2816_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_a_2835_ = lean_ctor_get(v_r_2809_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v_r_2809_, 1);
v___x_2836_ = lean_box(0);
v___x_2837_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_2801_, v_mkInfoTree_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v_a_2808_, v___x_2836_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v___x_2837_, 0);
lean_dec(v_unused_2845_);
v___x_2839_ = v___x_2837_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_dec(v___x_2837_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set_tag(v___x_2839_, 1);
lean_ctor_set(v___x_2839_, 0, v_a_2835_);
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2835_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v_a_2835_);
v_a_2846_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2837_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2837_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2854_, lean_object* v_mkInfoTree_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_2854_, v_mkInfoTree_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0(lean_object* v_stx_2864_, lean_object* v_output_2865_, lean_object* v_trees_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_lctx_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_lctx_2874_ = lean_ctor_get(v___y_2869_, 2);
lean_inc_ref(v_lctx_2874_);
v___x_2875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2875_, 0, v_lctx_2874_);
lean_ctor_set(v___x_2875_, 1, v_stx_2864_);
lean_ctor_set(v___x_2875_, 2, v_output_2865_);
v___x_2876_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
v___x_2877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v_trees_2866_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_stx_2879_, lean_object* v_output_2880_, lean_object* v_trees_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0(v_stx_2879_, v_output_2880_, v_trees_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(lean_object* v_stx_2890_, lean_object* v_output_2891_, lean_object* v_x_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___f_2900_; lean_object* v___x_2901_; 
v___f_2900_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2900_, 0, v_stx_2890_);
lean_closure_set(v___f_2900_, 1, v_output_2891_);
v___x_2901_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_2892_, v___f_2900_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___boxed(lean_object* v_stx_2902_, lean_object* v_output_2903_, lean_object* v_x_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_stx_2902_, v_output_2903_, v_x_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(lean_object* v_beforeStx_2913_, lean_object* v_afterStx_2914_, lean_object* v_x_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_inc(v_afterStx_2914_);
lean_inc(v_beforeStx_2913_);
v___x_2923_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___boxed), 11, 4);
lean_closure_set(v___x_2923_, 0, lean_box(0));
lean_closure_set(v___x_2923_, 1, v_beforeStx_2913_);
lean_closure_set(v___x_2923_, 2, v_afterStx_2914_);
lean_closure_set(v___x_2923_, 3, v_x_2915_);
v___x_2924_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_beforeStx_2913_, v_afterStx_2914_, v___x_2923_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
v_a_2933_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2924_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2924_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg___boxed(lean_object* v_beforeStx_2941_, lean_object* v_afterStx_2942_, lean_object* v_x_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(v_beforeStx_2941_, v_afterStx_2942_, v_x_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0(lean_object* v_00_u03b1_2952_, lean_object* v_beforeStx_2953_, lean_object* v_afterStx_2954_, lean_object* v_x_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(v_beforeStx_2953_, v_afterStx_2954_, v_x_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___boxed(lean_object* v_00_u03b1_2964_, lean_object* v_beforeStx_2965_, lean_object* v_afterStx_2966_, lean_object* v_x_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0(v_00_u03b1_2964_, v_beforeStx_2965_, v_afterStx_2966_, v_x_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0(lean_object* v_lhs_2976_, lean_object* v_rhs_2977_, uint8_t v_kind_2978_, lean_object* v_f_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_lhs_2976_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v___x_2989_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_rhs_2977_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; uint8_t v___x_2991_; uint8_t v___x_2992_; lean_object* v___x_2993_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = 1;
v___x_2992_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_2978_, v___x_2991_);
v___x_2993_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v___x_2992_, v_f_2979_, v_a_2988_, v_a_2990_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_2993_;
}
else
{
lean_dec(v_a_2988_);
lean_dec_ref(v_f_2979_);
return v___x_2989_;
}
}
else
{
lean_dec_ref(v_f_2979_);
lean_dec_ref(v_rhs_2977_);
return v___x_2987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0___boxed(lean_object* v_lhs_2994_, lean_object* v_rhs_2995_, lean_object* v_kind_2996_, lean_object* v_f_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
uint8_t v_kind_7816__boxed_3005_; lean_object* v_res_3006_; 
v_kind_7816__boxed_3005_ = lean_unbox(v_kind_2996_);
v_res_3006_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0(v_lhs_2994_, v_rhs_2995_, v_kind_7816__boxed_3005_, v_f_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1___boxed(lean_object* v_arg_3007_, lean_object* v_f_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1(v_arg_3007_, v_f_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___boxed(lean_object* v_t_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_t_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(lean_object* v_t_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
switch(lean_obj_tag(v_t_3026_))
{
case 0:
{
lean_object* v_infoTrees_3034_; lean_object* v_val_3035_; lean_object* v___x_3036_; lean_object* v_infoState_3037_; lean_object* v_env_3038_; lean_object* v_nextMacroScope_3039_; lean_object* v_ngen_3040_; lean_object* v_auxDeclNGen_3041_; lean_object* v_traceState_3042_; lean_object* v_cache_3043_; lean_object* v_recordedDeps_3044_; lean_object* v_messages_3045_; lean_object* v_snapshotTasks_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3067_; 
v_infoTrees_3034_ = lean_ctor_get(v_t_3026_, 1);
lean_inc_ref(v_infoTrees_3034_);
v_val_3035_ = lean_ctor_get(v_t_3026_, 2);
lean_inc_ref(v_val_3035_);
lean_dec_ref_known(v_t_3026_, 3);
v___x_3036_ = lean_st_ref_take(v_a_3032_);
v_infoState_3037_ = lean_ctor_get(v___x_3036_, 8);
v_env_3038_ = lean_ctor_get(v___x_3036_, 0);
v_nextMacroScope_3039_ = lean_ctor_get(v___x_3036_, 1);
v_ngen_3040_ = lean_ctor_get(v___x_3036_, 2);
v_auxDeclNGen_3041_ = lean_ctor_get(v___x_3036_, 3);
v_traceState_3042_ = lean_ctor_get(v___x_3036_, 4);
v_cache_3043_ = lean_ctor_get(v___x_3036_, 5);
v_recordedDeps_3044_ = lean_ctor_get(v___x_3036_, 6);
v_messages_3045_ = lean_ctor_get(v___x_3036_, 7);
v_snapshotTasks_3046_ = lean_ctor_get(v___x_3036_, 9);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3048_ = v___x_3036_;
v_isShared_3049_ = v_isSharedCheck_3067_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_snapshotTasks_3046_);
lean_inc(v_infoState_3037_);
lean_inc(v_messages_3045_);
lean_inc(v_recordedDeps_3044_);
lean_inc(v_cache_3043_);
lean_inc(v_traceState_3042_);
lean_inc(v_auxDeclNGen_3041_);
lean_inc(v_ngen_3040_);
lean_inc(v_nextMacroScope_3039_);
lean_inc(v_env_3038_);
lean_dec(v___x_3036_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3067_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
uint8_t v_enabled_3050_; lean_object* v_assignment_3051_; lean_object* v_lazyAssignment_3052_; lean_object* v_trees_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3066_; 
v_enabled_3050_ = lean_ctor_get_uint8(v_infoState_3037_, sizeof(void*)*3);
v_assignment_3051_ = lean_ctor_get(v_infoState_3037_, 0);
v_lazyAssignment_3052_ = lean_ctor_get(v_infoState_3037_, 1);
v_trees_3053_ = lean_ctor_get(v_infoState_3037_, 2);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_infoState_3037_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3055_ = v_infoState_3037_;
v_isShared_3056_ = v_isSharedCheck_3066_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_trees_3053_);
lean_inc(v_lazyAssignment_3052_);
lean_inc(v_assignment_3051_);
lean_dec(v_infoState_3037_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3066_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3057_; lean_object* v___x_3059_; 
v___x_3057_ = l_Lean_PersistentArray_append___redArg(v_trees_3053_, v_infoTrees_3034_);
lean_dec_ref(v_infoTrees_3034_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 2, v___x_3057_);
v___x_3059_ = v___x_3055_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_assignment_3051_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_lazyAssignment_3052_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v___x_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3065_, sizeof(void*)*3, v_enabled_3050_);
v___x_3059_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3061_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 8, v___x_3059_);
v___x_3061_ = v___x_3048_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_env_3038_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_nextMacroScope_3039_);
lean_ctor_set(v_reuseFailAlloc_3064_, 2, v_ngen_3040_);
lean_ctor_set(v_reuseFailAlloc_3064_, 3, v_auxDeclNGen_3041_);
lean_ctor_set(v_reuseFailAlloc_3064_, 4, v_traceState_3042_);
lean_ctor_set(v_reuseFailAlloc_3064_, 5, v_cache_3043_);
lean_ctor_set(v_reuseFailAlloc_3064_, 6, v_recordedDeps_3044_);
lean_ctor_set(v_reuseFailAlloc_3064_, 7, v_messages_3045_);
lean_ctor_set(v_reuseFailAlloc_3064_, 8, v___x_3059_);
lean_ctor_set(v_reuseFailAlloc_3064_, 9, v_snapshotTasks_3046_);
v___x_3061_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_st_ref_put(v_a_3032_, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v_val_3035_);
return v___x_3063_;
}
}
}
}
}
case 1:
{
lean_object* v_ref_3068_; uint8_t v_kind_3069_; lean_object* v_f_3070_; lean_object* v_lhs_3071_; lean_object* v_rhs_3072_; lean_object* v_toCold_3073_; lean_object* v_currRecDepth_3074_; lean_object* v_ref_3075_; uint16_t v_optionFlags_3076_; uint8_t v_suppressElabErrors_3077_; uint8_t v_isRecordingDeps_3078_; lean_object* v___x_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; lean_object* v_ref_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_ref_3068_ = lean_ctor_get(v_t_3026_, 0);
lean_inc(v_ref_3068_);
v_kind_3069_ = lean_ctor_get_uint8(v_t_3026_, sizeof(void*)*4);
v_f_3070_ = lean_ctor_get(v_t_3026_, 1);
lean_inc_ref(v_f_3070_);
v_lhs_3071_ = lean_ctor_get(v_t_3026_, 2);
lean_inc_ref(v_lhs_3071_);
v_rhs_3072_ = lean_ctor_get(v_t_3026_, 3);
lean_inc_ref(v_rhs_3072_);
lean_dec_ref_known(v_t_3026_, 4);
v_toCold_3073_ = lean_ctor_get(v_a_3031_, 0);
v_currRecDepth_3074_ = lean_ctor_get(v_a_3031_, 1);
v_ref_3075_ = lean_ctor_get(v_a_3031_, 2);
v_optionFlags_3076_ = lean_ctor_get_uint16(v_a_3031_, sizeof(void*)*3);
v_suppressElabErrors_3077_ = lean_ctor_get_uint8(v_a_3031_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3078_ = lean_ctor_get_uint8(v_a_3031_, sizeof(void*)*3 + 3);
v___x_3079_ = lean_box(v_kind_3069_);
v___f_3080_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3080_, 0, v_lhs_3071_);
lean_closure_set(v___f_3080_, 1, v_rhs_3072_);
lean_closure_set(v___f_3080_, 2, v___x_3079_);
lean_closure_set(v___f_3080_, 3, v_f_3070_);
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_box(0);
v___x_3083_ = 0;
v_ref_3084_ = l_Lean_replaceRef(v_ref_3068_, v_ref_3075_);
lean_inc(v_currRecDepth_3074_);
lean_inc_ref(v_toCold_3073_);
v___x_3085_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3085_, 0, v_toCold_3073_);
lean_ctor_set(v___x_3085_, 1, v_currRecDepth_3074_);
lean_ctor_set(v___x_3085_, 2, v_ref_3084_);
lean_ctor_set_uint16(v___x_3085_, sizeof(void*)*3, v_optionFlags_3076_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*3 + 2, v_suppressElabErrors_3077_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*3 + 3, v_isRecordingDeps_3078_);
v___x_3086_ = l_Lean_Elab_Term_withTermInfoContext_x27(v___x_3081_, v_ref_3068_, v___f_3080_, v___x_3082_, v___x_3082_, v___x_3083_, v___x_3083_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v___x_3085_, v_a_3032_);
lean_dec_ref_known(v___x_3085_, 3);
return v___x_3086_;
}
case 2:
{
lean_object* v_ref_3087_; lean_object* v_f_3088_; lean_object* v_arg_3089_; lean_object* v_toCold_3090_; lean_object* v_currRecDepth_3091_; lean_object* v_ref_3092_; uint16_t v_optionFlags_3093_; uint8_t v_suppressElabErrors_3094_; uint8_t v_isRecordingDeps_3095_; lean_object* v___f_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; lean_object* v_ref_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v_ref_3087_ = lean_ctor_get(v_t_3026_, 0);
lean_inc(v_ref_3087_);
v_f_3088_ = lean_ctor_get(v_t_3026_, 1);
lean_inc_ref(v_f_3088_);
v_arg_3089_ = lean_ctor_get(v_t_3026_, 2);
lean_inc_ref(v_arg_3089_);
lean_dec_ref_known(v_t_3026_, 3);
v_toCold_3090_ = lean_ctor_get(v_a_3031_, 0);
v_currRecDepth_3091_ = lean_ctor_get(v_a_3031_, 1);
v_ref_3092_ = lean_ctor_get(v_a_3031_, 2);
v_optionFlags_3093_ = lean_ctor_get_uint16(v_a_3031_, sizeof(void*)*3);
v_suppressElabErrors_3094_ = lean_ctor_get_uint8(v_a_3031_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3095_ = lean_ctor_get_uint8(v_a_3031_, sizeof(void*)*3 + 3);
v___f_3096_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3096_, 0, v_arg_3089_);
lean_closure_set(v___f_3096_, 1, v_f_3088_);
v___x_3097_ = lean_box(0);
v___x_3098_ = lean_box(0);
v___x_3099_ = 0;
v_ref_3100_ = l_Lean_replaceRef(v_ref_3087_, v_ref_3092_);
lean_inc(v_currRecDepth_3091_);
lean_inc_ref(v_toCold_3090_);
v___x_3101_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3101_, 0, v_toCold_3090_);
lean_ctor_set(v___x_3101_, 1, v_currRecDepth_3091_);
lean_ctor_set(v___x_3101_, 2, v_ref_3100_);
lean_ctor_set_uint16(v___x_3101_, sizeof(void*)*3, v_optionFlags_3093_);
lean_ctor_set_uint8(v___x_3101_, sizeof(void*)*3 + 2, v_suppressElabErrors_3094_);
lean_ctor_set_uint8(v___x_3101_, sizeof(void*)*3 + 3, v_isRecordingDeps_3095_);
v___x_3102_ = l_Lean_Elab_Term_withTermInfoContext_x27(v___x_3097_, v_ref_3087_, v___f_3096_, v___x_3098_, v___x_3098_, v___x_3099_, v___x_3099_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v___x_3101_, v_a_3032_);
lean_dec_ref_known(v___x_3101_, 3);
return v___x_3102_;
}
default: 
{
lean_object* v_macroName_3103_; lean_object* v_stx_3104_; lean_object* v_stx_x27_3105_; lean_object* v_nested_3106_; lean_object* v_toCold_3107_; lean_object* v_currRecDepth_3108_; lean_object* v_ref_3109_; uint16_t v_optionFlags_3110_; uint8_t v_suppressElabErrors_3111_; uint8_t v_isRecordingDeps_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; lean_object* v_ref_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_macroName_3103_ = lean_ctor_get(v_t_3026_, 0);
lean_inc(v_macroName_3103_);
v_stx_3104_ = lean_ctor_get(v_t_3026_, 1);
lean_inc_n(v_stx_3104_, 2);
v_stx_x27_3105_ = lean_ctor_get(v_t_3026_, 2);
lean_inc(v_stx_x27_3105_);
v_nested_3106_ = lean_ctor_get(v_t_3026_, 3);
lean_inc_ref(v_nested_3106_);
lean_dec_ref_known(v_t_3026_, 4);
v_toCold_3107_ = lean_ctor_get(v_a_3031_, 0);
v_currRecDepth_3108_ = lean_ctor_get(v_a_3031_, 1);
v_ref_3109_ = lean_ctor_get(v_a_3031_, 2);
v_optionFlags_3110_ = lean_ctor_get_uint16(v_a_3031_, sizeof(void*)*3);
v_suppressElabErrors_3111_ = lean_ctor_get_uint8(v_a_3031_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3112_ = lean_ctor_get_uint8(v_a_3031_, sizeof(void*)*3 + 3);
v___x_3113_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___boxed), 8, 1);
lean_closure_set(v___x_3113_, 0, v_nested_3106_);
v___x_3114_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___boxed), 11, 4);
lean_closure_set(v___x_3114_, 0, lean_box(0));
lean_closure_set(v___x_3114_, 1, v_stx_3104_);
lean_closure_set(v___x_3114_, 2, v_stx_x27_3105_);
lean_closure_set(v___x_3114_, 3, v___x_3113_);
v___x_3115_ = lean_box(0);
v___x_3116_ = 0;
v_ref_3117_ = l_Lean_replaceRef(v_stx_3104_, v_ref_3109_);
lean_inc(v_currRecDepth_3108_);
lean_inc_ref(v_toCold_3107_);
v___x_3118_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3118_, 0, v_toCold_3107_);
lean_ctor_set(v___x_3118_, 1, v_currRecDepth_3108_);
lean_ctor_set(v___x_3118_, 2, v_ref_3117_);
lean_ctor_set_uint16(v___x_3118_, sizeof(void*)*3, v_optionFlags_3110_);
lean_ctor_set_uint8(v___x_3118_, sizeof(void*)*3 + 2, v_suppressElabErrors_3111_);
lean_ctor_set_uint8(v___x_3118_, sizeof(void*)*3 + 3, v_isRecordingDeps_3112_);
v___x_3119_ = l_Lean_Elab_Term_withTermInfoContext_x27(v_macroName_3103_, v_stx_3104_, v___x_3114_, v___x_3115_, v___x_3115_, v___x_3116_, v___x_3116_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v___x_3118_, v_a_3032_);
lean_dec_ref_known(v___x_3118_, 3);
return v___x_3119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1(lean_object* v_arg_3120_, lean_object* v_f_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_arg_3120_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3131_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref_known(v___x_3129_, 1);
v___x_3131_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(v_f_3121_, v_a_3130_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
return v___x_3131_;
}
else
{
lean_dec_ref(v_f_3121_);
return v___x_3129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0(lean_object* v_00_u03b1_3132_, lean_object* v_stx_3133_, lean_object* v_output_3134_, lean_object* v_x_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_stx_3133_, v_output_3134_, v_x_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3144_, lean_object* v_stx_3145_, lean_object* v_output_3146_, lean_object* v_x_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0(v_00_u03b1_3144_, v_stx_3145_, v_output_3146_, v_x_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3156_, lean_object* v_x_3157_, lean_object* v_mkInfoTree_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_3157_, v_mkInfoTree_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3167_, lean_object* v_x_3168_, lean_object* v_mkInfoTree_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1(v_00_u03b1_3167_, v_x_3168_, v_mkInfoTree_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(lean_object* v___x_3178_, uint8_t v___x_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
if (lean_obj_tag(v_a_3180_) == 0)
{
lean_object* v___x_3182_; 
lean_dec_ref(v___x_3178_);
v___x_3182_ = l_List_reverse___redArg(v_a_3181_);
return v___x_3182_;
}
else
{
lean_object* v_head_3183_; lean_object* v_tail_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3195_; 
v_head_3183_ = lean_ctor_get(v_a_3180_, 0);
v_tail_3184_ = lean_ctor_get(v_a_3180_, 1);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_a_3180_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3186_ = v_a_3180_;
v_isShared_3187_ = v_isSharedCheck_3195_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_tail_3184_);
lean_inc(v_head_3183_);
lean_dec(v_a_3180_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3195_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v_fst_3188_; uint8_t v___x_3189_; 
v_fst_3188_ = lean_ctor_get(v_head_3183_, 0);
lean_inc(v_fst_3188_);
lean_inc_ref(v___x_3178_);
v___x_3189_ = l_Lean_Environment_contains(v___x_3178_, v_fst_3188_, v___x_3179_);
if (v___x_3189_ == 0)
{
lean_del_object(v___x_3186_);
lean_dec(v_head_3183_);
v_a_3180_ = v_tail_3184_;
goto _start;
}
else
{
lean_object* v___x_3192_; 
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 1, v_a_3181_);
v___x_3192_ = v___x_3186_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_head_3183_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_a_3181_);
v___x_3192_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
v_a_3180_ = v_tail_3184_;
v_a_3181_ = v___x_3192_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0___boxed(lean_object* v___x_3196_, lean_object* v___x_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
uint8_t v___x_5456__boxed_3200_; lean_object* v_res_3201_; 
v___x_5456__boxed_3200_ = lean_unbox(v___x_3197_);
v_res_3201_ = l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(v___x_3196_, v___x_5456__boxed_3200_, v_a_3198_, v_a_3199_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(lean_object* v_className_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v_env_3207_; lean_object* v___y_3209_; lean_object* v___x_3215_; lean_object* v_toEnvExtension_3216_; lean_object* v_asyncMode_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v_defaultInstances_3220_; lean_object* v___x_3221_; 
v___x_3205_ = l_Lean_Meta_instInhabitedDefaultInstances_default;
v___x_3206_ = lean_st_ref_get(v___y_3203_);
v_env_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc_ref_n(v_env_3207_, 2);
lean_dec(v___x_3206_);
v___x_3215_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_3216_ = lean_ctor_get(v___x_3215_, 0);
v_asyncMode_3217_ = lean_ctor_get(v_toEnvExtension_3216_, 2);
v___x_3218_ = lean_box(0);
v___x_3219_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3205_, v___x_3215_, v_env_3207_, v_asyncMode_3217_, v___x_3218_);
v_defaultInstances_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_defaultInstances_3220_);
lean_dec(v___x_3219_);
v___x_3221_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_3220_, v_className_3202_);
lean_dec(v_defaultInstances_3220_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_box(0);
v___y_3209_ = v___x_3222_;
goto v___jp_3208_;
}
else
{
lean_object* v_val_3223_; 
v_val_3223_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_val_3223_);
lean_dec_ref_known(v___x_3221_, 1);
v___y_3209_ = v_val_3223_;
goto v___jp_3208_;
}
v___jp_3208_:
{
uint8_t v_isExporting_3210_; 
v_isExporting_3210_ = lean_ctor_get_uint8(v_env_3207_, sizeof(void*)*13);
if (v_isExporting_3210_ == 0)
{
lean_object* v___x_3211_; 
lean_dec_ref(v_env_3207_);
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___y_3209_);
return v___x_3211_;
}
else
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_box(0);
v___x_3213_ = l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(v_env_3207_, v_isExporting_3210_, v___y_3209_, v___x_3212_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg___boxed(lean_object* v_className_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec(v_className_3224_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3228_, lean_object* v_declHint_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v_env_3234_; uint8_t v___x_3235_; 
v___x_3232_ = lean_box(0);
v___x_3233_ = lean_st_ref_get(v___y_3230_);
v_env_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc_ref(v_env_3234_);
lean_dec(v___x_3233_);
v___x_3235_ = l_Lean_Name_isAnonymous(v_declHint_3229_);
if (v___x_3235_ == 0)
{
uint8_t v_isExporting_3236_; 
v_isExporting_3236_ = lean_ctor_get_uint8(v_env_3234_, sizeof(void*)*13);
if (v_isExporting_3236_ == 0)
{
lean_object* v___x_3237_; 
lean_dec_ref(v_env_3234_);
lean_dec(v_declHint_3229_);
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_msg_3228_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; uint8_t v___x_3239_; 
lean_inc_ref(v_env_3234_);
v___x_3238_ = l_Lean_Environment_setExporting(v_env_3234_, v___x_3235_);
lean_inc(v_declHint_3229_);
lean_inc_ref(v___x_3238_);
v___x_3239_ = l_Lean_Environment_contains(v___x_3238_, v_declHint_3229_, v_isExporting_3236_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; 
lean_dec_ref(v___x_3238_);
lean_dec_ref(v_env_3234_);
lean_dec(v_declHint_3229_);
v___x_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3240_, 0, v_msg_3228_);
return v___x_3240_;
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v_c_3248_; lean_object* v___x_3249_; 
v___x_3241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3242_ = lean_unsigned_to_nat(32u);
v___x_3243_ = lean_mk_empty_array_with_capacity(v___x_3242_);
lean_dec_ref(v___x_3243_);
v___x_3244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5);
v___x_3245_ = l_Lean_Options_empty;
v___x_3246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3238_);
lean_ctor_set(v___x_3246_, 1, v___x_3241_);
lean_ctor_set(v___x_3246_, 2, v___x_3244_);
lean_ctor_set(v___x_3246_, 3, v___x_3245_);
lean_inc(v_declHint_3229_);
v___x_3247_ = l_Lean_MessageData_ofConstName(v_declHint_3229_, v___x_3235_);
v_c_3248_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3248_, 0, v___x_3246_);
lean_ctor_set(v_c_3248_, 1, v___x_3247_);
v___x_3249_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3234_, v_declHint_3229_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_dec_ref(v_env_3234_);
lean_dec(v_declHint_3229_);
v___x_3250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
lean_ctor_set(v___x_3251_, 1, v_c_3248_);
v___x_3252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = l_Lean_MessageData_note(v___x_3253_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v_msg_3228_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
return v___x_3256_;
}
else
{
lean_object* v_val_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3291_; 
v_val_3257_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3259_ = v___x_3249_;
v_isShared_3260_ = v_isSharedCheck_3291_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_val_3257_);
lean_dec(v___x_3249_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3291_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3261_; lean_object* v_moduleNames_3262_; lean_object* v_mod_3263_; uint8_t v___x_3264_; 
v___x_3261_ = l_Lean_Environment_header(v_env_3234_);
lean_dec_ref(v_env_3234_);
v_moduleNames_3262_ = lean_ctor_get(v___x_3261_, 4);
lean_inc_ref(v_moduleNames_3262_);
lean_dec_ref(v___x_3261_);
v_mod_3263_ = lean_array_get(v___x_3232_, v_moduleNames_3262_, v_val_3257_);
lean_dec(v_val_3257_);
lean_dec_ref(v_moduleNames_3262_);
v___x_3264_ = l_Lean_isPrivateName(v_declHint_3229_);
lean_dec(v_declHint_3229_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3265_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11);
v___x_3266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
lean_ctor_set(v___x_3266_, 1, v_c_3248_);
v___x_3267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13);
v___x_3268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3266_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = l_Lean_MessageData_ofName(v_mod_3263_);
v___x_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = l_Lean_MessageData_note(v___x_3272_);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v_msg_3228_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set_tag(v___x_3259_, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3274_);
v___x_3276_ = v___x_3259_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v_c_3248_);
v___x_3280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_Lean_MessageData_ofName(v_mod_3263_);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = l_Lean_MessageData_note(v___x_3285_);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_msg_3228_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set_tag(v___x_3259_, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3287_);
v___x_3289_ = v___x_3259_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3292_; 
lean_dec_ref(v_env_3234_);
lean_dec(v_declHint_3229_);
v___x_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3292_, 0, v_msg_3228_);
return v___x_3292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3293_, lean_object* v_declHint_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3293_, v_declHint_3294_, v___y_3295_);
lean_dec(v___y_3295_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_msg_3298_, lean_object* v_declHint_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3315_; 
v___x_3305_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3298_, v_declHint_3299_, v___y_3303_);
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3315_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3315_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3310_ = l_Lean_unknownIdentifierMessageTag;
v___x_3311_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v_a_3306_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3311_);
v___x_3313_ = v___x_3308_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3316_, lean_object* v_declHint_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_3316_, v_declHint_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_ref_3330_; lean_object* v___x_3331_; lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3340_; 
v_ref_3330_ = lean_ctor_get(v___y_3327_, 2);
v___x_3331_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3340_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3340_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3336_; lean_object* v___x_3338_; 
lean_inc(v_ref_3330_);
v___x_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3336_, 0, v_ref_3330_);
lean_ctor_set(v___x_3336_, 1, v_a_3332_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set_tag(v___x_3334_, 1);
lean_ctor_set(v___x_3334_, 0, v___x_3336_);
v___x_3338_ = v___x_3334_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_3348_, lean_object* v_msg_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_toCold_3355_; lean_object* v_currRecDepth_3356_; lean_object* v_ref_3357_; uint16_t v_optionFlags_3358_; uint8_t v_suppressElabErrors_3359_; uint8_t v_isRecordingDeps_3360_; lean_object* v_ref_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v_toCold_3355_ = lean_ctor_get(v___y_3352_, 0);
v_currRecDepth_3356_ = lean_ctor_get(v___y_3352_, 1);
v_ref_3357_ = lean_ctor_get(v___y_3352_, 2);
v_optionFlags_3358_ = lean_ctor_get_uint16(v___y_3352_, sizeof(void*)*3);
v_suppressElabErrors_3359_ = lean_ctor_get_uint8(v___y_3352_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3360_ = lean_ctor_get_uint8(v___y_3352_, sizeof(void*)*3 + 3);
v_ref_3361_ = l_Lean_replaceRef(v_ref_3348_, v_ref_3357_);
lean_inc(v_currRecDepth_3356_);
lean_inc_ref(v_toCold_3355_);
v___x_3362_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3362_, 0, v_toCold_3355_);
lean_ctor_set(v___x_3362_, 1, v_currRecDepth_3356_);
lean_ctor_set(v___x_3362_, 2, v_ref_3361_);
lean_ctor_set_uint16(v___x_3362_, sizeof(void*)*3, v_optionFlags_3358_);
lean_ctor_set_uint8(v___x_3362_, sizeof(void*)*3 + 2, v_suppressElabErrors_3359_);
lean_ctor_set_uint8(v___x_3362_, sizeof(void*)*3 + 3, v_isRecordingDeps_3360_);
v___x_3363_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3349_, v___y_3350_, v___y_3351_, v___x_3362_, v___y_3353_);
lean_dec_ref_known(v___x_3362_, 3);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3364_, lean_object* v_msg_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3364_, v_msg_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v_ref_3364_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_3372_, lean_object* v_msg_3373_, lean_object* v_declHint_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; lean_object* v_a_3381_; lean_object* v___x_3382_; 
v___x_3380_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_3373_, v_declHint_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3372_, v_a_3381_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3383_, lean_object* v_msg_3384_, lean_object* v_declHint_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3383_, v_msg_3384_, v_declHint_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v_ref_3383_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_3392_, lean_object* v_constName_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; uint8_t v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3399_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1);
v___x_3400_ = 0;
lean_inc(v_constName_3393_);
v___x_3401_ = l_Lean_MessageData_ofConstName(v_constName_3393_, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3399_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3);
v___x_3404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3402_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
v___x_3405_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3392_, v___x_3404_, v_constName_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_3406_, lean_object* v_constName_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3406_, v_constName_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v_ref_3406_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(lean_object* v_constName_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_ref_3420_; lean_object* v___x_3421_; 
v_ref_3420_ = lean_ctor_get(v___y_3417_, 2);
v___x_3421_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3420_, v_constName_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(lean_object* v_constName_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v___x_3435_; lean_object* v_env_3436_; uint8_t v___x_3437_; lean_object* v___x_3438_; 
v___x_3435_ = lean_st_ref_get(v___y_3433_);
v_env_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc_ref(v_env_3436_);
lean_dec(v___x_3435_);
v___x_3437_ = 0;
lean_inc(v_constName_3429_);
v___x_3438_ = l_Lean_Environment_find_x3f(v_env_3436_, v_constName_3429_, v___x_3437_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
return v___x_3439_;
}
else
{
lean_object* v_val_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_constName_3429_);
v_val_3440_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3438_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_val_3440_);
lean_dec(v___x_3438_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set_tag(v___x_3442_, 0);
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_val_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1___boxed(lean_object* v_constName_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(v_constName_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(lean_object* v_declName_3458_, uint8_t v_lhs_3459_, lean_object* v___x_3460_, lean_object* v_as_x27_3461_, lean_object* v_b_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
if (lean_obj_tag(v_as_x27_3461_) == 0)
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v_b_3462_);
return v___x_3468_;
}
else
{
lean_object* v_head_3469_; lean_object* v_tail_3470_; lean_object* v_fst_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; lean_object* v___x_3476_; 
lean_dec_ref(v_b_3462_);
v_head_3469_ = lean_ctor_get(v_as_x27_3461_, 0);
v_tail_3470_ = lean_ctor_get(v_as_x27_3461_, 1);
v_fst_3471_ = lean_ctor_get(v_head_3469_, 0);
v___x_3472_ = lean_box(0);
v___x_3473_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0));
v___x_3474_ = lean_unsigned_to_nat(1u);
v___x_3475_ = lean_nat_dec_le(v___x_3460_, v___x_3474_);
lean_inc(v_fst_3471_);
v___x_3476_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(v_fst_3471_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3509_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3479_ = v___x_3476_;
v_isShared_3480_ = v_isSharedCheck_3509_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3509_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = l_Lean_ConstantInfo_type(v_a_3477_);
lean_dec(v_a_3477_);
v___x_3482_ = l_Lean_Expr_getForallBody(v___x_3481_);
lean_dec_ref(v___x_3481_);
if (lean_obj_tag(v___x_3482_) == 5)
{
lean_object* v_fn_3483_; 
v_fn_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc_ref(v_fn_3483_);
lean_dec_ref_known(v___x_3482_, 2);
if (lean_obj_tag(v_fn_3483_) == 5)
{
lean_object* v_fn_3484_; 
v_fn_3484_ = lean_ctor_get(v_fn_3483_, 0);
lean_inc_ref(v_fn_3484_);
if (lean_obj_tag(v_fn_3484_) == 5)
{
lean_object* v_arg_3485_; lean_object* v_arg_3486_; uint8_t v___y_3488_; uint8_t v___y_3498_; 
v_arg_3485_ = lean_ctor_get(v_fn_3483_, 1);
lean_inc_ref(v_arg_3485_);
lean_dec_ref_known(v_fn_3483_, 2);
v_arg_3486_ = lean_ctor_get(v_fn_3484_, 1);
lean_inc_ref(v_arg_3486_);
lean_dec_ref_known(v_fn_3484_, 2);
if (v_lhs_3459_ == 0)
{
lean_dec_ref(v_arg_3485_);
v___y_3498_ = v___x_3475_;
goto v___jp_3497_;
}
else
{
uint8_t v___x_3501_; 
v___x_3501_ = l_Lean_Expr_isAppOf(v_arg_3485_, v_declName_3458_);
lean_dec_ref(v_arg_3485_);
if (v___x_3501_ == 0)
{
v___y_3498_ = v___x_3501_;
goto v___jp_3497_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
lean_dec_ref(v_arg_3486_);
lean_del_object(v___x_3479_);
v___x_3502_ = lean_box(v_lhs_3459_);
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
v___x_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___x_3472_);
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
return v___x_3505_;
}
}
v___jp_3487_:
{
uint8_t v___x_3489_; 
v___x_3489_ = l_Lean_Expr_isAppOf(v_arg_3486_, v_declName_3458_);
lean_dec_ref(v_arg_3486_);
if (v___x_3489_ == 0)
{
lean_del_object(v___x_3479_);
v_as_x27_3461_ = v_tail_3470_;
v_b_3462_ = v___x_3473_;
goto _start;
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3495_; 
v___x_3491_ = lean_box(v___y_3488_);
v___x_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
v___x_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_ctor_set(v___x_3493_, 1, v___x_3472_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3493_);
v___x_3495_ = v___x_3479_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
v___jp_3497_:
{
uint8_t v___x_3499_; 
v___x_3499_ = 1;
if (v_lhs_3459_ == 0)
{
v___y_3488_ = v___x_3499_;
goto v___jp_3487_;
}
else
{
if (v___y_3498_ == 0)
{
lean_dec_ref(v_arg_3486_);
lean_del_object(v___x_3479_);
v_as_x27_3461_ = v_tail_3470_;
v_b_3462_ = v___x_3473_;
goto _start;
}
else
{
v___y_3488_ = v___x_3499_;
goto v___jp_3487_;
}
}
}
}
else
{
lean_dec_ref_known(v_fn_3483_, 2);
lean_dec_ref(v_fn_3484_);
lean_del_object(v___x_3479_);
v_as_x27_3461_ = v_tail_3470_;
v_b_3462_ = v___x_3473_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_3483_);
lean_del_object(v___x_3479_);
v_as_x27_3461_ = v_tail_3470_;
v_b_3462_ = v___x_3473_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_3482_);
lean_del_object(v___x_3479_);
v_as_x27_3461_ = v_tail_3470_;
v_b_3462_ = v___x_3473_;
goto _start;
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
v_a_3510_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3476_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3476_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___boxed(lean_object* v_declName_3518_, lean_object* v_lhs_3519_, lean_object* v___x_3520_, lean_object* v_as_x27_3521_, lean_object* v_b_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
uint8_t v_lhs_boxed_3528_; lean_object* v_res_3529_; 
v_lhs_boxed_3528_ = lean_unbox(v_lhs_3519_);
v_res_3529_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3518_, v_lhs_boxed_3528_, v___x_3520_, v_as_x27_3521_, v_b_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v_as_x27_3521_);
lean_dec(v___x_3520_);
lean_dec(v_declName_3518_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(lean_object* v_f_3530_, lean_object* v_maxType_3531_, uint8_t v_lhs_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
if (lean_obj_tag(v_f_3530_) == 4)
{
lean_object* v_declName_3538_; lean_object* v___x_3539_; 
v_declName_3538_ = lean_ctor_get(v_f_3530_, 0);
v___x_3539_ = l_Lean_Expr_getAppFn(v_maxType_3531_);
if (lean_obj_tag(v___x_3539_) == 4)
{
lean_object* v_declName_3540_; lean_object* v_className_3541_; lean_object* v___x_3542_; lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3579_; 
v_declName_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_declName_3540_);
lean_dec_ref_known(v___x_3539_, 2);
v_className_3541_ = l_Lean_Name_getPrefix(v_declName_3538_);
v___x_3542_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3541_, v_a_3536_);
lean_dec(v_className_3541_);
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3545_ = v___x_3542_;
v_isShared_3546_ = v_isSharedCheck_3579_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3542_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3579_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3547_ = l_List_lengthTR___redArg(v_a_3543_);
v___x_3548_ = lean_unsigned_to_nat(1u);
v___x_3549_ = lean_nat_dec_le(v___x_3547_, v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_del_object(v___x_3545_);
v___x_3550_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0));
v___x_3551_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3540_, v_lhs_3532_, v___x_3547_, v_a_3543_, v___x_3550_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3543_);
lean_dec(v___x_3547_);
lean_dec(v_declName_3540_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3565_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3565_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3565_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v_fst_3556_; 
v_fst_3556_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_fst_3556_);
lean_dec(v_a_3552_);
if (lean_obj_tag(v_fst_3556_) == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3557_ = lean_box(v___x_3549_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3557_);
v___x_3559_ = v___x_3554_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
else
{
lean_object* v_val_3561_; lean_object* v___x_3563_; 
v_val_3561_ = lean_ctor_get(v_fst_3556_, 0);
lean_inc(v_val_3561_);
lean_dec_ref_known(v_fst_3556_, 1);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_val_3561_);
v___x_3563_ = v___x_3554_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_val_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
v_a_3566_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3551_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3551_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
uint8_t v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3577_; 
lean_dec(v___x_3547_);
lean_dec(v_a_3543_);
lean_dec(v_declName_3540_);
v___x_3574_ = 0;
v___x_3575_ = lean_box(v___x_3574_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 0, v___x_3575_);
v___x_3577_ = v___x_3545_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
uint8_t v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
lean_dec_ref(v___x_3539_);
v___x_3580_ = 0;
v___x_3581_ = lean_box(v___x_3580_);
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
}
else
{
uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = 0;
v___x_3584_ = lean_box(v___x_3583_);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
return v___x_3585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances___boxed(lean_object* v_f_3586_, lean_object* v_maxType_3587_, lean_object* v_lhs_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
uint8_t v_lhs_boxed_3594_; lean_object* v_res_3595_; 
v_lhs_boxed_3594_ = lean_unbox(v_lhs_3588_);
v_res_3595_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(v_f_3586_, v_maxType_3587_, v_lhs_boxed_3594_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec_ref(v_maxType_3587_);
lean_dec_ref(v_f_3586_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0(lean_object* v_className_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3596_, v___y_3600_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___boxed(lean_object* v_className_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0(v_className_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v_className_3603_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2(lean_object* v_declName_3610_, uint8_t v_lhs_3611_, lean_object* v___x_3612_, lean_object* v_as_3613_, lean_object* v_as_x27_3614_, lean_object* v_b_3615_, lean_object* v_a_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3610_, v_lhs_3611_, v___x_3612_, v_as_x27_3614_, v_b_3615_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___boxed(lean_object* v_declName_3623_, lean_object* v_lhs_3624_, lean_object* v___x_3625_, lean_object* v_as_3626_, lean_object* v_as_x27_3627_, lean_object* v_b_3628_, lean_object* v_a_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
uint8_t v_lhs_boxed_3635_; lean_object* v_res_3636_; 
v_lhs_boxed_3635_ = lean_unbox(v_lhs_3624_);
v_res_3636_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2(v_declName_3623_, v_lhs_boxed_3635_, v___x_3625_, v_as_3626_, v_as_x27_3627_, v_b_3628_, v_a_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v_as_x27_3627_);
lean_dec(v_as_3626_);
lean_dec(v___x_3625_);
lean_dec(v_declName_3623_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2(lean_object* v_00_u03b1_3637_, lean_object* v_constName_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3645_, lean_object* v_constName_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2(v_00_u03b1_3645_, v_constName_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_3653_, lean_object* v_ref_3654_, lean_object* v_constName_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3654_, v_constName_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3662_, lean_object* v_ref_3663_, lean_object* v_constName_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3(v_00_u03b1_3662_, v_ref_3663_, v_constName_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v_ref_3663_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_3671_, lean_object* v_ref_3672_, lean_object* v_msg_3673_, lean_object* v_declHint_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3672_, v_msg_3673_, v_declHint_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3681_, lean_object* v_ref_3682_, lean_object* v_msg_3683_, lean_object* v_declHint_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_3681_, v_ref_3682_, v_msg_3683_, v_declHint_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec(v_ref_3682_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_3691_, lean_object* v_declHint_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3691_, v_declHint_3692_, v___y_3696_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_3699_, lean_object* v_declHint_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_3699_, v_declHint_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_3707_, lean_object* v_ref_3708_, lean_object* v_msg_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3708_, v_msg_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3716_, lean_object* v_ref_3717_, lean_object* v_msg_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_3716_, v_ref_3717_, v_msg_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v_ref_3717_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_3725_, lean_object* v_msg_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_3733_, lean_object* v_msg_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_3733_, v_msg_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(lean_object* v_f_3741_, lean_object* v_maxType_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v_a_3749_; 
if (lean_obj_tag(v_f_3741_) == 4)
{
lean_object* v_declName_3756_; lean_object* v_className_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_declName_3756_ = lean_ctor_get(v_f_3741_, 0);
v_className_3757_ = l_Lean_Name_getPrefix(v_declName_3756_);
v___x_3758_ = lean_unsigned_to_nat(3u);
v___x_3759_ = lean_mk_empty_array_with_capacity(v___x_3758_);
lean_inc_ref_n(v_maxType_3742_, 2);
v___x_3760_ = lean_array_push(v___x_3759_, v_maxType_3742_);
v___x_3761_ = lean_array_push(v___x_3760_, v_maxType_3742_);
v___x_3762_ = lean_array_push(v___x_3761_, v_maxType_3742_);
v___x_3763_ = l_Lean_Meta_mkAppM(v_className_3757_, v___x_3762_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v___x_3765_ = lean_box(0);
v___x_3766_ = l_Lean_Meta_trySynthInstance(v_a_3764_, v___x_3765_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3781_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3781_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3781_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
if (lean_obj_tag(v_a_3767_) == 1)
{
uint8_t v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3774_; 
lean_dec_ref_known(v_a_3767_, 1);
v___x_3771_ = 1;
v___x_3772_ = lean_box(v___x_3771_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v___x_3772_);
v___x_3774_ = v___x_3769_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
else
{
uint8_t v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
lean_dec(v_a_3767_);
v___x_3776_ = 0;
v___x_3777_ = lean_box(v___x_3776_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v___x_3777_);
v___x_3779_ = v___x_3769_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
lean_object* v_a_3782_; 
v_a_3782_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3766_, 1);
v_a_3749_ = v_a_3782_;
goto v___jp_3748_;
}
}
else
{
lean_object* v_a_3783_; 
v_a_3783_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3763_, 1);
v_a_3749_ = v_a_3783_;
goto v___jp_3748_;
}
}
else
{
uint8_t v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_dec_ref(v_maxType_3742_);
v___x_3784_ = 0;
v___x_3785_ = lean_box(v___x_3784_);
v___x_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
return v___x_3786_;
}
v___jp_3748_:
{
uint8_t v___x_3750_; 
v___x_3750_ = l_Lean_Exception_isInterrupt(v_a_3749_);
if (v___x_3750_ == 0)
{
uint8_t v___x_3751_; 
lean_inc_ref(v_a_3749_);
v___x_3751_ = l_Lean_Exception_isRuntime(v_a_3749_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_dec_ref(v_a_3749_);
v___x_3752_ = lean_box(v___x_3751_);
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
return v___x_3753_;
}
else
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3754_, 0, v_a_3749_);
return v___x_3754_;
}
}
else
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3755_, 0, v_a_3749_);
return v___x_3755_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance___boxed(lean_object* v_f_3787_, lean_object* v_maxType_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(v_f_3787_, v_maxType_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec_ref(v_f_3787_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(lean_object* v_cls_3795_, lean_object* v_msg_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_ref_3802_; lean_object* v___x_3803_; lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3849_; 
v_ref_3802_ = lean_ctor_get(v___y_3799_, 2);
v___x_3803_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3849_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3849_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v_traceState_3809_; lean_object* v_env_3810_; lean_object* v_nextMacroScope_3811_; lean_object* v_ngen_3812_; lean_object* v_auxDeclNGen_3813_; lean_object* v_cache_3814_; lean_object* v_recordedDeps_3815_; lean_object* v_messages_3816_; lean_object* v_infoState_3817_; lean_object* v_snapshotTasks_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3848_; 
v___x_3808_ = lean_st_ref_take(v___y_3800_);
v_traceState_3809_ = lean_ctor_get(v___x_3808_, 4);
v_env_3810_ = lean_ctor_get(v___x_3808_, 0);
v_nextMacroScope_3811_ = lean_ctor_get(v___x_3808_, 1);
v_ngen_3812_ = lean_ctor_get(v___x_3808_, 2);
v_auxDeclNGen_3813_ = lean_ctor_get(v___x_3808_, 3);
v_cache_3814_ = lean_ctor_get(v___x_3808_, 5);
v_recordedDeps_3815_ = lean_ctor_get(v___x_3808_, 6);
v_messages_3816_ = lean_ctor_get(v___x_3808_, 7);
v_infoState_3817_ = lean_ctor_get(v___x_3808_, 8);
v_snapshotTasks_3818_ = lean_ctor_get(v___x_3808_, 9);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3820_ = v___x_3808_;
v_isShared_3821_ = v_isSharedCheck_3848_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_snapshotTasks_3818_);
lean_inc(v_infoState_3817_);
lean_inc(v_messages_3816_);
lean_inc(v_recordedDeps_3815_);
lean_inc(v_cache_3814_);
lean_inc(v_traceState_3809_);
lean_inc(v_auxDeclNGen_3813_);
lean_inc(v_ngen_3812_);
lean_inc(v_nextMacroScope_3811_);
lean_inc(v_env_3810_);
lean_dec(v___x_3808_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3848_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
uint64_t v_tid_3822_; lean_object* v_traces_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3847_; 
v_tid_3822_ = lean_ctor_get_uint64(v_traceState_3809_, sizeof(void*)*1);
v_traces_3823_ = lean_ctor_get(v_traceState_3809_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_traceState_3809_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3825_ = v_traceState_3809_;
v_isShared_3826_ = v_isSharedCheck_3847_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_traces_3823_);
lean_dec(v_traceState_3809_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3847_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; double v___x_3829_; uint8_t v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3827_ = lean_box(0);
v___x_3828_ = lean_box(0);
v___x_3829_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0);
v___x_3830_ = 0;
v___x_3831_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1));
v___x_3832_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3832_, 0, v_cls_3795_);
lean_ctor_set(v___x_3832_, 1, v___x_3828_);
lean_ctor_set(v___x_3832_, 2, v___x_3831_);
lean_ctor_set_float(v___x_3832_, sizeof(void*)*3, v___x_3829_);
lean_ctor_set_float(v___x_3832_, sizeof(void*)*3 + 8, v___x_3829_);
lean_ctor_set_uint8(v___x_3832_, sizeof(void*)*3 + 16, v___x_3830_);
v___x_3833_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2));
v___x_3834_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3832_);
lean_ctor_set(v___x_3834_, 1, v_a_3804_);
lean_ctor_set(v___x_3834_, 2, v___x_3833_);
lean_inc(v_ref_3802_);
v___x_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3835_, 0, v_ref_3802_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
v___x_3836_ = l_Lean_PersistentArray_push___redArg(v_traces_3823_, v___x_3835_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3836_);
v___x_3838_ = v___x_3825_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3836_);
lean_ctor_set_uint64(v_reuseFailAlloc_3846_, sizeof(void*)*1, v_tid_3822_);
v___x_3838_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3840_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v___x_3838_);
v___x_3840_ = v___x_3820_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_env_3810_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_nextMacroScope_3811_);
lean_ctor_set(v_reuseFailAlloc_3845_, 2, v_ngen_3812_);
lean_ctor_set(v_reuseFailAlloc_3845_, 3, v_auxDeclNGen_3813_);
lean_ctor_set(v_reuseFailAlloc_3845_, 4, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3845_, 5, v_cache_3814_);
lean_ctor_set(v_reuseFailAlloc_3845_, 6, v_recordedDeps_3815_);
lean_ctor_set(v_reuseFailAlloc_3845_, 7, v_messages_3816_);
lean_ctor_set(v_reuseFailAlloc_3845_, 8, v_infoState_3817_);
lean_ctor_set(v_reuseFailAlloc_3845_, 9, v_snapshotTasks_3818_);
v___x_3840_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3841_ = lean_st_ref_put(v___y_3800_, v___x_3840_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v___x_3827_);
v___x_3843_ = v___x_3806_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3827_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg___boxed(lean_object* v_cls_3850_, lean_object* v_msg_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v_cls_3850_, v_msg_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
return v_res_3857_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1(void){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__0));
v___x_3860_ = l_Lean_stringToMessageData(v___x_3859_);
return v___x_3860_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3(void){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__2));
v___x_3863_ = l_Lean_stringToMessageData(v___x_3862_);
return v___x_3863_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5(void){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__4));
v___x_3866_ = l_Lean_stringToMessageData(v___x_3865_);
return v___x_3866_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__6));
v___x_3869_ = l_Lean_stringToMessageData(v___x_3868_);
return v___x_3869_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__8));
v___x_3872_ = l_Lean_stringToMessageData(v___x_3871_);
return v___x_3872_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__0));
v___x_3875_ = l_Lean_stringToMessageData(v___x_3874_);
return v___x_3875_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__2));
v___x_3878_ = l_Lean_stringToMessageData(v___x_3877_);
return v___x_3878_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__5));
v___x_3883_ = l_Lean_MessageData_ofFormat(v___x_3882_);
return v___x_3883_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__7));
v___x_3886_ = l_Lean_stringToMessageData(v___x_3885_);
return v___x_3886_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10(void){
_start:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__9));
v___x_3889_ = l_Lean_stringToMessageData(v___x_3888_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(lean_object* v_tree_3892_, lean_object* v_expectedType_x3f_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___x_3922_; 
lean_inc(v_expectedType_x3f_3893_);
lean_inc_ref(v_tree_3892_);
v___x_3922_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v_tree_3892_, v_expectedType_x3f_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_toCold_3923_; lean_object* v_options_3924_; lean_object* v_a_3925_; lean_object* v_inheritedTraceOptions_3926_; uint8_t v_hasTrace_3927_; lean_object* v___x_3928_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3991_; lean_object* v___y_3992_; 
v_toCold_3923_ = lean_ctor_get(v_a_3898_, 0);
v_options_3924_ = lean_ctor_get(v_toCold_3923_, 2);
v_a_3925_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3922_, 1);
v_inheritedTraceOptions_3926_ = lean_ctor_get(v_toCold_3923_, 11);
v_hasTrace_3927_ = lean_ctor_get_uint8(v_options_3924_, sizeof(void*)*1);
v___x_3928_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
if (v_hasTrace_3927_ == 0)
{
v___y_3956_ = v_a_3894_;
v___y_3957_ = v_a_3895_;
v___y_3958_ = v_a_3896_;
v___y_3959_ = v_a_3897_;
v___y_3960_ = v_a_3898_;
v___y_3961_ = v_a_3899_;
goto v___jp_3955_;
}
else
{
lean_object* v___x_4003_; uint8_t v___x_4004_; 
v___x_4003_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4004_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3926_, v_options_3924_, v___x_4003_);
if (v___x_4004_ == 0)
{
v___y_3956_ = v_a_3894_;
v___y_3957_ = v_a_3895_;
v___y_3958_ = v_a_3896_;
v___y_3959_ = v_a_3897_;
v___y_3960_ = v_a_3898_;
v___y_3961_ = v_a_3899_;
goto v___jp_3955_;
}
else
{
lean_object* v_max_x3f_4005_; uint8_t v_hasUncomparable_4006_; uint8_t v_hasUnknown_4007_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___x_4019_; lean_object* v___y_4021_; 
v_max_x3f_4005_ = lean_ctor_get(v_a_3925_, 0);
v_hasUncomparable_4006_ = lean_ctor_get_uint8(v_a_3925_, sizeof(void*)*1);
v_hasUnknown_4007_ = lean_ctor_get_uint8(v_a_3925_, sizeof(void*)*1 + 1);
v___x_4019_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8);
if (v_hasUncomparable_4006_ == 0)
{
lean_object* v___x_4029_; 
v___x_4029_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_4021_ = v___x_4029_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4030_; 
v___x_4030_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_4021_ = v___x_4030_;
goto v___jp_4020_;
}
v___jp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_inc_ref(v___y_4010_);
v___x_4011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___y_4010_);
v___x_4012_ = l_Lean_MessageData_ofFormat(v___x_4011_);
v___x_4013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___y_4009_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
v___x_4014_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3);
v___x_4015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4013_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
if (lean_obj_tag(v_max_x3f_4005_) == 0)
{
lean_object* v___x_4016_; 
v___x_4016_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6);
v___y_3991_ = v___x_4015_;
v___y_3992_ = v___x_4016_;
goto v___jp_3990_;
}
else
{
lean_object* v_val_4017_; lean_object* v___x_4018_; 
v_val_4017_ = lean_ctor_get(v_max_x3f_4005_, 0);
lean_inc(v_val_4017_);
v___x_4018_ = l_Lean_MessageData_ofExpr(v_val_4017_);
v___y_3991_ = v___x_4015_;
v___y_3992_ = v___x_4018_;
goto v___jp_3990_;
}
}
v___jp_4020_:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_inc_ref(v___y_4021_);
v___x_4022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___y_4021_);
v___x_4023_ = l_Lean_MessageData_ofFormat(v___x_4022_);
v___x_4024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4019_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
v___x_4025_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10);
v___x_4026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
if (v_hasUnknown_4007_ == 0)
{
lean_object* v___x_4027_; 
v___x_4027_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_4009_ = v___x_4026_;
v___y_4010_ = v___x_4027_;
goto v___jp_4008_;
}
else
{
lean_object* v___x_4028_; 
v___x_4028_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_4009_ = v___x_4026_;
v___y_4010_ = v___x_4028_;
goto v___jp_4008_;
}
}
}
}
v___jp_3929_:
{
lean_object* v_toCold_3937_; lean_object* v_options_3938_; uint8_t v_hasTrace_3939_; 
v_toCold_3937_ = lean_ctor_get(v___y_3935_, 0);
v_options_3938_ = lean_ctor_get(v_toCold_3937_, 2);
v_hasTrace_3939_ = lean_ctor_get_uint8(v_options_3938_, sizeof(void*)*1);
if (v_hasTrace_3939_ == 0)
{
v___y_3913_ = v___y_3930_;
v___y_3914_ = v___y_3931_;
v___y_3915_ = v___y_3932_;
v___y_3916_ = v___y_3933_;
v___y_3917_ = v___y_3934_;
v___y_3918_ = v___y_3935_;
v___y_3919_ = v___y_3936_;
goto v___jp_3912_;
}
else
{
lean_object* v_inheritedTraceOptions_3940_; lean_object* v___x_3941_; uint8_t v___x_3942_; 
v_inheritedTraceOptions_3940_ = lean_ctor_get(v_toCold_3937_, 11);
v___x_3941_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_3942_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3940_, v_options_3938_, v___x_3941_);
if (v___x_3942_ == 0)
{
v___y_3913_ = v___y_3930_;
v___y_3914_ = v___y_3931_;
v___y_3915_ = v___y_3932_;
v___y_3916_ = v___y_3933_;
v___y_3917_ = v___y_3934_;
v___y_3918_ = v___y_3935_;
v___y_3919_ = v___y_3936_;
goto v___jp_3912_;
}
else
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3943_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1);
lean_inc_ref(v___y_3930_);
v___x_3944_ = l_Lean_MessageData_ofExpr(v___y_3930_);
v___x_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_3928_, v___x_3945_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_dec_ref_known(v___x_3946_, 1);
v___y_3913_ = v___y_3930_;
v___y_3914_ = v___y_3931_;
v___y_3915_ = v___y_3932_;
v___y_3916_ = v___y_3933_;
v___y_3917_ = v___y_3934_;
v___y_3918_ = v___y_3935_;
v___y_3919_ = v___y_3936_;
goto v___jp_3912_;
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v___y_3930_);
lean_dec(v_expectedType_x3f_3893_);
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3946_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3946_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
}
v___jp_3955_:
{
uint8_t v_hasUncomparable_3962_; 
v_hasUncomparable_3962_ = lean_ctor_get_uint8(v_a_3925_, sizeof(void*)*1);
if (v_hasUncomparable_3962_ == 0)
{
lean_object* v_max_x3f_3963_; 
v_max_x3f_3963_ = lean_ctor_get(v_a_3925_, 0);
lean_inc(v_max_x3f_3963_);
if (lean_obj_tag(v_max_x3f_3963_) == 0)
{
lean_dec(v_a_3925_);
v___y_3902_ = v___y_3961_;
v___y_3903_ = v___y_3958_;
v___y_3904_ = v___y_3956_;
v___y_3905_ = v___y_3957_;
v___y_3906_ = v___y_3960_;
v___y_3907_ = v___y_3959_;
goto v___jp_3901_;
}
else
{
uint8_t v_hasUnknown_3964_; lean_object* v_val_3965_; lean_object* v___x_3966_; 
v_hasUnknown_3964_ = lean_ctor_get_uint8(v_a_3925_, sizeof(void*)*1 + 1);
lean_dec(v_a_3925_);
v_val_3965_ = lean_ctor_get(v_max_x3f_3963_, 0);
lean_inc_n(v_val_3965_, 2);
lean_dec_ref_known(v_max_x3f_3963_, 1);
v___x_3966_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v_tree_3892_, v_val_3965_, v_hasUncomparable_3962_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3968_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3968_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_3967_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3968_) == 0)
{
if (v_hasUnknown_3964_ == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3970_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc_n(v_a_3969_, 2);
lean_dec_ref_known(v___x_3968_, 1);
lean_inc(v___y_3961_);
lean_inc_ref(v___y_3960_);
lean_inc(v___y_3959_);
lean_inc_ref(v___y_3958_);
v___x_3970_ = lean_infer_type(v_a_3969_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3972_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref_known(v___x_3970_, 1);
v___x_3972_ = l_Lean_Meta_isExprDefEqGuarded(v_a_3971_, v_val_3965_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_dec_ref_known(v___x_3972_, 1);
v___y_3930_ = v_a_3969_;
v___y_3931_ = v___y_3956_;
v___y_3932_ = v___y_3957_;
v___y_3933_ = v___y_3958_;
v___y_3934_ = v___y_3959_;
v___y_3935_ = v___y_3960_;
v___y_3936_ = v___y_3961_;
goto v___jp_3929_;
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec(v_a_3969_);
lean_dec(v_expectedType_x3f_3893_);
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3972_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3972_);
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
lean_dec(v_a_3969_);
lean_dec(v_val_3965_);
lean_dec(v_expectedType_x3f_3893_);
return v___x_3970_;
}
}
else
{
lean_object* v_a_3981_; 
lean_dec(v_val_3965_);
v_a_3981_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v___x_3968_, 1);
v___y_3930_ = v_a_3981_;
v___y_3931_ = v___y_3956_;
v___y_3932_ = v___y_3957_;
v___y_3933_ = v___y_3958_;
v___y_3934_ = v___y_3959_;
v___y_3935_ = v___y_3960_;
v___y_3936_ = v___y_3961_;
goto v___jp_3929_;
}
}
else
{
lean_dec(v_val_3965_);
lean_dec(v_expectedType_x3f_3893_);
return v___x_3968_;
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec(v_val_3965_);
lean_dec(v_expectedType_x3f_3893_);
v_a_3982_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3966_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3966_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
else
{
lean_dec(v_a_3925_);
v___y_3902_ = v___y_3961_;
v___y_3903_ = v___y_3958_;
v___y_3904_ = v___y_3956_;
v___y_3905_ = v___y_3957_;
v___y_3906_ = v___y_3960_;
v___y_3907_ = v___y_3959_;
goto v___jp_3901_;
}
}
v___jp_3990_:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___y_3991_);
lean_ctor_set(v___x_3993_, 1, v___y_3992_);
v___x_3994_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_3928_, v___x_3993_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_dec_ref_known(v___x_3994_, 1);
v___y_3956_ = v_a_3894_;
v___y_3957_ = v_a_3895_;
v___y_3958_ = v_a_3896_;
v___y_3959_ = v_a_3897_;
v___y_3960_ = v_a_3898_;
v___y_3961_ = v_a_3899_;
goto v___jp_3955_;
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec(v_a_3925_);
lean_dec(v_expectedType_x3f_3893_);
lean_dec_ref(v_tree_3892_);
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3994_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3994_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec(v_expectedType_x3f_3893_);
lean_dec_ref(v_tree_3892_);
v_a_4031_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_3922_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_3922_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
v___jp_3901_:
{
lean_object* v___x_3908_; 
v___x_3908_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_tree_3892_, v___y_3904_, v___y_3905_, v___y_3903_, v___y_3907_, v___y_3906_, v___y_3902_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = lean_box(0);
v___x_3911_ = l_Lean_Elab_Term_ensureHasType(v_expectedType_x3f_3893_, v_a_3909_, v___x_3910_, v___x_3910_, v___y_3904_, v___y_3905_, v___y_3903_, v___y_3907_, v___y_3906_, v___y_3902_);
return v___x_3911_;
}
else
{
lean_dec(v_expectedType_x3f_3893_);
return v___x_3908_;
}
}
v___jp_3912_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = lean_box(0);
v___x_3921_ = l_Lean_Elab_Term_ensureHasType(v_expectedType_x3f_3893_, v___y_3913_, v___x_3920_, v___x_3920_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
return v___x_3921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0(lean_object* v_maxType_4039_, lean_object* v_nested_4040_, lean_object* v_f_x3f_4041_, uint8_t v_lhs_4042_, uint8_t v_isPred_4043_, lean_object* v_macroName_4044_, lean_object* v_stx_4045_, lean_object* v_stx_x27_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4039_, v_nested_4040_, v_f_x3f_4041_, v_lhs_4042_, v_isPred_4043_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4063_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4057_ = v___x_4054_;
v_isShared_4058_ = v_isSharedCheck_4063_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4054_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4063_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4059_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4059_, 0, v_macroName_4044_);
lean_ctor_set(v___x_4059_, 1, v_stx_4045_);
lean_ctor_set(v___x_4059_, 2, v_stx_x27_4046_);
lean_ctor_set(v___x_4059_, 3, v_a_4055_);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v___x_4059_);
v___x_4061_ = v___x_4057_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
else
{
lean_dec(v_stx_x27_4046_);
lean_dec(v_stx_4045_);
lean_dec(v_macroName_4044_);
return v___x_4054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0___boxed(lean_object* v_maxType_4064_, lean_object* v_nested_4065_, lean_object* v_f_x3f_4066_, lean_object* v_lhs_4067_, lean_object* v_isPred_4068_, lean_object* v_macroName_4069_, lean_object* v_stx_4070_, lean_object* v_stx_x27_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
uint8_t v_lhs_boxed_4079_; uint8_t v_isPred_boxed_4080_; lean_object* v_res_4081_; 
v_lhs_boxed_4079_ = lean_unbox(v_lhs_4067_);
v_isPred_boxed_4080_ = lean_unbox(v_isPred_4068_);
v_res_4081_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0(v_maxType_4064_, v_nested_4065_, v_f_x3f_4066_, v_lhs_boxed_4079_, v_isPred_boxed_4080_, v_macroName_4069_, v_stx_4070_, v_stx_x27_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(lean_object* v_maxType_4082_, lean_object* v_t_4083_, lean_object* v_f_x3f_4084_, uint8_t v_lhs_4085_, uint8_t v_isPred_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
switch(lean_obj_tag(v_t_4083_))
{
case 0:
{
lean_object* v_ref_4094_; lean_object* v_infoTrees_4095_; lean_object* v_val_4096_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v_toCold_4102_; lean_object* v_currRecDepth_4103_; lean_object* v_ref_4104_; uint16_t v_optionFlags_4105_; uint8_t v_suppressElabErrors_4106_; uint8_t v_isRecordingDeps_4107_; lean_object* v___y_4108_; lean_object* v___x_4130_; 
v_ref_4094_ = lean_ctor_get(v_t_4083_, 0);
v_infoTrees_4095_ = lean_ctor_get(v_t_4083_, 1);
v_val_4096_ = lean_ctor_get(v_t_4083_, 2);
lean_inc(v_a_4092_);
lean_inc_ref(v_a_4091_);
lean_inc(v_a_4090_);
lean_inc_ref(v_a_4089_);
lean_inc_ref(v_val_4096_);
v___x_4130_ = lean_infer_type(v_val_4096_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4132_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref_known(v___x_4130_, 1);
v___x_4132_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_spec__0___redArg(v_a_4131_, v_a_4090_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_toCold_4133_; lean_object* v_options_4134_; lean_object* v_a_4135_; lean_object* v_inheritedTraceOptions_4136_; uint8_t v_hasTrace_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; 
v_toCold_4133_ = lean_ctor_get(v_a_4091_, 0);
v_options_4134_ = lean_ctor_get(v_toCold_4133_, 2);
v_a_4135_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4132_, 1);
v_inheritedTraceOptions_4136_ = lean_ctor_get(v_toCold_4133_, 11);
v_hasTrace_4137_ = lean_ctor_get_uint8(v_options_4134_, sizeof(void*)*1);
v___x_4138_ = l_Lean_Expr_cleanupAnnotations(v_a_4135_);
v___x_4139_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
if (v_hasTrace_4137_ == 0)
{
v___y_4202_ = v_a_4087_;
v___y_4203_ = v_a_4088_;
v___y_4204_ = v_a_4089_;
v___y_4205_ = v_a_4090_;
v___y_4206_ = v_a_4091_;
v___y_4207_ = v_a_4092_;
goto v___jp_4201_;
}
else
{
lean_object* v___x_4228_; uint8_t v___x_4229_; 
v___x_4228_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4136_, v_options_4134_, v___x_4228_);
if (v___x_4229_ == 0)
{
v___y_4202_ = v_a_4087_;
v___y_4203_ = v_a_4088_;
v___y_4204_ = v_a_4089_;
v___y_4205_ = v_a_4090_;
v___y_4206_ = v_a_4091_;
v___y_4207_ = v_a_4092_;
goto v___jp_4201_;
}
else
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4230_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7);
lean_inc_ref(v_val_4096_);
v___x_4231_ = l_Lean_MessageData_ofExpr(v_val_4096_);
v___x_4232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3);
v___x_4234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4232_);
lean_ctor_set(v___x_4234_, 1, v___x_4233_);
lean_inc_ref(v___x_4138_);
v___x_4235_ = l_Lean_MessageData_ofExpr(v___x_4138_);
v___x_4236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4234_);
lean_ctor_set(v___x_4236_, 1, v___x_4235_);
v___x_4237_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9);
v___x_4238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4236_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
lean_inc_ref(v_maxType_4082_);
v___x_4239_ = l_Lean_MessageData_ofExpr(v_maxType_4082_);
v___x_4240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4238_);
lean_ctor_set(v___x_4240_, 1, v___x_4239_);
v___x_4241_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4139_, v___x_4240_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_dec_ref_known(v___x_4241_, 1);
v___y_4202_ = v_a_4087_;
v___y_4203_ = v_a_4088_;
v___y_4204_ = v_a_4089_;
v___y_4205_ = v_a_4090_;
v___y_4206_ = v_a_4091_;
v___y_4207_ = v_a_4092_;
goto v___jp_4201_;
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec_ref(v___x_4138_);
lean_dec_ref_known(v_t_4083_, 3);
lean_dec(v_f_x3f_4084_);
lean_dec_ref(v_maxType_4082_);
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4241_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4241_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
v___jp_4140_:
{
lean_object* v___x_4147_; 
lean_inc_ref(v___x_4138_);
lean_inc_ref(v_maxType_4082_);
v___x_4147_ = l_Lean_Meta_isExprDefEqGuarded(v_maxType_4082_, v___x_4138_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4192_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4150_ = v___x_4147_;
v_isShared_4151_ = v_isSharedCheck_4192_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4147_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4192_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
uint8_t v___x_4152_; 
v___x_4152_ = lean_unbox(v_a_4148_);
lean_dec(v_a_4148_);
if (v___x_4152_ == 0)
{
lean_object* v_toCold_4153_; lean_object* v_options_4154_; uint8_t v_hasTrace_4155_; 
lean_inc_ref(v_val_4096_);
lean_inc_ref(v_infoTrees_4095_);
lean_inc(v_ref_4094_);
lean_del_object(v___x_4150_);
lean_dec_ref_known(v_t_4083_, 3);
v_toCold_4153_ = lean_ctor_get(v___y_4145_, 0);
v_options_4154_ = lean_ctor_get(v_toCold_4153_, 2);
v_hasTrace_4155_ = lean_ctor_get_uint8(v_options_4154_, sizeof(void*)*1);
if (v_hasTrace_4155_ == 0)
{
lean_object* v_currRecDepth_4156_; lean_object* v_ref_4157_; uint16_t v_optionFlags_4158_; uint8_t v_suppressElabErrors_4159_; uint8_t v_isRecordingDeps_4160_; 
lean_dec_ref(v___x_4138_);
v_currRecDepth_4156_ = lean_ctor_get(v___y_4145_, 1);
v_ref_4157_ = lean_ctor_get(v___y_4145_, 2);
v_optionFlags_4158_ = lean_ctor_get_uint16(v___y_4145_, sizeof(void*)*3);
v_suppressElabErrors_4159_ = lean_ctor_get_uint8(v___y_4145_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4160_ = lean_ctor_get_uint8(v___y_4145_, sizeof(void*)*3 + 3);
v___y_4098_ = v___y_4141_;
v___y_4099_ = v___y_4142_;
v___y_4100_ = v___y_4143_;
v___y_4101_ = v___y_4144_;
v_toCold_4102_ = v_toCold_4153_;
v_currRecDepth_4103_ = v_currRecDepth_4156_;
v_ref_4104_ = v_ref_4157_;
v_optionFlags_4105_ = v_optionFlags_4158_;
v_suppressElabErrors_4106_ = v_suppressElabErrors_4159_;
v_isRecordingDeps_4107_ = v_isRecordingDeps_4160_;
v___y_4108_ = v___y_4146_;
goto v___jp_4097_;
}
else
{
lean_object* v_currRecDepth_4161_; lean_object* v_ref_4162_; uint16_t v_optionFlags_4163_; uint8_t v_suppressElabErrors_4164_; uint8_t v_isRecordingDeps_4165_; lean_object* v_inheritedTraceOptions_4166_; lean_object* v___x_4167_; uint8_t v___x_4168_; 
v_currRecDepth_4161_ = lean_ctor_get(v___y_4145_, 1);
v_ref_4162_ = lean_ctor_get(v___y_4145_, 2);
v_optionFlags_4163_ = lean_ctor_get_uint16(v___y_4145_, sizeof(void*)*3);
v_suppressElabErrors_4164_ = lean_ctor_get_uint8(v___y_4145_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4165_ = lean_ctor_get_uint8(v___y_4145_, sizeof(void*)*3 + 3);
v_inheritedTraceOptions_4166_ = lean_ctor_get(v_toCold_4153_, 11);
v___x_4167_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4166_, v_options_4154_, v___x_4167_);
if (v___x_4168_ == 0)
{
lean_dec_ref(v___x_4138_);
v___y_4098_ = v___y_4141_;
v___y_4099_ = v___y_4142_;
v___y_4100_ = v___y_4143_;
v___y_4101_ = v___y_4144_;
v_toCold_4102_ = v_toCold_4153_;
v_currRecDepth_4103_ = v_currRecDepth_4161_;
v_ref_4104_ = v_ref_4162_;
v_optionFlags_4105_ = v_optionFlags_4163_;
v_suppressElabErrors_4106_ = v_suppressElabErrors_4164_;
v_isRecordingDeps_4107_ = v_isRecordingDeps_4165_;
v___y_4108_ = v___y_4146_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4169_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1);
lean_inc_ref(v_val_4096_);
v___x_4170_ = l_Lean_MessageData_ofExpr(v_val_4096_);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4171_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = l_Lean_MessageData_ofExpr(v___x_4138_);
v___x_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5);
v___x_4177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4175_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
lean_inc_ref(v_maxType_4082_);
v___x_4178_ = l_Lean_MessageData_ofExpr(v_maxType_4082_);
v___x_4179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4177_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4139_, v___x_4179_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_dec_ref_known(v___x_4180_, 1);
v___y_4098_ = v___y_4141_;
v___y_4099_ = v___y_4142_;
v___y_4100_ = v___y_4143_;
v___y_4101_ = v___y_4144_;
v_toCold_4102_ = v_toCold_4153_;
v_currRecDepth_4103_ = v_currRecDepth_4161_;
v_ref_4104_ = v_ref_4162_;
v_optionFlags_4105_ = v_optionFlags_4163_;
v_suppressElabErrors_4106_ = v_suppressElabErrors_4164_;
v_isRecordingDeps_4107_ = v_isRecordingDeps_4165_;
v___y_4108_ = v___y_4146_;
goto v___jp_4097_;
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec_ref(v_val_4096_);
lean_dec_ref(v_infoTrees_4095_);
lean_dec(v_ref_4094_);
lean_dec_ref(v_maxType_4082_);
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4180_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4180_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
}
else
{
lean_object* v___x_4190_; 
lean_dec_ref(v___x_4138_);
lean_dec_ref(v_maxType_4082_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 0, v_t_4083_);
v___x_4190_ = v___x_4150_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_t_4083_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
lean_dec_ref(v___x_4138_);
lean_dec_ref_known(v_t_4083_, 3);
lean_dec_ref(v_maxType_4082_);
v_a_4193_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4147_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4147_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
v___jp_4201_:
{
uint8_t v___x_4208_; 
v___x_4208_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_4138_);
if (v___x_4208_ == 0)
{
lean_dec(v_f_x3f_4084_);
v___y_4141_ = v___y_4202_;
v___y_4142_ = v___y_4203_;
v___y_4143_ = v___y_4204_;
v___y_4144_ = v___y_4205_;
v___y_4145_ = v___y_4206_;
v___y_4146_ = v___y_4207_;
goto v___jp_4140_;
}
else
{
if (lean_obj_tag(v_f_x3f_4084_) == 1)
{
lean_object* v_val_4209_; lean_object* v___x_4210_; 
v_val_4209_ = lean_ctor_get(v_f_x3f_4084_, 0);
lean_inc(v_val_4209_);
lean_dec_ref_known(v_f_x3f_4084_, 1);
v___x_4210_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(v_val_4209_, v_maxType_4082_, v_lhs_4085_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
lean_dec(v_val_4209_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4219_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
uint8_t v___x_4215_; 
v___x_4215_ = lean_unbox(v_a_4211_);
lean_dec(v_a_4211_);
if (v___x_4215_ == 0)
{
lean_del_object(v___x_4213_);
v___y_4141_ = v___y_4202_;
v___y_4142_ = v___y_4203_;
v___y_4143_ = v___y_4204_;
v___y_4144_ = v___y_4205_;
v___y_4145_ = v___y_4206_;
v___y_4146_ = v___y_4207_;
goto v___jp_4140_;
}
else
{
lean_object* v___x_4217_; 
lean_dec_ref(v___x_4138_);
lean_dec_ref(v_maxType_4082_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v_t_4083_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_t_4083_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
lean_dec_ref(v___x_4138_);
lean_dec_ref_known(v_t_4083_, 3);
lean_dec_ref(v_maxType_4082_);
v_a_4220_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4210_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4210_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_dec(v_f_x3f_4084_);
v___y_4141_ = v___y_4202_;
v___y_4142_ = v___y_4203_;
v___y_4143_ = v___y_4204_;
v___y_4144_ = v___y_4205_;
v___y_4145_ = v___y_4206_;
v___y_4146_ = v___y_4207_;
goto v___jp_4140_;
}
}
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_dec_ref_known(v_t_4083_, 3);
lean_dec(v_f_x3f_4084_);
lean_dec_ref(v_maxType_4082_);
v_a_4250_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4132_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4132_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
lean_dec_ref_known(v_t_4083_, 3);
lean_dec(v_f_x3f_4084_);
lean_dec_ref(v_maxType_4082_);
v_a_4258_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4130_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4130_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
v___jp_4097_:
{
lean_object* v___x_4109_; lean_object* v_ref_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4109_ = lean_box(0);
v_ref_4110_ = l_Lean_replaceRef(v_ref_4094_, v_ref_4104_);
lean_inc(v_currRecDepth_4103_);
lean_inc_ref(v_toCold_4102_);
v___x_4111_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4111_, 0, v_toCold_4102_);
lean_ctor_set(v___x_4111_, 1, v_currRecDepth_4103_);
lean_ctor_set(v___x_4111_, 2, v_ref_4110_);
lean_ctor_set_uint16(v___x_4111_, sizeof(void*)*3, v_optionFlags_4105_);
lean_ctor_set_uint8(v___x_4111_, sizeof(void*)*3 + 2, v_suppressElabErrors_4106_);
lean_ctor_set_uint8(v___x_4111_, sizeof(void*)*3 + 3, v_isRecordingDeps_4107_);
v___x_4112_ = l_Lean_Elab_Term_mkCoe(v_maxType_4082_, v_val_4096_, v___x_4109_, v___x_4109_, v___x_4109_, v___x_4109_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___x_4111_, v___y_4108_);
lean_dec_ref_known(v___x_4111_, 3);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4121_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4115_ = v___x_4112_;
v_isShared_4116_ = v_isSharedCheck_4121_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4112_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4121_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4117_; lean_object* v___x_4119_; 
v___x_4117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4117_, 0, v_ref_4094_);
lean_ctor_set(v___x_4117_, 1, v_infoTrees_4095_);
lean_ctor_set(v___x_4117_, 2, v_a_4113_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v___x_4117_);
v___x_4119_ = v___x_4115_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec_ref(v_infoTrees_4095_);
lean_dec(v_ref_4094_);
v_a_4122_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4112_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4112_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
}
case 1:
{
lean_object* v_ref_4266_; uint8_t v_kind_4267_; lean_object* v_f_4268_; lean_object* v_lhs_4269_; lean_object* v_rhs_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4386_; 
lean_dec(v_f_x3f_4084_);
v_ref_4266_ = lean_ctor_get(v_t_4083_, 0);
v_kind_4267_ = lean_ctor_get_uint8(v_t_4083_, sizeof(void*)*4);
v_f_4268_ = lean_ctor_get(v_t_4083_, 1);
v_lhs_4269_ = lean_ctor_get(v_t_4083_, 2);
v_rhs_4270_ = lean_ctor_get(v_t_4083_, 3);
v_isSharedCheck_4386_ = !lean_is_exclusive(v_t_4083_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4272_ = v_t_4083_;
v_isShared_4273_ = v_isSharedCheck_4386_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_rhs_4270_);
lean_inc(v_lhs_4269_);
lean_inc(v_f_4268_);
lean_inc(v_ref_4266_);
lean_dec(v_t_4083_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4386_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
switch(v_kind_4267_)
{
case 2:
{
lean_object* v___x_4292_; uint8_t v___x_4293_; lean_object* v___x_4294_; 
lean_del_object(v___x_4272_);
v___x_4292_ = lean_box(0);
v___x_4293_ = 0;
v___x_4294_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4082_, v_rhs_4270_, v___x_4292_, v___x_4293_, v___x_4293_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4303_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4303_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4303_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4299_; lean_object* v___x_4301_; 
v___x_4299_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_4299_, 0, v_ref_4266_);
lean_ctor_set(v___x_4299_, 1, v_f_4268_);
lean_ctor_set(v___x_4299_, 2, v_lhs_4269_);
lean_ctor_set(v___x_4299_, 3, v_a_4295_);
lean_ctor_set_uint8(v___x_4299_, sizeof(void*)*4, v_kind_4267_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4299_);
v___x_4301_ = v___x_4297_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
else
{
lean_dec_ref(v_lhs_4269_);
lean_dec_ref(v_f_4268_);
lean_dec(v_ref_4266_);
return v___x_4294_;
}
}
case 3:
{
lean_object* v___x_4304_; uint8_t v___x_4305_; lean_object* v___x_4306_; 
lean_del_object(v___x_4272_);
v___x_4304_ = lean_box(0);
v___x_4305_ = 0;
v___x_4306_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4082_, v_lhs_4269_, v___x_4304_, v___x_4305_, v___x_4305_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4315_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4309_ = v___x_4306_;
v_isShared_4310_ = v_isSharedCheck_4315_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4306_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4315_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4311_; lean_object* v___x_4313_; 
v___x_4311_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_4311_, 0, v_ref_4266_);
lean_ctor_set(v___x_4311_, 1, v_f_4268_);
lean_ctor_set(v___x_4311_, 2, v_a_4307_);
lean_ctor_set(v___x_4311_, 3, v_rhs_4270_);
lean_ctor_set_uint8(v___x_4311_, sizeof(void*)*4, v_kind_4267_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 0, v___x_4311_);
v___x_4313_ = v___x_4309_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4311_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
else
{
lean_dec_ref(v_rhs_4270_);
lean_dec_ref(v_f_4268_);
lean_dec(v_ref_4266_);
return v___x_4306_;
}
}
default: 
{
if (v_isPred_4086_ == 0)
{
lean_object* v___x_4316_; 
lean_inc_ref(v_maxType_4082_);
v___x_4316_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(v_f_4268_, v_maxType_4082_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; uint8_t v___x_4318_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4318_ = lean_unbox(v_a_4317_);
lean_dec(v_a_4317_);
if (v___x_4318_ == 0)
{
lean_object* v_toCold_4319_; lean_object* v_currRecDepth_4320_; lean_object* v_ref_4321_; uint16_t v_optionFlags_4322_; uint8_t v_suppressElabErrors_4323_; uint8_t v_isRecordingDeps_4324_; lean_object* v___x_4325_; lean_object* v_ref_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
lean_del_object(v___x_4272_);
lean_dec_ref(v_maxType_4082_);
v_toCold_4319_ = lean_ctor_get(v_a_4091_, 0);
v_currRecDepth_4320_ = lean_ctor_get(v_a_4091_, 1);
v_ref_4321_ = lean_ctor_get(v_a_4091_, 2);
v_optionFlags_4322_ = lean_ctor_get_uint16(v_a_4091_, sizeof(void*)*3);
v_suppressElabErrors_4323_ = lean_ctor_get_uint8(v_a_4091_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4324_ = lean_ctor_get_uint8(v_a_4091_, sizeof(void*)*3 + 3);
v___x_4325_ = lean_box(0);
v_ref_4326_ = l_Lean_replaceRef(v_ref_4266_, v_ref_4321_);
lean_inc(v_currRecDepth_4320_);
lean_inc_ref(v_toCold_4319_);
v___x_4327_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4327_, 0, v_toCold_4319_);
lean_ctor_set(v___x_4327_, 1, v_currRecDepth_4320_);
lean_ctor_set(v___x_4327_, 2, v_ref_4326_);
lean_ctor_set_uint16(v___x_4327_, sizeof(void*)*3, v_optionFlags_4322_);
lean_ctor_set_uint8(v___x_4327_, sizeof(void*)*3 + 2, v_suppressElabErrors_4323_);
lean_ctor_set_uint8(v___x_4327_, sizeof(void*)*3 + 3, v_isRecordingDeps_4324_);
v___x_4328_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_lhs_4269_, v___x_4325_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v___x_4327_, v_a_4092_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4330_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4328_, 1);
v___x_4330_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_rhs_4270_, v___x_4325_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v___x_4327_, v_a_4092_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; uint8_t v___x_4332_; uint8_t v___x_4333_; lean_object* v___x_4334_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
v___x_4332_ = 1;
v___x_4333_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_4267_, v___x_4332_);
v___x_4334_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v___x_4333_, v_f_4268_, v_a_4329_, v_a_4331_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v___x_4327_, v_a_4092_);
lean_dec_ref_known(v___x_4327_, 3);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4336_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
v___x_4336_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v_a_4092_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4345_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4339_ = v___x_4336_;
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4336_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4341_, 0, v_ref_4266_);
lean_ctor_set(v___x_4341_, 1, v_a_4337_);
lean_ctor_set(v___x_4341_, 2, v_a_4335_);
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 0, v___x_4341_);
v___x_4343_ = v___x_4339_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4341_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec(v_a_4335_);
lean_dec(v_ref_4266_);
v_a_4346_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4336_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4336_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
lean_dec(v_ref_4266_);
v_a_4354_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_4334_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4334_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
lean_dec(v_a_4329_);
lean_dec_ref_known(v___x_4327_, 3);
lean_dec_ref(v_f_4268_);
lean_dec(v_ref_4266_);
v_a_4362_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4330_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4330_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
else
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
lean_dec_ref_known(v___x_4327_, 3);
lean_dec_ref(v_rhs_4270_);
lean_dec_ref(v_f_4268_);
lean_dec(v_ref_4266_);
v_a_4370_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4372_ = v___x_4328_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4328_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
else
{
goto v___jp_4274_;
}
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
lean_del_object(v___x_4272_);
lean_dec_ref(v_rhs_4270_);
lean_dec_ref(v_lhs_4269_);
lean_dec_ref(v_f_4268_);
lean_dec(v_ref_4266_);
lean_dec_ref(v_maxType_4082_);
v_a_4378_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4316_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4316_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
else
{
goto v___jp_4274_;
}
}
}
v___jp_4274_:
{
uint8_t v___x_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; lean_object* v___x_4278_; 
v___x_4275_ = 1;
lean_inc_ref(v_f_4268_);
v___x_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4276_, 0, v_f_4268_);
v___x_4277_ = 0;
lean_inc_ref(v___x_4276_);
lean_inc_ref(v_maxType_4082_);
v___x_4278_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4082_, v_lhs_4269_, v___x_4276_, v___x_4275_, v___x_4277_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4280_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4279_);
lean_dec_ref_known(v___x_4278_, 1);
v___x_4280_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4082_, v_rhs_4270_, v___x_4276_, v___x_4277_, v___x_4277_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4291_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4283_ = v___x_4280_;
v_isShared_4284_ = v_isSharedCheck_4291_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4280_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4291_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 3, v_a_4281_);
lean_ctor_set(v___x_4272_, 2, v_a_4279_);
v___x_4286_ = v___x_4272_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_ref_4266_);
lean_ctor_set(v_reuseFailAlloc_4290_, 1, v_f_4268_);
lean_ctor_set(v_reuseFailAlloc_4290_, 2, v_a_4279_);
lean_ctor_set(v_reuseFailAlloc_4290_, 3, v_a_4281_);
lean_ctor_set_uint8(v_reuseFailAlloc_4290_, sizeof(void*)*4, v_kind_4267_);
v___x_4286_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v___x_4288_; 
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4286_);
v___x_4288_ = v___x_4283_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4286_);
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
else
{
lean_dec(v_a_4279_);
lean_del_object(v___x_4272_);
lean_dec_ref(v_f_4268_);
lean_dec(v_ref_4266_);
return v___x_4280_;
}
}
else
{
lean_dec_ref_known(v___x_4276_, 1);
lean_del_object(v___x_4272_);
lean_dec_ref(v_rhs_4270_);
lean_dec_ref(v_f_4268_);
lean_dec(v_ref_4266_);
lean_dec_ref(v_maxType_4082_);
return v___x_4278_;
}
}
}
}
case 2:
{
lean_object* v_ref_4387_; lean_object* v_f_4388_; lean_object* v_arg_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4407_; 
lean_dec(v_f_x3f_4084_);
v_ref_4387_ = lean_ctor_get(v_t_4083_, 0);
v_f_4388_ = lean_ctor_get(v_t_4083_, 1);
v_arg_4389_ = lean_ctor_get(v_t_4083_, 2);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_t_4083_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4391_ = v_t_4083_;
v_isShared_4392_ = v_isSharedCheck_4407_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_arg_4389_);
lean_inc(v_f_4388_);
lean_inc(v_ref_4387_);
lean_dec(v_t_4083_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4407_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4393_; uint8_t v___x_4394_; lean_object* v___x_4395_; 
v___x_4393_ = lean_box(0);
v___x_4394_ = 0;
v___x_4395_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4082_, v_arg_4389_, v___x_4393_, v___x_4394_, v___x_4394_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4406_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4398_ = v___x_4395_;
v_isShared_4399_ = v_isSharedCheck_4406_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4406_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 2, v_a_4396_);
v___x_4401_ = v___x_4391_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_ref_4387_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v_f_4388_);
lean_ctor_set(v_reuseFailAlloc_4405_, 2, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
lean_object* v___x_4403_; 
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v___x_4401_);
v___x_4403_ = v___x_4398_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
else
{
lean_del_object(v___x_4391_);
lean_dec_ref(v_f_4388_);
lean_dec(v_ref_4387_);
return v___x_4395_;
}
}
}
default: 
{
lean_object* v_macroName_4408_; lean_object* v_stx_4409_; lean_object* v_stx_x27_4410_; lean_object* v_nested_4411_; lean_object* v_toCold_4412_; lean_object* v_currRecDepth_4413_; lean_object* v_ref_4414_; uint16_t v_optionFlags_4415_; uint8_t v_suppressElabErrors_4416_; uint8_t v_isRecordingDeps_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___f_4420_; lean_object* v_ref_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v_macroName_4408_ = lean_ctor_get(v_t_4083_, 0);
lean_inc(v_macroName_4408_);
v_stx_4409_ = lean_ctor_get(v_t_4083_, 1);
lean_inc_n(v_stx_4409_, 2);
v_stx_x27_4410_ = lean_ctor_get(v_t_4083_, 2);
lean_inc_n(v_stx_x27_4410_, 2);
v_nested_4411_ = lean_ctor_get(v_t_4083_, 3);
lean_inc_ref(v_nested_4411_);
lean_dec_ref_known(v_t_4083_, 4);
v_toCold_4412_ = lean_ctor_get(v_a_4091_, 0);
v_currRecDepth_4413_ = lean_ctor_get(v_a_4091_, 1);
v_ref_4414_ = lean_ctor_get(v_a_4091_, 2);
v_optionFlags_4415_ = lean_ctor_get_uint16(v_a_4091_, sizeof(void*)*3);
v_suppressElabErrors_4416_ = lean_ctor_get_uint8(v_a_4091_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4417_ = lean_ctor_get_uint8(v_a_4091_, sizeof(void*)*3 + 3);
v___x_4418_ = lean_box(v_lhs_4085_);
v___x_4419_ = lean_box(v_isPred_4086_);
v___f_4420_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4420_, 0, v_maxType_4082_);
lean_closure_set(v___f_4420_, 1, v_nested_4411_);
lean_closure_set(v___f_4420_, 2, v_f_x3f_4084_);
lean_closure_set(v___f_4420_, 3, v___x_4418_);
lean_closure_set(v___f_4420_, 4, v___x_4419_);
lean_closure_set(v___f_4420_, 5, v_macroName_4408_);
lean_closure_set(v___f_4420_, 6, v_stx_4409_);
lean_closure_set(v___f_4420_, 7, v_stx_x27_4410_);
v_ref_4421_ = l_Lean_replaceRef(v_stx_4409_, v_ref_4414_);
lean_inc(v_currRecDepth_4413_);
lean_inc_ref(v_toCold_4412_);
v___x_4422_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4422_, 0, v_toCold_4412_);
lean_ctor_set(v___x_4422_, 1, v_currRecDepth_4413_);
lean_ctor_set(v___x_4422_, 2, v_ref_4421_);
lean_ctor_set_uint16(v___x_4422_, sizeof(void*)*3, v_optionFlags_4415_);
lean_ctor_set_uint8(v___x_4422_, sizeof(void*)*3 + 2, v_suppressElabErrors_4416_);
lean_ctor_set_uint8(v___x_4422_, sizeof(void*)*3 + 3, v_isRecordingDeps_4417_);
v___x_4423_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_stx_4409_, v_stx_x27_4410_, v___f_4420_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v___x_4422_, v_a_4092_);
lean_dec_ref_known(v___x_4422_, 3);
return v___x_4423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(lean_object* v_t_4424_, lean_object* v_maxType_4425_, uint8_t v_isPred_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_){
_start:
{
lean_object* v___x_4434_; uint8_t v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = lean_box(0);
v___x_4435_ = 0;
v___x_4436_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4425_, v_t_4424_, v___x_4434_, v___x_4435_, v_isPred_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe___boxed(lean_object* v_t_4437_, lean_object* v_maxType_4438_, lean_object* v_isPred_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_){
_start:
{
uint8_t v_isPred_boxed_4447_; lean_object* v_res_4448_; 
v_isPred_boxed_4447_ = lean_unbox(v_isPred_4439_);
v_res_4448_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v_t_4437_, v_maxType_4438_, v_isPred_boxed_4447_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec(v_a_4441_);
lean_dec_ref(v_a_4440_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___boxed(lean_object* v_tree_4449_, lean_object* v_expectedType_x3f_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_tree_4449_, v_expectedType_x3f_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___boxed(lean_object* v_maxType_4459_, lean_object* v_t_4460_, lean_object* v_f_x3f_4461_, lean_object* v_lhs_4462_, lean_object* v_isPred_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
uint8_t v_lhs_boxed_4471_; uint8_t v_isPred_boxed_4472_; lean_object* v_res_4473_; 
v_lhs_boxed_4471_ = lean_unbox(v_lhs_4462_);
v_isPred_boxed_4472_ = lean_unbox(v_isPred_4463_);
v_res_4473_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4459_, v_t_4460_, v_f_x3f_4461_, v_lhs_boxed_4471_, v_isPred_boxed_4472_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr_spec__2(lean_object* v_msg_4474_){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = l_Lean_instInhabitedExpr;
v___x_4476_ = lean_panic_fn_borrowed(v___x_4475_, v_msg_4474_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0(lean_object* v_cls_4477_, lean_object* v_msg_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v___x_4486_; 
v___x_4486_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v_cls_4477_, v_msg_4478_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___boxed(lean_object* v_cls_4487_, lean_object* v_msg_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0(v_cls_4487_, v_msg_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp(lean_object* v_stx_4497_, lean_object* v_expectedType_x3f_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v_stx_4497_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v_a_4507_; lean_object* v___x_4508_; 
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_a_4507_);
lean_dec_ref_known(v___x_4506_, 1);
v___x_4508_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_a_4507_, v_expectedType_x3f_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
return v___x_4508_;
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v_expectedType_x3f_4498_);
v_a_4509_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4506_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4506_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp___boxed(lean_object* v_stx_4517_, lean_object* v_expectedType_x3f_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_Elab_Term_Op_elabOp(v_stx_4517_, v_expectedType_x3f_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp(lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v___x_4536_; 
v___x_4536_ = l_Lean_Elab_Term_Op_elabOp(v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp___boxed(lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_Elab_Term_Op_elabBinOp(v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1(){
_start:
{
lean_object* v___f_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___f_4556_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4557_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4558_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1));
v___x_4559_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2));
v___x_4560_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4557_, v___x_4558_, v___x_4559_, v___f_4556_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___boxed(lean_object* v_a_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1();
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3(){
_start:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4589_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2));
v___x_4590_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__6));
v___x_4591_ = l_Lean_addBuiltinDeclarationRanges(v___x_4589_, v___x_4590_);
return v___x_4591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___boxed(lean_object* v_a_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3();
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy(lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v___x_4603_; 
v___x_4603_ = l_Lean_Elab_Term_Op_elabOp(v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy___boxed(lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lean_Elab_Term_Op_elabBinOpLazy(v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1(){
_start:
{
lean_object* v___f_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___f_4622_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4623_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4624_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3));
v___x_4625_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1));
v___x_4626_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4623_, v___x_4624_, v___x_4625_, v___f_4622_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___boxed(lean_object* v_a_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1();
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3(){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4655_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1));
v___x_4656_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__6));
v___x_4657_ = l_Lean_addBuiltinDeclarationRanges(v___x_4655_, v___x_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___boxed(lean_object* v_a_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3();
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact(lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v___x_4669_; 
v___x_4669_ = l_Lean_Elab_Term_Op_elabOp(v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact___boxed(lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_Lean_Elab_Term_Op_elabLeftact(v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
lean_dec(v_a_4675_);
lean_dec_ref(v_a_4674_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1(){
_start:
{
lean_object* v___f_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___f_4688_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4689_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4690_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7));
v___x_4691_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1));
v___x_4692_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4689_, v___x_4690_, v___x_4691_, v___f_4688_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___boxed(lean_object* v_a_4693_){
_start:
{
lean_object* v_res_4694_; 
v_res_4694_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1();
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3(){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4721_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1));
v___x_4722_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__6));
v___x_4723_ = l_Lean_addBuiltinDeclarationRanges(v___x_4721_, v___x_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___boxed(lean_object* v_a_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3();
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact(lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l_Lean_Elab_Term_Op_elabOp(v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact___boxed(lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Lean_Elab_Term_Op_elabRightact(v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_);
lean_dec(v_a_4743_);
lean_dec_ref(v_a_4742_);
lean_dec(v_a_4741_);
lean_dec_ref(v_a_4740_);
lean_dec(v_a_4739_);
lean_dec_ref(v_a_4738_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1(){
_start:
{
lean_object* v___f_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___f_4754_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4755_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4756_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9));
v___x_4757_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1));
v___x_4758_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4755_, v___x_4756_, v___x_4757_, v___f_4754_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___boxed(lean_object* v_a_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1();
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3(){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4787_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1));
v___x_4788_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__6));
v___x_4789_ = l_Lean_addBuiltinDeclarationRanges(v___x_4787_, v___x_4788_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___boxed(lean_object* v_a_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3();
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp(lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_){
_start:
{
lean_object* v___x_4801_; 
v___x_4801_ = l_Lean_Elab_Term_Op_elabOp(v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp___boxed(lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l_Lean_Elab_Term_Op_elabUnOp(v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1(){
_start:
{
lean_object* v___f_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___f_4820_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4821_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4822_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5));
v___x_4823_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1));
v___x_4824_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4821_, v___x_4822_, v___x_4823_, v___f_4820_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___boxed(lean_object* v_a_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1();
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3(){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4853_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1));
v___x_4854_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__6));
v___x_4855_ = l_Lean_addBuiltinDeclarationRanges(v___x_4853_, v___x_4854_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___boxed(lean_object* v_a_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3();
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0(lean_object* v_k_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v___x_4866_; 
lean_inc(v___y_4860_);
lean_inc_ref(v___y_4859_);
v___x_4866_ = lean_apply_7(v_k_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, lean_box(0));
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0___boxed(lean_object* v_k_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0(v_k_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(lean_object* v_k_4876_, uint8_t v_allowLevelAssignments_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_){
_start:
{
lean_object* v___f_4885_; lean_object* v___x_4886_; 
lean_inc(v___y_4879_);
lean_inc_ref(v___y_4878_);
v___f_4885_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4885_, 0, v_k_4876_);
lean_closure_set(v___f_4885_, 1, v___y_4878_);
lean_closure_set(v___f_4885_, 2, v___y_4879_);
v___x_4886_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_4877_, v___f_4885_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
if (lean_obj_tag(v___x_4886_) == 0)
{
return v___x_4886_;
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4886_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4886_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___boxed(lean_object* v_k_4895_, lean_object* v_allowLevelAssignments_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4904_; lean_object* v_res_4905_; 
v_allowLevelAssignments_boxed_4904_ = lean_unbox(v_allowLevelAssignments_4896_);
v_res_4905_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v_k_4895_, v_allowLevelAssignments_boxed_4904_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_);
lean_dec(v___y_4902_);
lean_dec_ref(v___y_4901_);
lean_dec(v___y_4900_);
lean_dec_ref(v___y_4899_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0(lean_object* v_00_u03b1_4906_, lean_object* v_k_4907_, uint8_t v_allowLevelAssignments_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v___x_4916_; 
v___x_4916_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v_k_4907_, v_allowLevelAssignments_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_);
return v___x_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___boxed(lean_object* v_00_u03b1_4917_, lean_object* v_k_4918_, lean_object* v_allowLevelAssignments_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4927_; lean_object* v_res_4928_; 
v_allowLevelAssignments_boxed_4927_ = lean_unbox(v_allowLevelAssignments_4919_);
v_res_4928_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0(v_00_u03b1_4917_, v_k_4918_, v_allowLevelAssignments_boxed_4927_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0(lean_object* v_a_4929_, lean_object* v___x_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = l_Lean_Meta_isExprDefEq(v_a_4929_, v___x_4930_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0___boxed(lean_object* v_a_4939_, lean_object* v___x_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v_res_4948_; 
v_res_4948_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0(v_a_4939_, v___x_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
return v_res_4948_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0(void){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4949_ = lean_box(0);
v___x_4950_ = l_Lean_mkSort(v___x_4949_);
return v___x_4950_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3(void){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4954_ = lean_box(0);
v___x_4955_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__2));
v___x_4956_ = l_Lean_mkConst(v___x_4955_, v___x_4954_);
return v___x_4956_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4(void){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4957_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3);
v___x_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4957_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(uint8_t v_noProp_4959_, lean_object* v_e_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_){
_start:
{
if (v_noProp_4959_ == 0)
{
lean_object* v___x_4968_; 
v___x_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4968_, 0, v_e_4960_);
return v___x_4968_;
}
else
{
lean_object* v___x_4969_; 
lean_inc(v_a_4966_);
lean_inc_ref(v_a_4965_);
lean_inc(v_a_4964_);
lean_inc_ref(v_a_4963_);
lean_inc_ref(v_e_4960_);
v___x_4969_ = lean_infer_type(v_e_4960_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; lean_object* v___x_4971_; lean_object* v___f_4972_; uint8_t v___x_4973_; lean_object* v___x_4974_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_a_4970_);
lean_dec_ref_known(v___x_4969_, 1);
v___x_4971_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0);
v___f_4972_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4972_, 0, v_a_4970_);
lean_closure_set(v___f_4972_, 1, v___x_4971_);
v___x_4973_ = 0;
v___x_4974_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v___f_4972_, v___x_4973_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4986_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4977_ = v___x_4974_;
v_isShared_4978_ = v_isSharedCheck_4986_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4974_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4986_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
uint8_t v___x_4979_; 
v___x_4979_ = lean_unbox(v_a_4975_);
lean_dec(v_a_4975_);
if (v___x_4979_ == 0)
{
lean_object* v___x_4981_; 
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 0, v_e_4960_);
v___x_4981_ = v___x_4977_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_e_4960_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
else
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
lean_del_object(v___x_4977_);
v___x_4983_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4);
v___x_4984_ = lean_box(0);
v___x_4985_ = l_Lean_Elab_Term_ensureHasType(v___x_4983_, v_e_4960_, v___x_4984_, v___x_4984_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
return v___x_4985_;
}
}
}
else
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
lean_dec_ref(v_e_4960_);
v_a_4987_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4989_ = v___x_4974_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4974_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
}
else
{
lean_dec_ref(v_e_4960_);
return v___x_4969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___boxed(lean_object* v_noProp_4995_, lean_object* v_e_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_){
_start:
{
uint8_t v_noProp_boxed_5004_; lean_object* v_res_5005_; 
v_noProp_boxed_5004_ = lean_unbox(v_noProp_4995_);
v_res_5005_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_boxed_5004_, v_e_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
lean_dec(v_a_5002_);
lean_dec_ref(v_a_5001_);
lean_dec(v_a_5000_);
lean_dec_ref(v_a_4999_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
return v_res_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0(lean_object* v_val_5006_, lean_object* v___x_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_){
_start:
{
lean_object* v___x_5015_; 
v___x_5015_ = l_Lean_Meta_isExprDefEq(v_val_5006_, v___x_5007_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
return v___x_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0___boxed(lean_object* v_val_5016_, lean_object* v___x_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l_Lean_Elab_Term_Op_elabBinRelCore___lam__0(v_val_5016_, v___x_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
return v_res_5025_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2(void){
_start:
{
lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5030_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
v___x_5031_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2));
v___x_5032_ = l_Lean_Name_append(v___x_5031_, v___x_5030_);
return v___x_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1(lean_object* v___x_5033_, lean_object* v___x_5034_, lean_object* v_stx_5035_, lean_object* v_val_5036_, uint8_t v_noProp_5037_, lean_object* v___x_5038_, lean_object* v_expectedType_x3f_5039_, uint8_t v___x_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_){
_start:
{
lean_object* v_toCold_5048_; lean_object* v_currRecDepth_5049_; lean_object* v_ref_5050_; uint16_t v_optionFlags_5051_; uint8_t v_suppressElabErrors_5052_; uint8_t v_isRecordingDeps_5053_; lean_object* v_ref_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v_toCold_5048_ = lean_ctor_get(v___y_5045_, 0);
v_currRecDepth_5049_ = lean_ctor_get(v___y_5045_, 1);
v_ref_5050_ = lean_ctor_get(v___y_5045_, 2);
v_optionFlags_5051_ = lean_ctor_get_uint16(v___y_5045_, sizeof(void*)*3);
v_suppressElabErrors_5052_ = lean_ctor_get_uint8(v___y_5045_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5053_ = lean_ctor_get_uint8(v___y_5045_, sizeof(void*)*3 + 3);
v_ref_5054_ = l_Lean_replaceRef(v___x_5033_, v_ref_5050_);
lean_inc(v_currRecDepth_5049_);
lean_inc_ref(v_toCold_5048_);
v___x_5055_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5055_, 0, v_toCold_5048_);
lean_ctor_set(v___x_5055_, 1, v_currRecDepth_5049_);
lean_ctor_set(v___x_5055_, 2, v_ref_5054_);
lean_ctor_set_uint16(v___x_5055_, sizeof(void*)*3, v_optionFlags_5051_);
lean_ctor_set_uint8(v___x_5055_, sizeof(void*)*3 + 2, v_suppressElabErrors_5052_);
lean_ctor_set_uint8(v___x_5055_, sizeof(void*)*3 + 3, v_isRecordingDeps_5053_);
lean_inc(v___x_5033_);
v___x_5056_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v___x_5033_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___x_5055_, v___y_5046_);
lean_dec_ref_known(v___x_5055_, 3);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_object* v_a_5057_; lean_object* v_ref_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v_a_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_a_5057_);
lean_dec_ref_known(v___x_5056_, 1);
v_ref_5058_ = l_Lean_replaceRef(v___x_5034_, v_ref_5050_);
lean_inc(v_currRecDepth_5049_);
lean_inc_ref(v_toCold_5048_);
v___x_5059_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5059_, 0, v_toCold_5048_);
lean_ctor_set(v___x_5059_, 1, v_currRecDepth_5049_);
lean_ctor_set(v___x_5059_, 2, v_ref_5058_);
lean_ctor_set_uint16(v___x_5059_, sizeof(void*)*3, v_optionFlags_5051_);
lean_ctor_set_uint8(v___x_5059_, sizeof(void*)*3 + 2, v_suppressElabErrors_5052_);
lean_ctor_set_uint8(v___x_5059_, sizeof(void*)*3 + 3, v_isRecordingDeps_5053_);
lean_inc(v___x_5034_);
v___x_5060_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v___x_5034_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___x_5059_, v___y_5046_);
lean_dec_ref_known(v___x_5059_, 3);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; uint8_t v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___x_5120_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc_n(v_a_5061_, 2);
lean_dec_ref_known(v___x_5060_, 1);
v___x_5062_ = 0;
lean_inc(v_a_5057_);
lean_inc_ref(v_val_5036_);
v___x_5063_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_5063_, 0, v_stx_5035_);
lean_ctor_set(v___x_5063_, 1, v_val_5036_);
lean_ctor_set(v___x_5063_, 2, v_a_5057_);
lean_ctor_set(v___x_5063_, 3, v_a_5061_);
lean_ctor_set_uint8(v___x_5063_, sizeof(void*)*4, v___x_5062_);
v___x_5064_ = lean_box(0);
lean_inc_ref(v___x_5063_);
v___x_5120_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v___x_5063_, v___x_5064_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v_options_5121_; lean_object* v_a_5122_; lean_object* v_inheritedTraceOptions_5123_; uint8_t v_hasTrace_5124_; lean_object* v___x_5125_; uint8_t v___y_5127_; lean_object* v_maxType_5128_; lean_object* v___y_5129_; lean_object* v___y_5130_; lean_object* v___y_5131_; lean_object* v___y_5132_; lean_object* v___y_5133_; lean_object* v___y_5134_; lean_object* v___y_5174_; lean_object* v___y_5175_; lean_object* v___y_5176_; lean_object* v___y_5177_; lean_object* v___y_5178_; lean_object* v___y_5179_; lean_object* v___y_5199_; lean_object* v___y_5200_; 
v_options_5121_ = lean_ctor_get(v_toCold_5048_, 2);
v_a_5122_ = lean_ctor_get(v___x_5120_, 0);
lean_inc(v_a_5122_);
lean_dec_ref_known(v___x_5120_, 1);
v_inheritedTraceOptions_5123_ = lean_ctor_get(v_toCold_5048_, 11);
v_hasTrace_5124_ = lean_ctor_get_uint8(v_options_5121_, sizeof(void*)*1);
v___x_5125_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
if (v_hasTrace_5124_ == 0)
{
v___y_5174_ = v___y_5041_;
v___y_5175_ = v___y_5042_;
v___y_5176_ = v___y_5043_;
v___y_5177_ = v___y_5044_;
v___y_5178_ = v___y_5045_;
v___y_5179_ = v___y_5046_;
goto v___jp_5173_;
}
else
{
lean_object* v___x_5211_; uint8_t v___x_5212_; 
v___x_5211_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2, &l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2_once, _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2);
v___x_5212_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5123_, v_options_5121_, v___x_5211_);
if (v___x_5212_ == 0)
{
v___y_5174_ = v___y_5041_;
v___y_5175_ = v___y_5042_;
v___y_5176_ = v___y_5043_;
v___y_5177_ = v___y_5044_;
v___y_5178_ = v___y_5045_;
v___y_5179_ = v___y_5046_;
goto v___jp_5173_;
}
else
{
lean_object* v_max_x3f_5213_; uint8_t v_hasUncomparable_5214_; uint8_t v_hasUnknown_5215_; lean_object* v___y_5217_; lean_object* v___y_5218_; lean_object* v___x_5227_; lean_object* v___y_5229_; 
v_max_x3f_5213_ = lean_ctor_get(v_a_5122_, 0);
v_hasUncomparable_5214_ = lean_ctor_get_uint8(v_a_5122_, sizeof(void*)*1);
v_hasUnknown_5215_ = lean_ctor_get_uint8(v_a_5122_, sizeof(void*)*1 + 1);
v___x_5227_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8);
if (v_hasUncomparable_5214_ == 0)
{
lean_object* v___x_5237_; 
v___x_5237_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_5229_ = v___x_5237_;
goto v___jp_5228_;
}
else
{
lean_object* v___x_5238_; 
v___x_5238_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_5229_ = v___x_5238_;
goto v___jp_5228_;
}
v___jp_5216_:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; 
lean_inc_ref(v___y_5218_);
v___x_5219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5219_, 0, v___y_5218_);
v___x_5220_ = l_Lean_MessageData_ofFormat(v___x_5219_);
v___x_5221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5221_, 0, v___y_5217_);
lean_ctor_set(v___x_5221_, 1, v___x_5220_);
v___x_5222_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3);
v___x_5223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5223_, 0, v___x_5221_);
lean_ctor_set(v___x_5223_, 1, v___x_5222_);
if (lean_obj_tag(v_max_x3f_5213_) == 0)
{
lean_object* v___x_5224_; 
v___x_5224_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6);
v___y_5199_ = v___x_5223_;
v___y_5200_ = v___x_5224_;
goto v___jp_5198_;
}
else
{
lean_object* v_val_5225_; lean_object* v___x_5226_; 
v_val_5225_ = lean_ctor_get(v_max_x3f_5213_, 0);
lean_inc(v_val_5225_);
v___x_5226_ = l_Lean_MessageData_ofExpr(v_val_5225_);
v___y_5199_ = v___x_5223_;
v___y_5200_ = v___x_5226_;
goto v___jp_5198_;
}
}
v___jp_5228_:
{
lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; 
lean_inc_ref(v___y_5229_);
v___x_5230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5230_, 0, v___y_5229_);
v___x_5231_ = l_Lean_MessageData_ofFormat(v___x_5230_);
v___x_5232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5227_);
lean_ctor_set(v___x_5232_, 1, v___x_5231_);
v___x_5233_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10);
v___x_5234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5232_);
lean_ctor_set(v___x_5234_, 1, v___x_5233_);
if (v_hasUnknown_5215_ == 0)
{
lean_object* v___x_5235_; 
v___x_5235_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_5217_ = v___x_5234_;
v___y_5218_ = v___x_5235_;
goto v___jp_5216_;
}
else
{
lean_object* v___x_5236_; 
v___x_5236_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_5217_ = v___x_5234_;
v___y_5218_ = v___x_5236_;
goto v___jp_5216_;
}
}
}
}
v___jp_5126_:
{
lean_object* v___x_5135_; 
v___x_5135_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v___x_5063_, v_maxType_5128_, v___y_5127_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_object* v_a_5136_; lean_object* v___x_5137_; 
v_a_5136_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_a_5136_);
lean_dec_ref_known(v___x_5135_, 1);
v___x_5137_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5136_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v_toCold_5138_; lean_object* v_options_5139_; uint8_t v_hasTrace_5140_; 
v_toCold_5138_ = lean_ctor_get(v___y_5133_, 0);
v_options_5139_ = lean_ctor_get(v_toCold_5138_, 2);
v_hasTrace_5140_ = lean_ctor_get_uint8(v_options_5139_, sizeof(void*)*1);
if (v_hasTrace_5140_ == 0)
{
lean_dec(v___y_5134_);
lean_dec_ref(v___y_5133_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
return v___x_5137_;
}
else
{
lean_object* v_a_5141_; lean_object* v_inheritedTraceOptions_5142_; lean_object* v___x_5143_; uint8_t v___x_5144_; 
v_a_5141_ = lean_ctor_get(v___x_5137_, 0);
v_inheritedTraceOptions_5142_ = lean_ctor_get(v_toCold_5138_, 11);
v___x_5143_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2, &l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2_once, _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2);
v___x_5144_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5142_, v_options_5139_, v___x_5143_);
if (v___x_5144_ == 0)
{
lean_dec(v___y_5134_);
lean_dec_ref(v___y_5133_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
return v___x_5137_;
}
else
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
lean_inc_n(v_a_5141_, 2);
lean_dec_ref_known(v___x_5137_, 1);
v___x_5145_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1);
v___x_5146_ = l_Lean_MessageData_ofExpr(v_a_5141_);
v___x_5147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5147_, 0, v___x_5145_);
lean_ctor_set(v___x_5147_, 1, v___x_5146_);
v___x_5148_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_5125_, v___x_5147_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_);
lean_dec(v___y_5134_);
lean_dec_ref(v___y_5133_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5155_ == 0)
{
lean_object* v_unused_5156_; 
v_unused_5156_ = lean_ctor_get(v___x_5148_, 0);
lean_dec(v_unused_5156_);
v___x_5150_ = v___x_5148_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_dec(v___x_5148_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
lean_ctor_set(v___x_5150_, 0, v_a_5141_);
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5141_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec(v_a_5141_);
v_a_5157_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5148_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5148_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
}
else
{
lean_dec(v___y_5134_);
lean_dec_ref(v___y_5133_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
return v___x_5137_;
}
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_dec(v___y_5134_);
lean_dec_ref(v___y_5133_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
v_a_5165_ = lean_ctor_get(v___x_5135_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5135_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5135_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5135_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
}
}
v___jp_5173_:
{
uint8_t v_hasUncomparable_5180_; 
v_hasUncomparable_5180_ = lean_ctor_get_uint8(v_a_5122_, sizeof(void*)*1);
if (v_hasUncomparable_5180_ == 0)
{
lean_object* v_max_x3f_5181_; 
v_max_x3f_5181_ = lean_ctor_get(v_a_5122_, 0);
lean_inc(v_max_x3f_5181_);
lean_dec(v_a_5122_);
if (lean_obj_tag(v_max_x3f_5181_) == 0)
{
lean_dec_ref_known(v___x_5063_, 4);
v___y_5066_ = v___y_5177_;
v___y_5067_ = v___y_5179_;
v___y_5068_ = v___y_5178_;
v___y_5069_ = v___y_5176_;
v___y_5070_ = v___y_5175_;
v___y_5071_ = v___y_5174_;
goto v___jp_5065_;
}
else
{
lean_object* v_val_5182_; uint8_t v___x_5183_; 
lean_dec(v_a_5061_);
lean_dec(v_a_5057_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
lean_dec(v___x_5034_);
lean_dec(v___x_5033_);
v_val_5182_ = lean_ctor_get(v_max_x3f_5181_, 0);
lean_inc(v_val_5182_);
lean_dec_ref_known(v_max_x3f_5181_, 1);
v___x_5183_ = 1;
if (v_noProp_5037_ == 0)
{
v___y_5127_ = v___x_5183_;
v_maxType_5128_ = v_val_5182_;
v___y_5129_ = v___y_5174_;
v___y_5130_ = v___y_5175_;
v___y_5131_ = v___y_5176_;
v___y_5132_ = v___y_5177_;
v___y_5133_ = v___y_5178_;
v___y_5134_ = v___y_5179_;
goto v___jp_5126_;
}
else
{
lean_object* v___x_5184_; lean_object* v___f_5185_; lean_object* v___x_5186_; 
v___x_5184_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0);
lean_inc(v_val_5182_);
v___f_5185_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5185_, 0, v_val_5182_);
lean_closure_set(v___f_5185_, 1, v___x_5184_);
v___x_5186_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v___f_5185_, v___x_5040_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; uint8_t v___x_5188_; 
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
lean_dec_ref_known(v___x_5186_, 1);
v___x_5188_ = lean_unbox(v_a_5187_);
lean_dec(v_a_5187_);
if (v___x_5188_ == 0)
{
v___y_5127_ = v___x_5183_;
v_maxType_5128_ = v_val_5182_;
v___y_5129_ = v___y_5174_;
v___y_5130_ = v___y_5175_;
v___y_5131_ = v___y_5176_;
v___y_5132_ = v___y_5177_;
v___y_5133_ = v___y_5178_;
v___y_5134_ = v___y_5179_;
goto v___jp_5126_;
}
else
{
lean_object* v___x_5189_; 
lean_dec(v_val_5182_);
v___x_5189_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3);
v___y_5127_ = v___x_5183_;
v_maxType_5128_ = v___x_5189_;
v___y_5129_ = v___y_5174_;
v___y_5130_ = v___y_5175_;
v___y_5131_ = v___y_5176_;
v___y_5132_ = v___y_5177_;
v___y_5133_ = v___y_5178_;
v___y_5134_ = v___y_5179_;
goto v___jp_5126_;
}
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
lean_dec(v_val_5182_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec(v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec_ref_known(v___x_5063_, 4);
v_a_5190_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5186_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5186_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5122_);
lean_dec_ref_known(v___x_5063_, 4);
v___y_5066_ = v___y_5177_;
v___y_5067_ = v___y_5179_;
v___y_5068_ = v___y_5178_;
v___y_5069_ = v___y_5176_;
v___y_5070_ = v___y_5175_;
v___y_5071_ = v___y_5174_;
goto v___jp_5065_;
}
}
v___jp_5198_:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5201_, 0, v___y_5199_);
lean_ctor_set(v___x_5201_, 1, v___y_5200_);
v___x_5202_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_5125_, v___x_5201_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_dec_ref_known(v___x_5202_, 1);
v___y_5174_ = v___y_5041_;
v___y_5175_ = v___y_5042_;
v___y_5176_ = v___y_5043_;
v___y_5177_ = v___y_5044_;
v___y_5178_ = v___y_5045_;
v___y_5179_ = v___y_5046_;
goto v___jp_5173_;
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
lean_dec(v_a_5122_);
lean_dec_ref_known(v___x_5063_, 4);
lean_dec(v_a_5061_);
lean_dec(v_a_5057_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
lean_dec(v___x_5034_);
lean_dec(v___x_5033_);
v_a_5203_ = lean_ctor_get(v___x_5202_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___x_5202_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5202_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5208_; 
if (v_isShared_5206_ == 0)
{
v___x_5208_ = v___x_5205_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_a_5203_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
}
else
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
lean_dec_ref_known(v___x_5063_, 4);
lean_dec(v_a_5061_);
lean_dec(v_a_5057_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
lean_dec(v___x_5034_);
lean_dec(v___x_5033_);
v_a_5239_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5120_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5120_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
v___jp_5065_:
{
lean_object* v___x_5072_; 
v___x_5072_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5057_, v___y_5071_, v___y_5070_, v___y_5069_, v___y_5066_, v___y_5068_, v___y_5067_);
if (lean_obj_tag(v___x_5072_) == 0)
{
lean_object* v_a_5073_; lean_object* v___x_5074_; 
v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
lean_inc(v_a_5073_);
lean_dec_ref_known(v___x_5072_, 1);
v___x_5074_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5061_, v___y_5071_, v___y_5070_, v___y_5069_, v___y_5066_, v___y_5068_, v___y_5067_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v_a_5075_; lean_object* v_toCold_5076_; lean_object* v_currRecDepth_5077_; lean_object* v_ref_5078_; uint16_t v_optionFlags_5079_; uint8_t v_suppressElabErrors_5080_; uint8_t v_isRecordingDeps_5081_; lean_object* v_ref_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
lean_inc(v_a_5075_);
lean_dec_ref_known(v___x_5074_, 1);
v_toCold_5076_ = lean_ctor_get(v___y_5068_, 0);
v_currRecDepth_5077_ = lean_ctor_get(v___y_5068_, 1);
v_ref_5078_ = lean_ctor_get(v___y_5068_, 2);
v_optionFlags_5079_ = lean_ctor_get_uint16(v___y_5068_, sizeof(void*)*3);
v_suppressElabErrors_5080_ = lean_ctor_get_uint8(v___y_5068_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5081_ = lean_ctor_get_uint8(v___y_5068_, sizeof(void*)*3 + 3);
v_ref_5082_ = l_Lean_replaceRef(v___x_5033_, v_ref_5078_);
lean_dec(v___x_5033_);
lean_inc(v_currRecDepth_5077_);
lean_inc_ref(v_toCold_5076_);
v___x_5083_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5083_, 0, v_toCold_5076_);
lean_ctor_set(v___x_5083_, 1, v_currRecDepth_5077_);
lean_ctor_set(v___x_5083_, 2, v_ref_5082_);
lean_ctor_set_uint16(v___x_5083_, sizeof(void*)*3, v_optionFlags_5079_);
lean_ctor_set_uint8(v___x_5083_, sizeof(void*)*3 + 2, v_suppressElabErrors_5080_);
lean_ctor_set_uint8(v___x_5083_, sizeof(void*)*3 + 3, v_isRecordingDeps_5081_);
v___x_5084_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_5037_, v_a_5073_, v___y_5071_, v___y_5070_, v___y_5069_, v___y_5066_, v___x_5083_, v___y_5067_);
lean_dec_ref_known(v___x_5083_, 3);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v_ref_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref_known(v___x_5084_, 1);
v_ref_5086_ = l_Lean_replaceRef(v___x_5034_, v_ref_5078_);
lean_dec(v___x_5034_);
lean_inc(v_currRecDepth_5077_);
lean_inc_ref(v_toCold_5076_);
v___x_5087_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5087_, 0, v_toCold_5076_);
lean_ctor_set(v___x_5087_, 1, v_currRecDepth_5077_);
lean_ctor_set(v___x_5087_, 2, v_ref_5086_);
lean_ctor_set_uint16(v___x_5087_, sizeof(void*)*3, v_optionFlags_5079_);
lean_ctor_set_uint8(v___x_5087_, sizeof(void*)*3 + 2, v_suppressElabErrors_5080_);
lean_ctor_set_uint8(v___x_5087_, sizeof(void*)*3 + 3, v_isRecordingDeps_5081_);
v___x_5088_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_5037_, v_a_5075_, v___y_5071_, v___y_5070_, v___y_5069_, v___y_5066_, v___x_5087_, v___y_5067_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5119_; 
v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5091_ = v___x_5088_;
v_isShared_5092_ = v_isSharedCheck_5119_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5088_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5119_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5093_; 
lean_inc(v___y_5067_);
lean_inc_ref(v___y_5068_);
lean_inc(v___y_5066_);
lean_inc_ref(v___y_5069_);
lean_inc(v_a_5085_);
v___x_5093_ = lean_infer_type(v_a_5085_, v___y_5069_, v___y_5066_, v___y_5068_, v___y_5067_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5118_; 
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5096_ = v___x_5093_;
v_isShared_5097_ = v_isSharedCheck_5118_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5093_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5118_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set_tag(v___x_5096_, 1);
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
lean_object* v___x_5100_; 
v___x_5100_ = l_Lean_Elab_Term_ensureHasType(v___x_5099_, v_a_5089_, v___x_5064_, v___x_5064_, v___y_5071_, v___y_5070_, v___y_5069_, v___y_5066_, v___x_5087_, v___y_5067_);
lean_dec_ref_known(v___x_5087_, 3);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5116_; 
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5103_ = v___x_5100_;
v_isShared_5104_ = v_isSharedCheck_5116_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5116_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5105_; lean_object* v___x_5107_; 
v___x_5105_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
if (v_isShared_5104_ == 0)
{
lean_ctor_set_tag(v___x_5103_, 1);
lean_ctor_set(v___x_5103_, 0, v_a_5085_);
v___x_5107_ = v___x_5103_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5085_);
v___x_5107_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
lean_object* v___x_5109_; 
if (v_isShared_5092_ == 0)
{
lean_ctor_set_tag(v___x_5091_, 1);
lean_ctor_set(v___x_5091_, 0, v_a_5101_);
v___x_5109_ = v___x_5091_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5101_);
v___x_5109_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v___x_5110_ = lean_mk_empty_array_with_capacity(v___x_5038_);
v___x_5111_ = lean_array_push(v___x_5110_, v___x_5107_);
v___x_5112_ = lean_array_push(v___x_5111_, v___x_5109_);
v___x_5113_ = l_Lean_Elab_Term_elabAppArgs(v_val_5036_, v___x_5105_, v___x_5112_, v_expectedType_x3f_5039_, v___x_5040_, v___x_5040_, v___x_5040_, v___y_5071_, v___y_5070_, v___y_5069_, v___y_5066_, v___y_5068_, v___y_5067_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5069_);
return v___x_5113_;
}
}
}
}
else
{
lean_del_object(v___x_5091_);
lean_dec(v_a_5085_);
lean_dec_ref(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
return v___x_5100_;
}
}
}
}
else
{
lean_del_object(v___x_5091_);
lean_dec(v_a_5089_);
lean_dec_ref_known(v___x_5087_, 3);
lean_dec(v_a_5085_);
lean_dec_ref(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
return v___x_5093_;
}
}
}
else
{
lean_dec_ref_known(v___x_5087_, 3);
lean_dec(v_a_5085_);
lean_dec_ref(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
return v___x_5088_;
}
}
else
{
lean_dec(v_a_5075_);
lean_dec_ref(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
lean_dec(v___x_5034_);
return v___x_5084_;
}
}
else
{
lean_dec(v_a_5073_);
lean_dec_ref(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
lean_dec(v___x_5034_);
lean_dec(v___x_5033_);
return v___x_5074_;
}
}
else
{
lean_dec_ref(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec(v_a_5061_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
lean_dec(v___x_5034_);
lean_dec(v___x_5033_);
return v___x_5072_;
}
}
}
else
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
lean_dec(v_a_5057_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
lean_dec(v_stx_5035_);
lean_dec(v___x_5034_);
lean_dec(v___x_5033_);
v_a_5247_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___x_5060_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5060_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5262_; 
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v_expectedType_x3f_5039_);
lean_dec_ref(v_val_5036_);
lean_dec(v_stx_5035_);
lean_dec(v___x_5034_);
lean_dec(v___x_5033_);
v_a_5255_ = lean_ctor_get(v___x_5056_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5257_ = v___x_5056_;
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5056_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5260_; 
if (v_isShared_5258_ == 0)
{
v___x_5260_ = v___x_5257_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
v___x_5260_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
return v___x_5260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___boxed(lean_object* v___x_5263_, lean_object* v___x_5264_, lean_object* v_stx_5265_, lean_object* v_val_5266_, lean_object* v_noProp_5267_, lean_object* v___x_5268_, lean_object* v_expectedType_x3f_5269_, lean_object* v___x_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
uint8_t v_noProp_boxed_5278_; uint8_t v___x_11288__boxed_5279_; lean_object* v_res_5280_; 
v_noProp_boxed_5278_ = lean_unbox(v_noProp_5267_);
v___x_11288__boxed_5279_ = lean_unbox(v___x_5270_);
v_res_5280_ = l_Lean_Elab_Term_Op_elabBinRelCore___lam__1(v___x_5263_, v___x_5264_, v_stx_5265_, v_val_5266_, v_noProp_boxed_5278_, v___x_5268_, v_expectedType_x3f_5269_, v___x_11288__boxed_5279_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec(v___x_5268_);
return v_res_5280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore(uint8_t v_noProp_5281_, lean_object* v_stx_5282_, lean_object* v_expectedType_x3f_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_){
_start:
{
lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; uint8_t v___x_5294_; lean_object* v___x_5295_; 
v___x_5291_ = lean_unsigned_to_nat(1u);
v___x_5292_ = l_Lean_Syntax_getArg(v_stx_5282_, v___x_5291_);
v___x_5293_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_5294_ = 0;
lean_inc(v___x_5292_);
v___x_5295_ = l_Lean_Elab_Term_resolveId_x3f(v___x_5292_, v___x_5293_, v___x_5294_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
lean_inc(v_a_5296_);
lean_dec_ref_known(v___x_5295_, 1);
if (lean_obj_tag(v_a_5296_) == 0)
{
lean_object* v___x_5297_; lean_object* v___x_5298_; 
lean_dec(v_expectedType_x3f_5283_);
lean_dec(v_stx_5282_);
v___x_5297_ = l_Lean_Syntax_getId(v___x_5292_);
v___x_5298_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v___x_5292_, v___x_5297_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
lean_dec(v___x_5292_);
return v___x_5298_;
}
else
{
lean_object* v_val_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___f_5306_; lean_object* v___x_5307_; 
lean_dec(v___x_5292_);
v_val_5299_ = lean_ctor_get(v_a_5296_, 0);
lean_inc(v_val_5299_);
lean_dec_ref_known(v_a_5296_, 1);
v___x_5300_ = lean_unsigned_to_nat(2u);
v___x_5301_ = l_Lean_Syntax_getArg(v_stx_5282_, v___x_5300_);
v___x_5302_ = lean_unsigned_to_nat(3u);
v___x_5303_ = l_Lean_Syntax_getArg(v_stx_5282_, v___x_5302_);
v___x_5304_ = lean_box(v_noProp_5281_);
v___x_5305_ = lean_box(v___x_5294_);
v___f_5306_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___boxed), 15, 8);
lean_closure_set(v___f_5306_, 0, v___x_5301_);
lean_closure_set(v___f_5306_, 1, v___x_5303_);
lean_closure_set(v___f_5306_, 2, v_stx_5282_);
lean_closure_set(v___f_5306_, 3, v_val_5299_);
lean_closure_set(v___f_5306_, 4, v___x_5304_);
lean_closure_set(v___f_5306_, 5, v___x_5300_);
lean_closure_set(v___f_5306_, 6, v_expectedType_x3f_5283_);
lean_closure_set(v___f_5306_, 7, v___x_5305_);
v___x_5307_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_box(0), v___f_5306_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
return v___x_5307_;
}
}
else
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
lean_dec(v___x_5292_);
lean_dec(v_expectedType_x3f_5283_);
lean_dec(v_stx_5282_);
v_a_5308_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5310_ = v___x_5295_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5295_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___boxed(lean_object* v_noProp_5316_, lean_object* v_stx_5317_, lean_object* v_expectedType_x3f_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_){
_start:
{
uint8_t v_noProp_boxed_5326_; lean_object* v_res_5327_; 
v_noProp_boxed_5326_ = lean_unbox(v_noProp_5316_);
v_res_5327_ = l_Lean_Elab_Term_Op_elabBinRelCore(v_noProp_boxed_5326_, v_stx_5317_, v_expectedType_x3f_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_);
lean_dec(v_a_5324_);
lean_dec_ref(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec_ref(v_a_5321_);
lean_dec(v_a_5320_);
lean_dec_ref(v_a_5319_);
return v_res_5327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel(lean_object* v_stx_5328_, lean_object* v_expectedType_x3f_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_){
_start:
{
uint8_t v___x_5337_; lean_object* v___x_5338_; 
v___x_5337_ = 0;
v___x_5338_ = l_Lean_Elab_Term_Op_elabBinRelCore(v___x_5337_, v_stx_5328_, v_expectedType_x3f_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel___boxed(lean_object* v_stx_5339_, lean_object* v_expectedType_x3f_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_){
_start:
{
lean_object* v_res_5348_; 
v_res_5348_ = l_Lean_Elab_Term_Op_elabBinRel(v_stx_5339_, v_expectedType_x3f_5340_, v_a_5341_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_);
lean_dec(v_a_5346_);
lean_dec_ref(v_a_5345_);
lean_dec(v_a_5344_);
lean_dec_ref(v_a_5343_);
lean_dec(v_a_5342_);
lean_dec_ref(v_a_5341_);
return v_res_5348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1(){
_start:
{
lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5362_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5363_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0));
v___x_5364_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2));
v___x_5365_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRel___boxed), 9, 0);
v___x_5366_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5362_, v___x_5363_, v___x_5364_, v___x_5365_);
return v___x_5366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___boxed(lean_object* v_a_5367_){
_start:
{
lean_object* v_res_5368_; 
v_res_5368_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1();
return v_res_5368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3(){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5395_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2));
v___x_5396_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__6));
v___x_5397_ = l_Lean_addBuiltinDeclarationRanges(v___x_5395_, v___x_5396_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___boxed(lean_object* v_a_5398_){
_start:
{
lean_object* v_res_5399_; 
v_res_5399_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3();
return v_res_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp(lean_object* v_stx_5400_, lean_object* v_expectedType_x3f_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_){
_start:
{
uint8_t v___x_5409_; lean_object* v___x_5410_; 
v___x_5409_ = 1;
v___x_5410_ = l_Lean_Elab_Term_Op_elabBinRelCore(v___x_5409_, v_stx_5400_, v_expectedType_x3f_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp___boxed(lean_object* v_stx_5411_, lean_object* v_expectedType_x3f_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_){
_start:
{
lean_object* v_res_5420_; 
v_res_5420_ = l_Lean_Elab_Term_Op_elabBinRelNoProp(v_stx_5411_, v_expectedType_x3f_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_);
lean_dec(v_a_5418_);
lean_dec_ref(v_a_5417_);
lean_dec(v_a_5416_);
lean_dec_ref(v_a_5415_);
lean_dec(v_a_5414_);
lean_dec_ref(v_a_5413_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1(){
_start:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
v___x_5435_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5436_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1));
v___x_5437_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3));
v___x_5438_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelNoProp___boxed), 9, 0);
v___x_5439_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5435_, v___x_5436_, v___x_5437_, v___x_5438_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___boxed(lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1();
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3(){
_start:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; 
v___x_5468_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3));
v___x_5469_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__6));
v___x_5470_ = l_Lean_addBuiltinDeclarationRanges(v___x_5468_, v___x_5469_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___boxed(lean_object* v_a_5471_){
_start:
{
lean_object* v_res_5472_; 
v_res_5472_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3();
return v_res_5472_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1(void){
_start:
{
lean_object* v___x_5474_; lean_object* v___x_5475_; 
v___x_5474_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__0));
v___x_5475_ = l_Lean_stringToMessageData(v___x_5474_);
return v___x_5475_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3(void){
_start:
{
lean_object* v___x_5477_; lean_object* v___x_5478_; 
v___x_5477_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__2));
v___x_5478_ = l_Lean_stringToMessageData(v___x_5477_);
return v___x_5478_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7(void){
_start:
{
lean_object* v___x_5483_; lean_object* v___x_5484_; 
v___x_5483_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__6));
v___x_5484_ = l_Lean_stringToMessageData(v___x_5483_);
return v___x_5484_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11(void){
_start:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5489_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__10));
v___x_5490_ = l_Lean_stringToMessageData(v___x_5489_);
return v___x_5490_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13(void){
_start:
{
lean_object* v___x_5492_; lean_object* v___x_5493_; 
v___x_5492_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__12));
v___x_5493_ = l_Lean_stringToMessageData(v___x_5492_);
return v___x_5493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty(lean_object* v_stx_5494_, lean_object* v_expectedType_x3f_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_){
_start:
{
lean_object* v___x_5503_; 
lean_inc(v_expectedType_x3f_5495_);
v___x_5503_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
if (lean_obj_tag(v___x_5503_) == 0)
{
lean_dec_ref_known(v___x_5503_, 1);
if (lean_obj_tag(v_expectedType_x3f_5495_) == 0)
{
lean_object* v___x_5504_; lean_object* v___x_5505_; 
v___x_5504_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1);
v___x_5505_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_5504_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
return v___x_5505_;
}
else
{
lean_object* v_val_5506_; lean_object* v___x_5507_; 
v_val_5506_ = lean_ctor_get(v_expectedType_x3f_5495_, 0);
lean_inc_n(v_val_5506_, 2);
lean_dec_ref_known(v_expectedType_x3f_5495_, 1);
v___x_5507_ = l_Lean_Meta_mkDefault(v_val_5506_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
if (lean_obj_tag(v___x_5507_) == 0)
{
lean_dec(v_val_5506_);
return v___x_5507_;
}
else
{
lean_object* v_a_5508_; uint8_t v___x_5509_; 
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
v___x_5509_ = l_Lean_Exception_isInterrupt(v_a_5508_);
if (v___x_5509_ == 0)
{
uint8_t v___x_5510_; 
lean_inc(v_a_5508_);
v___x_5510_ = l_Lean_Exception_isRuntime(v_a_5508_);
if (v___x_5510_ == 0)
{
lean_object* v___x_5511_; 
lean_dec_ref_known(v___x_5507_, 1);
lean_inc(v_val_5506_);
v___x_5511_ = l_Lean_Meta_mkOfNonempty(v_val_5506_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
if (lean_obj_tag(v___x_5511_) == 0)
{
lean_dec(v_val_5506_);
return v___x_5511_;
}
else
{
lean_object* v_a_5512_; uint8_t v___x_5513_; 
v_a_5512_ = lean_ctor_get(v___x_5511_, 0);
v___x_5513_ = l_Lean_Exception_isInterrupt(v_a_5512_);
if (v___x_5513_ == 0)
{
uint8_t v___x_5514_; 
lean_inc(v_a_5512_);
v___x_5514_ = l_Lean_Exception_isRuntime(v_a_5512_);
if (v___x_5514_ == 0)
{
lean_object* v___x_5515_; lean_object* v___x_5516_; uint8_t v___x_5517_; 
lean_dec_ref_known(v___x_5511_, 1);
v___x_5515_ = lean_unsigned_to_nat(1u);
v___x_5516_ = l_Lean_Syntax_getArg(v_stx_5494_, v___x_5515_);
v___x_5517_ = l_Lean_Syntax_isNone(v___x_5516_);
lean_dec(v___x_5516_);
if (v___x_5517_ == 0)
{
uint8_t v___x_5518_; lean_object* v___x_5519_; 
v___x_5518_ = 1;
v___x_5519_ = l_Lean_Meta_mkLabeledSorry(v_val_5506_, v___x_5517_, v___x_5518_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
return v___x_5519_;
}
else
{
lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; 
v___x_5520_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3);
v___x_5521_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__5));
v___x_5522_ = l_Lean_MessageData_ofConstName(v___x_5521_, v___x_5514_);
v___x_5523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5523_, 0, v___x_5520_);
lean_ctor_set(v___x_5523_, 1, v___x_5522_);
v___x_5524_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7);
v___x_5525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5525_, 0, v___x_5523_);
lean_ctor_set(v___x_5525_, 1, v___x_5524_);
v___x_5526_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__9));
v___x_5527_ = l_Lean_MessageData_ofConstName(v___x_5526_, v___x_5514_);
v___x_5528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5528_, 0, v___x_5525_);
lean_ctor_set(v___x_5528_, 1, v___x_5527_);
v___x_5529_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11);
v___x_5530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5530_, 0, v___x_5528_);
lean_ctor_set(v___x_5530_, 1, v___x_5529_);
v___x_5531_ = l_Lean_indentExpr(v_val_5506_);
v___x_5532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5530_);
lean_ctor_set(v___x_5532_, 1, v___x_5531_);
v___x_5533_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13);
v___x_5534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5534_, 0, v___x_5532_);
lean_ctor_set(v___x_5534_, 1, v___x_5533_);
v___x_5535_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_5534_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
return v___x_5535_;
}
}
else
{
lean_dec(v_val_5506_);
return v___x_5511_;
}
}
else
{
lean_dec(v_val_5506_);
return v___x_5511_;
}
}
}
else
{
lean_dec(v_val_5506_);
return v___x_5507_;
}
}
else
{
lean_dec(v_val_5506_);
return v___x_5507_;
}
}
}
}
else
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5543_; 
lean_dec(v_expectedType_x3f_5495_);
v_a_5536_ = lean_ctor_get(v___x_5503_, 0);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5503_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5538_ = v___x_5503_;
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5503_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___boxed(lean_object* v_stx_5544_, lean_object* v_expectedType_x3f_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_){
_start:
{
lean_object* v_res_5553_; 
v_res_5553_ = l_Lean_Elab_Term_Op_elabDefaultOrNonempty(v_stx_5544_, v_expectedType_x3f_5545_, v_a_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_);
lean_dec(v_a_5551_);
lean_dec_ref(v_a_5550_);
lean_dec(v_a_5549_);
lean_dec_ref(v_a_5548_);
lean_dec(v_a_5547_);
lean_dec_ref(v_a_5546_);
lean_dec(v_stx_5544_);
return v_res_5553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1(){
_start:
{
lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; 
v___x_5568_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5569_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1));
v___x_5570_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3));
v___x_5571_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___boxed), 9, 0);
v___x_5572_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5568_, v___x_5569_, v___x_5570_, v___x_5571_);
return v___x_5572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___boxed(lean_object* v_a_5573_){
_start:
{
lean_object* v_res_5574_; 
v_res_5574_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1();
return v_res_5574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3(){
_start:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; 
v___x_5601_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3));
v___x_5602_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__6));
v___x_5603_ = l_Lean_addBuiltinDeclarationRanges(v___x_5601_, v___x_5602_);
return v___x_5603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___boxed(lean_object* v_a_5604_){
_start:
{
lean_object* v_res_5605_; 
v_res_5605_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3();
return v_res_5605_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; 
v___x_5652_ = lean_unsigned_to_nat(2859506122u);
v___x_5653_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__17_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_5654_ = l_Lean_Name_num___override(v___x_5653_, v___x_5652_);
return v___x_5654_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; 
v___x_5656_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__19_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_5657_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5658_ = l_Lean_Name_str___override(v___x_5657_, v___x_5656_);
return v___x_5658_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; 
v___x_5660_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__21_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_5661_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5662_ = l_Lean_Name_str___override(v___x_5661_, v___x_5660_);
return v___x_5662_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; 
v___x_5663_ = lean_unsigned_to_nat(2u);
v___x_5664_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5665_ = l_Lean_Name_num___override(v___x_5664_, v___x_5663_);
return v___x_5665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5667_; uint8_t v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; 
v___x_5667_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_5668_ = 0;
v___x_5669_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5670_ = l_Lean_registerTraceClass(v___x_5667_, v___x_5668_, v___x_5669_);
if (lean_obj_tag(v___x_5670_) == 0)
{
lean_object* v___x_5671_; lean_object* v___x_5672_; 
lean_dec_ref_known(v___x_5670_, 1);
v___x_5671_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
v___x_5672_ = l_Lean_registerTraceClass(v___x_5671_, v___x_5668_, v___x_5669_);
return v___x_5672_;
}
else
{
return v___x_5670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2____boxed(lean_object* v_a_5673_){
_start:
{
lean_object* v_res_5674_; 
v_res_5674_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_();
return v_res_5674_;
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
