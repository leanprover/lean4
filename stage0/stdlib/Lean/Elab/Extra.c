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
lean_object* l_Lean_Elab_Term_withDeprecationContextForSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
uint8_t l_Lean_Elab_Term_hasCDot(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabListLitAux_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabListLitAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_elabListLitAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Term_elabListLitAux___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabListLitAux___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_elabListLitAux___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Term_elabListLitAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabListLitAux___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabListLitAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Elab_Term_elabListLitAux___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabListLitAux___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_elabListLitAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Elab_Term_elabListLitAux___closed__2 = (const lean_object*)&l_Lean_Elab_Term_elabListLitAux___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_elabListLitAux___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Term_elabListLitAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabListLitAux___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabListLitAux___closed__2_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Elab_Term_elabListLitAux___closed__3 = (const lean_object*)&l_Lean_Elab_Term_elabListLitAux___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabListLitAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabListLitAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "listTreeLit"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 194, 89, 43, 254, 92, 144, 135)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabListLitAux"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabForIn___regBuiltin_Lean_Elab_Term_elabForIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_elabForIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(59, 133, 140, 29, 244, 240, 116, 227)}};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0___redArg(lean_object* v_l_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; lean_object* v_mctx_798_; lean_object* v___x_799_; lean_object* v_fst_800_; lean_object* v_snd_801_; lean_object* v___x_802_; lean_object* v_cache_803_; lean_object* v_zetaDeltaFVarIds_804_; lean_object* v_postponed_805_; lean_object* v_diag_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_815_; 
v___x_797_ = lean_st_ref_get(v___y_795_);
v_mctx_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref(v_mctx_798_);
lean_dec(v___x_797_);
v___x_799_ = lean_instantiate_level_mvars(v_mctx_798_, v_l_794_);
v_fst_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_fst_800_);
v_snd_801_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_snd_801_);
lean_dec_ref(v___x_799_);
v___x_802_ = lean_st_ref_take(v___y_795_);
v_cache_803_ = lean_ctor_get(v___x_802_, 1);
v_zetaDeltaFVarIds_804_ = lean_ctor_get(v___x_802_, 2);
v_postponed_805_ = lean_ctor_get(v___x_802_, 3);
v_diag_806_ = lean_ctor_get(v___x_802_, 4);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_816_);
v___x_808_ = v___x_802_;
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_diag_806_);
lean_inc(v_postponed_805_);
lean_inc(v_zetaDeltaFVarIds_804_);
lean_inc(v_cache_803_);
lean_dec(v___x_802_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v_fst_800_);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_fst_800_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_cache_803_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_zetaDeltaFVarIds_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_postponed_805_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_diag_806_);
v___x_811_ = v_reuseFailAlloc_814_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_st_ref_put(v___y_795_, v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v_snd_801_);
return v___x_813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0___redArg___boxed(lean_object* v_l_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0___redArg(v_l_817_, v___y_818_);
lean_dec(v___y_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0(lean_object* v_l_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0___redArg(v_l_821_, v___y_825_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0___boxed(lean_object* v_l_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0(v_l_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(lean_object* v_e_839_, lean_object* v___y_840_){
_start:
{
uint8_t v___x_842_; 
v___x_842_ = l_Lean_Expr_hasMVar(v_e_839_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v_e_839_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; lean_object* v_mctx_845_; lean_object* v___x_846_; lean_object* v_fst_847_; lean_object* v_snd_848_; lean_object* v___x_849_; lean_object* v_cache_850_; lean_object* v_zetaDeltaFVarIds_851_; lean_object* v_postponed_852_; lean_object* v_diag_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_862_; 
v___x_844_ = lean_st_ref_get(v___y_840_);
v_mctx_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc_ref(v_mctx_845_);
lean_dec(v___x_844_);
v___x_846_ = l_Lean_instantiateMVarsCore(v_mctx_845_, v_e_839_);
v_fst_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_fst_847_);
v_snd_848_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_snd_848_);
lean_dec_ref(v___x_846_);
v___x_849_ = lean_st_ref_take(v___y_840_);
v_cache_850_ = lean_ctor_get(v___x_849_, 1);
v_zetaDeltaFVarIds_851_ = lean_ctor_get(v___x_849_, 2);
v_postponed_852_ = lean_ctor_get(v___x_849_, 3);
v_diag_853_ = lean_ctor_get(v___x_849_, 4);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; 
v_unused_863_ = lean_ctor_get(v___x_849_, 0);
lean_dec(v_unused_863_);
v___x_855_ = v___x_849_;
v_isShared_856_ = v_isSharedCheck_862_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_diag_853_);
lean_inc(v_postponed_852_);
lean_inc(v_zetaDeltaFVarIds_851_);
lean_inc(v_cache_850_);
lean_dec(v___x_849_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_862_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_snd_848_);
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_snd_848_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_cache_850_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_zetaDeltaFVarIds_851_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_postponed_852_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_diag_853_);
v___x_858_ = v_reuseFailAlloc_861_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_st_ref_put(v___y_840_, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v_fst_847_);
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg___boxed(lean_object* v_e_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(v_e_864_, v___y_865_);
lean_dec(v___y_865_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1(lean_object* v_e_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(v_e_868_, v___y_872_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___boxed(lean_object* v_e_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1(v_e_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo(lean_object* v_expectedType_x3f_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_u_898_; lean_object* v_00_u03b1_899_; lean_object* v_listType_900_; lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_mkFreshLevelMVar(v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc_n(v_a_905_, 2);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = l_Lean_Level_succ___override(v_a_905_);
v___x_907_ = l_Lean_mkSort(v___x_906_);
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
v___x_909_ = 0;
v___x_910_ = lean_box(0);
v___x_911_ = l_Lean_Meta_mkFreshExprMVar(v___x_908_, v___x_909_, v___x_910_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_n(v_a_912_, 2);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___closed__1));
v___x_914_ = lean_box(0);
lean_inc(v_a_905_);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v_a_905_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_mkConst(v___x_913_, v___x_915_);
v___x_917_ = l_Lean_Expr_app___override(v___x_916_, v_a_912_);
if (lean_obj_tag(v_expectedType_x3f_889_) == 1)
{
lean_object* v_val_918_; lean_object* v___x_919_; 
v_val_918_ = lean_ctor_get(v_expectedType_x3f_889_, 0);
lean_inc(v_val_918_);
lean_dec_ref_known(v_expectedType_x3f_889_, 1);
lean_inc_ref(v___x_917_);
v___x_919_ = l_Lean_Meta_isExprDefEq(v_val_918_, v___x_917_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v___x_920_; lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v_a_923_; lean_object* v___x_924_; lean_object* v_a_925_; 
lean_dec_ref_known(v___x_919_, 1);
v___x_920_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__0___redArg(v_a_905_, v_a_893_);
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref(v___x_920_);
v___x_922_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(v_a_912_, v_a_893_);
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v___x_922_);
v___x_924_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(v___x_917_, v_a_893_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref(v___x_924_);
v_u_898_ = v_a_921_;
v_00_u03b1_899_ = v_a_923_;
v_listType_900_ = v_a_925_;
goto v___jp_897_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v___x_917_);
lean_dec(v_a_912_);
lean_dec(v_a_905_);
v_a_926_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_919_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_919_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_889_);
v_u_898_ = v_a_905_;
v_00_u03b1_899_ = v_a_912_;
v_listType_900_ = v___x_917_;
goto v___jp_897_;
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_a_905_);
lean_dec(v_expectedType_x3f_889_);
v_a_934_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_911_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_911_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_expectedType_x3f_889_);
v_a_942_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_904_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_904_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
v___jp_897_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_00_u03b1_899_);
lean_ctor_set(v___x_901_, 1, v_listType_900_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_u_898_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo___boxed(lean_object* v_expectedType_x3f_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo(v_expectedType_x3f_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree_spec__0(lean_object* v_cons_959_, lean_object* v_as_960_, size_t v_i_961_, size_t v_stop_962_, lean_object* v_b_963_){
_start:
{
uint8_t v___x_964_; 
v___x_964_ = lean_usize_dec_eq(v_i_961_, v_stop_962_);
if (v___x_964_ == 0)
{
size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_sub(v_i_961_, v___x_965_);
v___x_967_ = lean_array_uget_borrowed(v_as_960_, v___x_966_);
lean_inc(v___x_967_);
lean_inc_ref(v_cons_959_);
v___x_968_ = l_Lean_mkAppB(v_cons_959_, v___x_967_, v_b_963_);
v_i_961_ = v___x_966_;
v_b_963_ = v___x_968_;
goto _start;
}
else
{
lean_dec_ref(v_cons_959_);
return v_b_963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree_spec__0___boxed(lean_object* v_cons_970_, lean_object* v_as_971_, lean_object* v_i_972_, lean_object* v_stop_973_, lean_object* v_b_974_){
_start:
{
size_t v_i_boxed_975_; size_t v_stop_boxed_976_; lean_object* v_res_977_; 
v_i_boxed_975_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_stop_boxed_976_ = lean_unbox_usize(v_stop_973_);
lean_dec(v_stop_973_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree_spec__0(v_cons_970_, v_as_971_, v_i_boxed_975_, v_stop_boxed_976_, v_b_974_);
lean_dec_ref(v_as_971_);
return v_res_977_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__2(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = l_Lean_Expr_bvar___override(v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree(lean_object* v_cons_983_, lean_object* v_listType_984_, lean_object* v_elems_985_, lean_object* v_lo_986_, lean_object* v_hi_987_, lean_object* v_tail_988_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_989_ = lean_nat_sub(v_hi_987_, v_lo_986_);
v___x_990_ = lean_unsigned_to_nat(8u);
v___x_991_ = lean_nat_dec_lt(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_mid_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_nat_shiftr(v___x_989_, v___x_992_);
lean_dec(v___x_989_);
v_mid_994_ = lean_nat_add(v_lo_986_, v___x_993_);
lean_dec(v___x_993_);
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__1));
lean_inc_ref_n(v_listType_984_, 2);
lean_inc_ref(v_cons_983_);
v___x_996_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree(v_cons_983_, v_listType_984_, v_elems_985_, v_mid_994_, v_hi_987_, v_tail_988_);
v___x_997_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__2, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__2_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__2);
v___x_998_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree(v_cons_983_, v_listType_984_, v_elems_985_, v_lo_986_, v_mid_994_, v___x_997_);
lean_dec(v_mid_994_);
v___x_999_ = l_Lean_Expr_letE___override(v___x_995_, v_listType_984_, v___x_996_, v___x_998_, v___x_991_);
return v___x_999_;
}
else
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
lean_dec(v___x_989_);
lean_dec_ref(v_listType_984_);
v___x_1000_ = lean_array_get_size(v_elems_985_);
v___x_1001_ = lean_nat_dec_le(v_hi_987_, v___x_1000_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_nat_dec_lt(v_lo_986_, v___x_1000_);
if (v___x_1002_ == 0)
{
lean_dec_ref(v_cons_983_);
return v_tail_988_;
}
else
{
size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_usize_of_nat(v___x_1000_);
v___x_1004_ = lean_usize_of_nat(v_lo_986_);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree_spec__0(v_cons_983_, v_elems_985_, v___x_1003_, v___x_1004_, v_tail_988_);
return v___x_1005_;
}
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_nat_dec_lt(v_lo_986_, v_hi_987_);
if (v___x_1006_ == 0)
{
lean_dec_ref(v_cons_983_);
return v_tail_988_;
}
else
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_usize_of_nat(v_hi_987_);
v___x_1008_ = lean_usize_of_nat(v_lo_986_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree_spec__0(v_cons_983_, v_elems_985_, v___x_1007_, v___x_1008_, v_tail_988_);
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___boxed(lean_object* v_cons_1010_, lean_object* v_listType_1011_, lean_object* v_elems_1012_, lean_object* v_lo_1013_, lean_object* v_hi_1014_, lean_object* v_tail_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree(v_cons_1010_, v_listType_1011_, v_elems_1012_, v_lo_1013_, v_hi_1014_, v_tail_1015_);
lean_dec(v_hi_1014_);
lean_dec(v_lo_1013_);
lean_dec_ref(v_elems_1012_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabListLitAux_spec__0(lean_object* v_fst_1017_, size_t v_sz_1018_, size_t v_i_1019_, lean_object* v_bs_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
uint8_t v___x_1028_; 
v___x_1028_ = lean_usize_dec_lt(v_i_1019_, v_sz_1018_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_dec_ref(v_fst_1017_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_bs_1020_);
return v___x_1029_;
}
else
{
lean_object* v_v_1030_; lean_object* v___x_1031_; lean_object* v_bs_x27_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_v_1030_ = lean_array_uget(v_bs_1020_, v_i_1019_);
v___x_1031_ = lean_unsigned_to_nat(0u);
v_bs_x27_1032_ = lean_array_uset(v_bs_1020_, v_i_1019_, v___x_1031_);
lean_inc_ref(v_fst_1017_);
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_fst_1017_);
v___x_1034_ = lean_box(0);
v___x_1035_ = l_Lean_Elab_Term_elabTermEnsuringType(v_v_1030_, v___x_1033_, v___x_1028_, v___x_1028_, v___x_1034_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_add(v_i_1019_, v___x_1037_);
v___x_1039_ = lean_array_uset(v_bs_x27_1032_, v_i_1019_, v_a_1036_);
v_i_1019_ = v___x_1038_;
v_bs_1020_ = v___x_1039_;
goto _start;
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec_ref(v_bs_x27_1032_);
lean_dec_ref(v_fst_1017_);
v_a_1041_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1035_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1035_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabListLitAux_spec__0___boxed(lean_object* v_fst_1049_, lean_object* v_sz_1050_, lean_object* v_i_1051_, lean_object* v_bs_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
size_t v_sz_boxed_1060_; size_t v_i_boxed_1061_; lean_object* v_res_1062_; 
v_sz_boxed_1060_ = lean_unbox_usize(v_sz_1050_);
lean_dec(v_sz_1050_);
v_i_boxed_1061_ = lean_unbox_usize(v_i_1051_);
lean_dec(v_i_1051_);
v_res_1062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabListLitAux_spec__0(v_fst_1049_, v_sz_boxed_1060_, v_i_boxed_1061_, v_bs_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabListLitAux(lean_object* v_stx_1071_, lean_object* v_expectedType_x3f_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v_elemStxs_1082_; lean_object* v___x_1083_; 
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = l_Lean_Syntax_getArg(v_stx_1071_, v___x_1080_);
v_elemStxs_1082_ = l_Lean_Syntax_getSepArgs(v___x_1081_);
lean_dec(v___x_1081_);
v___x_1083_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo(v_expectedType_x3f_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v_snd_1085_; lean_object* v_fst_1086_; lean_object* v_fst_1087_; lean_object* v_snd_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1124_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v_snd_1085_ = lean_ctor_get(v_a_1084_, 1);
lean_inc(v_snd_1085_);
v_fst_1086_ = lean_ctor_get(v_a_1084_, 0);
lean_inc(v_fst_1086_);
lean_dec(v_a_1084_);
v_fst_1087_ = lean_ctor_get(v_snd_1085_, 0);
v_snd_1088_ = lean_ctor_get(v_snd_1085_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_snd_1085_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1090_ = v_snd_1085_;
v_isShared_1091_ = v_isSharedCheck_1124_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_snd_1088_);
lean_inc(v_fst_1087_);
lean_dec(v_snd_1085_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1124_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1092_ = ((lean_object*)(l_Lean_Elab_Term_elabListLitAux___closed__1));
v___x_1093_ = lean_box(0);
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 1);
lean_ctor_set(v___x_1090_, 1, v___x_1093_);
lean_ctor_set(v___x_1090_, 0, v_fst_1086_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_fst_1086_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; size_t v_sz_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
lean_inc_ref(v___x_1095_);
v___x_1096_ = l_Lean_mkConst(v___x_1092_, v___x_1095_);
lean_inc_n(v_fst_1087_, 2);
v___x_1097_ = l_Lean_Expr_app___override(v___x_1096_, v_fst_1087_);
v___x_1098_ = ((lean_object*)(l_Lean_Elab_Term_elabListLitAux___closed__3));
v___x_1099_ = l_Lean_mkConst(v___x_1098_, v___x_1095_);
v___x_1100_ = l_Lean_Expr_app___override(v___x_1099_, v_fst_1087_);
v_sz_1101_ = lean_array_size(v_elemStxs_1082_);
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabListLitAux_spec__0(v_fst_1087_, v_sz_1101_, v___x_1102_, v_elemStxs_1082_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1114_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_array_get_size(v_a_1104_);
v___x_1110_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree(v___x_1100_, v_snd_1088_, v_a_1104_, v___x_1108_, v___x_1109_, v___x_1097_);
lean_dec(v_a_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1110_);
v___x_1112_ = v___x_1106_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v___x_1100_);
lean_dec_ref(v___x_1097_);
lean_dec(v_snd_1088_);
v_a_1115_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1103_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1103_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v_elemStxs_1082_);
v_a_1125_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1083_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1083_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabListLitAux___boxed(lean_object* v_stx_1133_, lean_object* v_expectedType_x3f_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Elab_Term_elabListLitAux(v_stx_1133_, v_expectedType_x3f_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_stx_1133_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1(){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1153_ = l_Lean_Elab_Term_termElabAttribute;
v___x_1154_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__1));
v___x_1155_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___closed__3));
v___x_1156_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabListLitAux___boxed), 9, 0);
v___x_1157_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1153_, v___x_1154_, v___x_1155_, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1___boxed(lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1();
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorIdx___impl(uint8_t v_x_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_box(v_x_1160_);
v___x_1162_ = lean_obj_tag_nat(v___x_1161_);
lean_dec(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorIdx___impl___boxed(lean_object* v_x_1163_){
_start:
{
uint8_t v_x_4__boxed_1164_; lean_object* v_res_1165_; 
v_x_4__boxed_1164_ = lean_unbox(v_x_1163_);
v_res_1165_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorIdx___impl(v_x_4__boxed_1164_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___redArg(lean_object* v_k_1166_){
_start:
{
lean_inc(v_k_1166_);
return v_k_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___redArg___boxed(lean_object* v_k_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___redArg(v_k_1167_);
lean_dec(v_k_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim(lean_object* v_motive_1169_, lean_object* v_ctorIdx_1170_, uint8_t v_t_1171_, lean_object* v_h_1172_, lean_object* v_k_1173_){
_start:
{
lean_inc(v_k_1173_);
return v_k_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim___boxed(lean_object* v_motive_1174_, lean_object* v_ctorIdx_1175_, lean_object* v_t_1176_, lean_object* v_h_1177_, lean_object* v_k_1178_){
_start:
{
uint8_t v_t_boxed_1179_; lean_object* v_res_1180_; 
v_t_boxed_1179_ = lean_unbox(v_t_1176_);
v_res_1180_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_ctorElim(v_motive_1174_, v_ctorIdx_1175_, v_t_boxed_1179_, v_h_1177_, v_k_1178_);
lean_dec(v_k_1178_);
lean_dec(v_ctorIdx_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___redArg(lean_object* v_regular_1181_){
_start:
{
lean_inc(v_regular_1181_);
return v_regular_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___redArg___boxed(lean_object* v_regular_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___redArg(v_regular_1182_);
lean_dec(v_regular_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim(lean_object* v_motive_1184_, uint8_t v_t_1185_, lean_object* v_h_1186_, lean_object* v_regular_1187_){
_start:
{
lean_inc(v_regular_1187_);
return v_regular_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim___boxed(lean_object* v_motive_1188_, lean_object* v_t_1189_, lean_object* v_h_1190_, lean_object* v_regular_1191_){
_start:
{
uint8_t v_t_boxed_1192_; lean_object* v_res_1193_; 
v_t_boxed_1192_ = lean_unbox(v_t_1189_);
v_res_1193_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_regular_elim(v_motive_1188_, v_t_boxed_1192_, v_h_1190_, v_regular_1191_);
lean_dec(v_regular_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___redArg(lean_object* v_lazy_1194_){
_start:
{
lean_inc(v_lazy_1194_);
return v_lazy_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___redArg___boxed(lean_object* v_lazy_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___redArg(v_lazy_1195_);
lean_dec(v_lazy_1195_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim(lean_object* v_motive_1197_, uint8_t v_t_1198_, lean_object* v_h_1199_, lean_object* v_lazy_1200_){
_start:
{
lean_inc(v_lazy_1200_);
return v_lazy_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim___boxed(lean_object* v_motive_1201_, lean_object* v_t_1202_, lean_object* v_h_1203_, lean_object* v_lazy_1204_){
_start:
{
uint8_t v_t_boxed_1205_; lean_object* v_res_1206_; 
v_t_boxed_1205_ = lean_unbox(v_t_1202_);
v_res_1206_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_lazy_elim(v_motive_1201_, v_t_boxed_1205_, v_h_1203_, v_lazy_1204_);
lean_dec(v_lazy_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___redArg(lean_object* v_leftact_1207_){
_start:
{
lean_inc(v_leftact_1207_);
return v_leftact_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___redArg___boxed(lean_object* v_leftact_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___redArg(v_leftact_1208_);
lean_dec(v_leftact_1208_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim(lean_object* v_motive_1210_, uint8_t v_t_1211_, lean_object* v_h_1212_, lean_object* v_leftact_1213_){
_start:
{
lean_inc(v_leftact_1213_);
return v_leftact_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim___boxed(lean_object* v_motive_1214_, lean_object* v_t_1215_, lean_object* v_h_1216_, lean_object* v_leftact_1217_){
_start:
{
uint8_t v_t_boxed_1218_; lean_object* v_res_1219_; 
v_t_boxed_1218_ = lean_unbox(v_t_1215_);
v_res_1219_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_leftact_elim(v_motive_1214_, v_t_boxed_1218_, v_h_1216_, v_leftact_1217_);
lean_dec(v_leftact_1217_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___redArg(lean_object* v_rightact_1220_){
_start:
{
lean_inc(v_rightact_1220_);
return v_rightact_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___redArg___boxed(lean_object* v_rightact_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___redArg(v_rightact_1221_);
lean_dec(v_rightact_1221_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim(lean_object* v_motive_1223_, uint8_t v_t_1224_, lean_object* v_h_1225_, lean_object* v_rightact_1226_){
_start:
{
lean_inc(v_rightact_1226_);
return v_rightact_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim___boxed(lean_object* v_motive_1227_, lean_object* v_t_1228_, lean_object* v_h_1229_, lean_object* v_rightact_1230_){
_start:
{
uint8_t v_t_boxed_1231_; lean_object* v_res_1232_; 
v_t_boxed_1231_ = lean_unbox(v_t_1228_);
v_res_1232_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_BinOpKind_rightact_elim(v_motive_1227_, v_t_boxed_1231_, v_h_1229_, v_rightact_1230_);
lean_dec(v_rightact_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(uint8_t v_x_1233_, uint8_t v_y_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1235_ = lean_box(v_x_1233_);
v___x_1236_ = lean_obj_tag_nat(v___x_1235_);
lean_dec(v___x_1235_);
v___x_1237_ = lean_box(v_y_1234_);
v___x_1238_ = lean_obj_tag_nat(v___x_1237_);
lean_dec(v___x_1237_);
v___x_1239_ = lean_nat_dec_eq(v___x_1236_, v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq___boxed(lean_object* v_x_1240_, lean_object* v_y_1241_){
_start:
{
uint8_t v_x_24__boxed_1242_; uint8_t v_y_25__boxed_1243_; uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_x_24__boxed_1242_ = lean_unbox(v_x_1240_);
v_y_25__boxed_1243_ = lean_unbox(v_y_1241_);
v_res_1244_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_x_24__boxed_1242_, v_y_25__boxed_1243_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorIdx___impl(lean_object* v_x_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_obj_tag_nat(v_x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorIdx___impl___boxed(lean_object* v_x_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorIdx___impl(v_x_1250_);
lean_dec_ref(v_x_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(lean_object* v_t_1252_, lean_object* v_k_1253_){
_start:
{
switch(lean_obj_tag(v_t_1252_))
{
case 1:
{
lean_object* v_ref_1254_; uint8_t v_kind_1255_; lean_object* v_f_1256_; lean_object* v_lhs_1257_; lean_object* v_rhs_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_ref_1254_ = lean_ctor_get(v_t_1252_, 0);
lean_inc(v_ref_1254_);
v_kind_1255_ = lean_ctor_get_uint8(v_t_1252_, sizeof(void*)*4);
v_f_1256_ = lean_ctor_get(v_t_1252_, 1);
lean_inc_ref(v_f_1256_);
v_lhs_1257_ = lean_ctor_get(v_t_1252_, 2);
lean_inc_ref(v_lhs_1257_);
v_rhs_1258_ = lean_ctor_get(v_t_1252_, 3);
lean_inc_ref(v_rhs_1258_);
lean_dec_ref_known(v_t_1252_, 4);
v___x_1259_ = lean_box(v_kind_1255_);
v___x_1260_ = lean_apply_5(v_k_1253_, v_ref_1254_, v___x_1259_, v_f_1256_, v_lhs_1257_, v_rhs_1258_);
return v___x_1260_;
}
case 3:
{
lean_object* v_macroName_1261_; lean_object* v_stx_1262_; lean_object* v_stx_x27_1263_; lean_object* v_nested_1264_; lean_object* v___x_1265_; 
v_macroName_1261_ = lean_ctor_get(v_t_1252_, 0);
lean_inc(v_macroName_1261_);
v_stx_1262_ = lean_ctor_get(v_t_1252_, 1);
lean_inc(v_stx_1262_);
v_stx_x27_1263_ = lean_ctor_get(v_t_1252_, 2);
lean_inc(v_stx_x27_1263_);
v_nested_1264_ = lean_ctor_get(v_t_1252_, 3);
lean_inc_ref(v_nested_1264_);
lean_dec_ref_known(v_t_1252_, 4);
v___x_1265_ = lean_apply_4(v_k_1253_, v_macroName_1261_, v_stx_1262_, v_stx_x27_1263_, v_nested_1264_);
return v___x_1265_;
}
default: 
{
lean_object* v_ref_1266_; lean_object* v_infoTrees_1267_; lean_object* v_val_1268_; lean_object* v___x_1269_; 
v_ref_1266_ = lean_ctor_get(v_t_1252_, 0);
lean_inc(v_ref_1266_);
v_infoTrees_1267_ = lean_ctor_get(v_t_1252_, 1);
lean_inc_ref(v_infoTrees_1267_);
v_val_1268_ = lean_ctor_get(v_t_1252_, 2);
lean_inc_ref(v_val_1268_);
lean_dec_ref(v_t_1252_);
v___x_1269_ = lean_apply_3(v_k_1253_, v_ref_1266_, v_infoTrees_1267_, v_val_1268_);
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim(lean_object* v_motive_1270_, lean_object* v_ctorIdx_1271_, lean_object* v_t_1272_, lean_object* v_h_1273_, lean_object* v_k_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_1272_, v_k_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___boxed(lean_object* v_motive_1276_, lean_object* v_ctorIdx_1277_, lean_object* v_t_1278_, lean_object* v_h_1279_, lean_object* v_k_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim(v_motive_1276_, v_ctorIdx_1277_, v_t_1278_, v_h_1279_, v_k_1280_);
lean_dec(v_ctorIdx_1277_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_term_elim___redArg(lean_object* v_t_1282_, lean_object* v_term_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_1282_, v_term_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_term_elim(lean_object* v_motive_1285_, lean_object* v_t_1286_, lean_object* v_h_1287_, lean_object* v_term_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_1286_, v_term_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_binop_elim___redArg(lean_object* v_t_1290_, lean_object* v_binop_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_1290_, v_binop_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_binop_elim(lean_object* v_motive_1293_, lean_object* v_t_1294_, lean_object* v_h_1295_, lean_object* v_binop_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_1294_, v_binop_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_unop_elim___redArg(lean_object* v_t_1298_, lean_object* v_unop_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_1298_, v_unop_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_unop_elim(lean_object* v_motive_1301_, lean_object* v_t_1302_, lean_object* v_h_1303_, lean_object* v_unop_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_1302_, v_unop_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_macroExpansion_elim___redArg(lean_object* v_t_1306_, lean_object* v_macroExpansion_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_1306_, v_macroExpansion_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_macroExpansion_elim(lean_object* v_motive_1309_, lean_object* v_t_1310_, lean_object* v_h_1311_, lean_object* v_macroExpansion_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_Tree_ctorElim___redArg(v_t_1310_, v_macroExpansion_1312_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = lean_unsigned_to_nat(32u);
v___x_1315_ = lean_mk_empty_array_with_capacity(v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1317_ = ((size_t)5ULL);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = lean_unsigned_to_nat(32u);
v___x_1320_ = lean_mk_empty_array_with_capacity(v___x_1319_);
v___x_1321_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__0);
v___x_1322_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v___x_1320_);
lean_ctor_set(v___x_1322_, 2, v___x_1318_);
lean_ctor_set(v___x_1322_, 3, v___x_1318_);
lean_ctor_set_usize(v___x_1322_, 4, v___x_1317_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; lean_object* v_infoState_1326_; lean_object* v_trees_1327_; lean_object* v___x_1328_; lean_object* v_infoState_1329_; lean_object* v_env_1330_; lean_object* v_nextMacroScope_1331_; lean_object* v_ngen_1332_; lean_object* v_auxDeclNGen_1333_; lean_object* v_traceState_1334_; lean_object* v_cache_1335_; lean_object* v_recordedDeps_1336_; lean_object* v_messages_1337_; lean_object* v_snapshotTasks_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1359_; 
v___x_1325_ = lean_st_ref_get(v___y_1323_);
v_infoState_1326_ = lean_ctor_get(v___x_1325_, 8);
lean_inc_ref(v_infoState_1326_);
lean_dec(v___x_1325_);
v_trees_1327_ = lean_ctor_get(v_infoState_1326_, 2);
lean_inc_ref(v_trees_1327_);
lean_dec_ref(v_infoState_1326_);
v___x_1328_ = lean_st_ref_take(v___y_1323_);
v_infoState_1329_ = lean_ctor_get(v___x_1328_, 8);
v_env_1330_ = lean_ctor_get(v___x_1328_, 0);
v_nextMacroScope_1331_ = lean_ctor_get(v___x_1328_, 1);
v_ngen_1332_ = lean_ctor_get(v___x_1328_, 2);
v_auxDeclNGen_1333_ = lean_ctor_get(v___x_1328_, 3);
v_traceState_1334_ = lean_ctor_get(v___x_1328_, 4);
v_cache_1335_ = lean_ctor_get(v___x_1328_, 5);
v_recordedDeps_1336_ = lean_ctor_get(v___x_1328_, 6);
v_messages_1337_ = lean_ctor_get(v___x_1328_, 7);
v_snapshotTasks_1338_ = lean_ctor_get(v___x_1328_, 9);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1340_ = v___x_1328_;
v_isShared_1341_ = v_isSharedCheck_1359_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_snapshotTasks_1338_);
lean_inc(v_infoState_1329_);
lean_inc(v_messages_1337_);
lean_inc(v_recordedDeps_1336_);
lean_inc(v_cache_1335_);
lean_inc(v_traceState_1334_);
lean_inc(v_auxDeclNGen_1333_);
lean_inc(v_ngen_1332_);
lean_inc(v_nextMacroScope_1331_);
lean_inc(v_env_1330_);
lean_dec(v___x_1328_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1359_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
uint8_t v_enabled_1342_; lean_object* v_assignment_1343_; lean_object* v_lazyAssignment_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1357_; 
v_enabled_1342_ = lean_ctor_get_uint8(v_infoState_1329_, sizeof(void*)*3);
v_assignment_1343_ = lean_ctor_get(v_infoState_1329_, 0);
v_lazyAssignment_1344_ = lean_ctor_get(v_infoState_1329_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_infoState_1329_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v_infoState_1329_, 2);
lean_dec(v_unused_1358_);
v___x_1346_ = v_infoState_1329_;
v_isShared_1347_ = v_isSharedCheck_1357_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_lazyAssignment_1344_);
lean_inc(v_assignment_1343_);
lean_dec(v_infoState_1329_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1357_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___closed__1);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 2, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_assignment_1343_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_lazyAssignment_1344_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v___x_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1356_, sizeof(void*)*3, v_enabled_1342_);
v___x_1350_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 8, v___x_1350_);
v___x_1352_ = v___x_1340_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_env_1330_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_nextMacroScope_1331_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_ngen_1332_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_auxDeclNGen_1333_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v_traceState_1334_);
lean_ctor_set(v_reuseFailAlloc_1355_, 5, v_cache_1335_);
lean_ctor_set(v_reuseFailAlloc_1355_, 6, v_recordedDeps_1336_);
lean_ctor_set(v_reuseFailAlloc_1355_, 7, v_messages_1337_);
lean_ctor_set(v_reuseFailAlloc_1355_, 8, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1355_, 9, v_snapshotTasks_1338_);
v___x_1352_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_st_ref_put(v___y_1323_, v___x_1352_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_trees_1327_);
return v___x_1354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg___boxed(lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v___y_1360_);
lean_dec(v___y_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0(lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v___y_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___boxed(lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0(v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(lean_object* v_s_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = 1;
lean_inc(v_s_1379_);
v___x_1389_ = l_Lean_Elab_Term_elabTerm(v_s_1379_, v___x_1387_, v___x_1388_, v___x_1388_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v_a_1385_);
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1396_, 0, v_s_1379_);
lean_ctor_set(v___x_1396_, 1, v_a_1392_);
lean_ctor_set(v___x_1396_, 2, v_a_1390_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec(v_s_1379_);
v_a_1401_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1389_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1389_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf___boxed(lean_object* v_s_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(lean_object* v_beforeStx_1418_, lean_object* v_afterStx_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_declName_x3f_1428_; lean_object* v_macroStack_1429_; uint8_t v_mayPostpone_1430_; uint8_t v_errToSorry_1431_; lean_object* v_autoBoundImplicitContext_1432_; lean_object* v_autoBoundImplicitForbidden_1433_; lean_object* v_sectionVars_1434_; lean_object* v_sectionFVars_1435_; uint8_t v_implicitLambda_1436_; uint8_t v_heedElabAsElim_1437_; uint8_t v_isNoncomputableSection_1438_; uint8_t v_isMetaSection_1439_; uint8_t v_ignoreTCFailures_1440_; uint8_t v_inPattern_1441_; lean_object* v_tacSnap_x3f_1442_; uint8_t v_saveRecAppSyntax_1443_; uint8_t v_holesAsSyntheticOpaque_1444_; lean_object* v_fixedTermElabs_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_declName_x3f_1428_ = lean_ctor_get(v___y_1421_, 0);
v_macroStack_1429_ = lean_ctor_get(v___y_1421_, 1);
v_mayPostpone_1430_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8);
v_errToSorry_1431_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1432_ = lean_ctor_get(v___y_1421_, 2);
v_autoBoundImplicitForbidden_1433_ = lean_ctor_get(v___y_1421_, 3);
v_sectionVars_1434_ = lean_ctor_get(v___y_1421_, 4);
v_sectionFVars_1435_ = lean_ctor_get(v___y_1421_, 5);
v_implicitLambda_1436_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1437_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1438_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8 + 4);
v_isMetaSection_1439_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_1440_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8 + 6);
v_inPattern_1441_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1442_ = lean_ctor_get(v___y_1421_, 6);
v_saveRecAppSyntax_1443_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1444_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*8 + 9);
v_fixedTermElabs_1445_ = lean_ctor_get(v___y_1421_, 7);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_beforeStx_1418_);
lean_ctor_set(v___x_1446_, 1, v_afterStx_1419_);
lean_inc(v_macroStack_1429_);
v___x_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
lean_ctor_set(v___x_1447_, 1, v_macroStack_1429_);
lean_inc_ref(v_fixedTermElabs_1445_);
lean_inc(v_tacSnap_x3f_1442_);
lean_inc(v_sectionFVars_1435_);
lean_inc(v_sectionVars_1434_);
lean_inc_ref(v_autoBoundImplicitForbidden_1433_);
lean_inc(v_autoBoundImplicitContext_1432_);
lean_inc(v_declName_x3f_1428_);
v___x_1448_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_1448_, 0, v_declName_x3f_1428_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
lean_ctor_set(v___x_1448_, 2, v_autoBoundImplicitContext_1432_);
lean_ctor_set(v___x_1448_, 3, v_autoBoundImplicitForbidden_1433_);
lean_ctor_set(v___x_1448_, 4, v_sectionVars_1434_);
lean_ctor_set(v___x_1448_, 5, v_sectionFVars_1435_);
lean_ctor_set(v___x_1448_, 6, v_tacSnap_x3f_1442_);
lean_ctor_set(v___x_1448_, 7, v_fixedTermElabs_1445_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8, v_mayPostpone_1430_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8 + 1, v_errToSorry_1431_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8 + 2, v_implicitLambda_1436_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8 + 3, v_heedElabAsElim_1437_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1438_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8 + 5, v_isMetaSection_1439_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8 + 6, v_ignoreTCFailures_1440_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8 + 7, v_inPattern_1441_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1443_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1444_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
v___x_1449_ = lean_apply_7(v_x_1420_, v___x_1448_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, lean_box(0));
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg___boxed(lean_object* v_beforeStx_1450_, lean_object* v_afterStx_1451_, lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_beforeStx_1450_, v_afterStx_1451_, v_x_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0(lean_object* v_00_u03b1_1461_, lean_object* v_beforeStx_1462_, lean_object* v_afterStx_1463_, lean_object* v_x_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_beforeStx_1462_, v_afterStx_1463_, v_x_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___boxed(lean_object* v_00_u03b1_1473_, lean_object* v_beforeStx_1474_, lean_object* v_afterStx_1475_, lean_object* v_x_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0(v_00_u03b1_1473_, v_beforeStx_1474_, v_afterStx_1475_, v_x_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0(lean_object* v_s_1485_, lean_object* v___x_1486_, lean_object* v_fst_1487_, lean_object* v_snd_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v___x_1496_; 
lean_inc(v_s_1485_);
v___x_1496_ = l_Lean_Elab_Term_withDeprecationContextForSyntax___redArg(v_s_1485_, v___x_1486_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1505_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1505_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1505_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1501_, 0, v_fst_1487_);
lean_ctor_set(v___x_1501_, 1, v_s_1485_);
lean_ctor_set(v___x_1501_, 2, v_snd_1488_);
lean_ctor_set(v___x_1501_, 3, v_a_1497_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1501_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
lean_dec(v_snd_1488_);
lean_dec(v_fst_1487_);
lean_dec(v_s_1485_);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed(lean_object* v_s_1506_, lean_object* v___x_1507_, lean_object* v_fst_1508_, lean_object* v_snd_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0(v_s_1506_, v___x_1507_, v_fst_1508_, v_snd_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1517_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__0);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1521_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1522_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
lean_ctor_set(v___x_1524_, 2, v___x_1523_);
lean_ctor_set(v___x_1524_, 3, v___x_1523_);
lean_ctor_set(v___x_1524_, 4, v___x_1522_);
lean_ctor_set(v___x_1524_, 5, v___x_1522_);
lean_ctor_set(v___x_1524_, 6, v___x_1522_);
lean_ctor_set(v___x_1524_, 7, v___x_1522_);
lean_ctor_set(v___x_1524_, 8, v___x_1522_);
lean_ctor_set(v___x_1524_, 9, v___x_1522_);
lean_ctor_set(v___x_1524_, 10, v___x_1522_);
lean_ctor_set(v___x_1524_, 11, v___x_1521_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = lean_unsigned_to_nat(32u);
v___x_1526_ = lean_mk_empty_array_with_capacity(v___x_1525_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1528_ = ((size_t)5ULL);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = lean_unsigned_to_nat(32u);
v___x_1531_ = lean_mk_empty_array_with_capacity(v___x_1530_);
v___x_1532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3);
v___x_1533_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___x_1531_);
lean_ctor_set(v___x_1533_, 2, v___x_1529_);
lean_ctor_set(v___x_1533_, 3, v___x_1529_);
lean_ctor_set_usize(v___x_1533_, 4, v___x_1528_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1534_ = lean_box(1);
v___x_1535_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4);
v___x_1536_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_1537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1535_);
lean_ctor_set(v___x_1537_, 2, v___x_1534_);
return v___x_1537_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__6));
v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__8));
v___x_1543_ = l_Lean_stringToMessageData(v___x_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__10));
v___x_1546_ = l_Lean_stringToMessageData(v___x_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__12));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__14));
v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(lean_object* v_msg_1559_, lean_object* v_declHint_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_env_1565_; uint8_t v___x_1566_; 
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_st_ref_get(v___y_1561_);
v_env_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc_ref(v_env_1565_);
lean_dec(v___x_1564_);
v___x_1566_ = l_Lean_Name_isAnonymous(v_declHint_1560_);
if (v___x_1566_ == 0)
{
uint8_t v_isExporting_1567_; 
v_isExporting_1567_ = lean_ctor_get_uint8(v_env_1565_, sizeof(void*)*13);
if (v_isExporting_1567_ == 0)
{
lean_object* v___x_1568_; 
lean_dec_ref(v_env_1565_);
lean_dec(v_declHint_1560_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_msg_1559_);
return v___x_1568_;
}
else
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
lean_inc_ref(v_env_1565_);
v___x_1569_ = l_Lean_Environment_setExporting(v_env_1565_, v___x_1566_);
lean_inc(v_declHint_1560_);
lean_inc_ref(v___x_1569_);
v___x_1570_ = l_Lean_Environment_contains(v___x_1569_, v_declHint_1560_, v_isExporting_1567_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_env_1565_);
lean_dec(v_declHint_1560_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_msg_1559_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v_c_1577_; lean_object* v___x_1578_; 
v___x_1572_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_1573_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5);
v___x_1574_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1569_);
v___x_1575_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1569_);
lean_ctor_set(v___x_1575_, 1, v___x_1572_);
lean_ctor_set(v___x_1575_, 2, v___x_1573_);
lean_ctor_set(v___x_1575_, 3, v___x_1574_);
lean_inc(v_declHint_1560_);
v___x_1576_ = l_Lean_MessageData_ofConstName(v_declHint_1560_, v___x_1566_);
v_c_1577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1577_, 0, v___x_1575_);
lean_ctor_set(v_c_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1569_, v_declHint_1560_);
lean_dec_ref(v___x_1569_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref(v_env_1565_);
lean_dec(v_declHint_1560_);
v___x_1579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v_c_1577_);
v___x_1581_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = l_Lean_MessageData_note(v___x_1582_);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v_msg_1559_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
else
{
lean_object* v_val_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1620_; 
v_val_1586_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1588_ = v___x_1578_;
v_isShared_1589_ = v_isSharedCheck_1620_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_val_1586_);
lean_dec(v___x_1578_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1620_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v_moduleNames_1591_; lean_object* v_mod_1592_; uint8_t v___x_1593_; 
v___x_1590_ = l_Lean_Environment_header(v_env_1565_);
lean_dec_ref(v_env_1565_);
v_moduleNames_1591_ = lean_ctor_get(v___x_1590_, 4);
lean_inc_ref(v_moduleNames_1591_);
lean_dec_ref(v___x_1590_);
v_mod_1592_ = lean_array_get(v___x_1563_, v_moduleNames_1591_, v_val_1586_);
lean_dec(v_val_1586_);
lean_dec_ref(v_moduleNames_1591_);
v___x_1593_ = l_Lean_isPrivateName(v_declHint_1560_);
lean_dec(v_declHint_1560_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v_c_1577_);
v___x_1596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_MessageData_ofName(v_mod_1592_);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = l_Lean_MessageData_note(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v_msg_1559_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1603_);
v___x_1605_ = v___x_1588_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_c_1577_);
v___x_1609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_MessageData_ofName(v_mod_1592_);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l_Lean_MessageData_note(v___x_1614_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_msg_1559_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1616_);
v___x_1618_ = v___x_1588_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1621_; 
lean_dec_ref(v_env_1565_);
lean_dec(v_declHint_1560_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_msg_1559_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1622_, lean_object* v_declHint_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1622_, v_declHint_1623_, v___y_1624_);
lean_dec(v___y_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(lean_object* v_msg_1627_, lean_object* v_declHint_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1646_; 
v___x_1636_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1627_, v_declHint_1628_, v___y_1634_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1641_ = l_Lean_unknownIdentifierMessageTag;
v___x_1642_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_a_1637_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1642_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4___boxed(lean_object* v_msg_1647_, lean_object* v_declHint_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(v_msg_1647_, v_declHint_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_1657_, lean_object* v_msg_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_toCold_1666_; lean_object* v_currRecDepth_1667_; lean_object* v_ref_1668_; uint16_t v_optionFlags_1669_; uint8_t v_suppressElabErrors_1670_; uint8_t v_checkDeprecated_1671_; uint8_t v_isRecordingDeps_1672_; lean_object* v_ref_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_toCold_1666_ = lean_ctor_get(v___y_1663_, 0);
v_currRecDepth_1667_ = lean_ctor_get(v___y_1663_, 1);
v_ref_1668_ = lean_ctor_get(v___y_1663_, 2);
v_optionFlags_1669_ = lean_ctor_get_uint16(v___y_1663_, sizeof(void*)*3);
v_suppressElabErrors_1670_ = lean_ctor_get_uint8(v___y_1663_, sizeof(void*)*3 + 2);
v_checkDeprecated_1671_ = lean_ctor_get_uint8(v___y_1663_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1672_ = lean_ctor_get_uint8(v___y_1663_, sizeof(void*)*3 + 4);
v_ref_1673_ = l_Lean_replaceRef(v_ref_1657_, v_ref_1668_);
lean_inc(v_currRecDepth_1667_);
lean_inc_ref(v_toCold_1666_);
v___x_1674_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1674_, 0, v_toCold_1666_);
lean_ctor_set(v___x_1674_, 1, v_currRecDepth_1667_);
lean_ctor_set(v___x_1674_, 2, v_ref_1673_);
lean_ctor_set_uint16(v___x_1674_, sizeof(void*)*3, v_optionFlags_1669_);
lean_ctor_set_uint8(v___x_1674_, sizeof(void*)*3 + 2, v_suppressElabErrors_1670_);
lean_ctor_set_uint8(v___x_1674_, sizeof(void*)*3 + 3, v_checkDeprecated_1671_);
lean_ctor_set_uint8(v___x_1674_, sizeof(void*)*3 + 4, v_isRecordingDeps_1672_);
v___x_1675_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v_msg_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___x_1674_, v___y_1664_);
lean_dec_ref_known(v___x_1674_, 3);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1676_, lean_object* v_msg_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_1676_, v_msg_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v_ref_1676_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(lean_object* v_ref_1686_, lean_object* v_msg_1687_, lean_object* v_declHint_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; lean_object* v_a_1697_; lean_object* v___x_1698_; 
v___x_1696_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(v_msg_1687_, v_declHint_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_1686_, v_a_1697_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg___boxed(lean_object* v_ref_1699_, lean_object* v_msg_1700_, lean_object* v_declHint_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_1699_, v_msg_1700_, v_declHint_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v_ref_1699_);
return v_res_1709_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__0));
v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__2));
v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(lean_object* v_ref_1716_, lean_object* v_constName_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; uint8_t v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1725_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1);
v___x_1726_ = 0;
lean_inc(v_constName_1717_);
v___x_1727_ = l_Lean_MessageData_ofConstName(v_constName_1717_, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1725_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_1716_, v___x_1730_, v_constName_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___boxed(lean_object* v_ref_1732_, lean_object* v_constName_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_ref_1732_, v_constName_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v_ref_1732_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed(lean_object* v_s_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_s_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(lean_object* v_ref_1797_, uint8_t v_kind_1798_, lean_object* v_f_1799_, lean_object* v_lhs_1800_, lean_object* v_rhs_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_1810_ = 0;
lean_inc(v_f_1799_);
v___x_1811_ = l_Lean_Elab_Term_resolveId_x3f(v_f_1799_, v___x_1809_, v___x_1810_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1846_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1846_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1846_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
if (lean_obj_tag(v_a_1812_) == 1)
{
lean_object* v_val_1816_; lean_object* v___y_1818_; lean_object* v_rhs_1819_; lean_object* v_lhs_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; uint8_t v___x_1838_; uint8_t v___x_1839_; 
lean_dec(v_f_1799_);
v_val_1816_ = lean_ctor_get(v_a_1812_, 0);
lean_inc(v_val_1816_);
lean_dec_ref_known(v_a_1812_, 1);
v___x_1838_ = 2;
v___x_1839_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_1798_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_lhs_1800_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v_lhs_1825_ = v_a_1841_;
v___y_1826_ = v_a_1802_;
v___y_1827_ = v_a_1803_;
v___y_1828_ = v_a_1804_;
v___y_1829_ = v_a_1805_;
v___y_1830_ = v_a_1806_;
v___y_1831_ = v_a_1807_;
goto v___jp_1824_;
}
else
{
lean_dec(v_val_1816_);
lean_del_object(v___x_1814_);
lean_dec(v_rhs_1801_);
lean_dec(v_ref_1797_);
return v___x_1840_;
}
}
else
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_lhs_1800_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v_lhs_1825_ = v_a_1843_;
v___y_1826_ = v_a_1802_;
v___y_1827_ = v_a_1803_;
v___y_1828_ = v_a_1804_;
v___y_1829_ = v_a_1805_;
v___y_1830_ = v_a_1806_;
v___y_1831_ = v_a_1807_;
goto v___jp_1824_;
}
else
{
lean_dec(v_val_1816_);
lean_del_object(v___x_1814_);
lean_dec(v_rhs_1801_);
lean_dec(v_ref_1797_);
return v___x_1842_;
}
}
v___jp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1820_, 0, v_ref_1797_);
lean_ctor_set(v___x_1820_, 1, v_val_1816_);
lean_ctor_set(v___x_1820_, 2, v___y_1818_);
lean_ctor_set(v___x_1820_, 3, v_rhs_1819_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*4, v_kind_1798_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1820_);
v___x_1822_ = v___x_1814_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
v___jp_1824_:
{
uint8_t v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = 3;
v___x_1833_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_1798_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
v___x_1834_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_rhs_1801_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___y_1818_ = v_lhs_1825_;
v_rhs_1819_ = v_a_1835_;
goto v___jp_1817_;
}
else
{
lean_dec_ref(v_lhs_1825_);
lean_dec(v_val_1816_);
lean_del_object(v___x_1814_);
lean_dec(v_ref_1797_);
return v___x_1834_;
}
}
else
{
lean_object* v___x_1836_; 
v___x_1836_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_rhs_1801_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___y_1818_ = v_lhs_1825_;
v_rhs_1819_ = v_a_1837_;
goto v___jp_1817_;
}
else
{
lean_dec_ref(v_lhs_1825_);
lean_dec(v_val_1816_);
lean_del_object(v___x_1814_);
lean_dec(v_ref_1797_);
return v___x_1836_;
}
}
}
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_del_object(v___x_1814_);
lean_dec(v_a_1812_);
lean_dec(v_rhs_1801_);
lean_dec(v_lhs_1800_);
lean_dec(v_ref_1797_);
v___x_1844_ = l_Lean_Syntax_getId(v_f_1799_);
v___x_1845_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_f_1799_, v___x_1844_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
lean_dec(v_f_1799_);
return v___x_1845_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_rhs_1801_);
lean_dec(v_lhs_1800_);
lean_dec(v_f_1799_);
lean_dec(v_ref_1797_);
v_a_1847_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1811_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1811_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(lean_object* v_s_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1));
lean_inc(v_s_1855_);
v___x_1864_ = l_Lean_Syntax_isOfKind(v_s_1855_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3));
lean_inc(v_s_1855_);
v___x_1866_ = l_Lean_Syntax_isOfKind(v_s_1855_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5));
lean_inc(v_s_1855_);
v___x_1868_ = l_Lean_Syntax_isOfKind(v_s_1855_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7));
lean_inc(v_s_1855_);
v___x_1870_ = l_Lean_Syntax_isOfKind(v_s_1855_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9));
lean_inc(v_s_1855_);
v___x_1872_ = l_Lean_Syntax_isOfKind(v_s_1855_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11));
lean_inc(v_s_1855_);
v___x_1874_ = l_Lean_Syntax_isOfKind(v_s_1855_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v_toCold_1875_; lean_object* v_currRecDepth_1876_; lean_object* v_ref_1877_; uint16_t v_optionFlags_1878_; uint8_t v_suppressElabErrors_1879_; uint8_t v_checkDeprecated_1880_; uint8_t v_isRecordingDeps_1881_; lean_object* v_ref_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_toCold_1875_ = lean_ctor_get(v_a_1860_, 0);
v_currRecDepth_1876_ = lean_ctor_get(v_a_1860_, 1);
v_ref_1877_ = lean_ctor_get(v_a_1860_, 2);
v_optionFlags_1878_ = lean_ctor_get_uint16(v_a_1860_, sizeof(void*)*3);
v_suppressElabErrors_1879_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 2);
v_checkDeprecated_1880_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1881_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 4);
v_ref_1882_ = l_Lean_replaceRef(v_s_1855_, v_ref_1877_);
lean_inc(v_currRecDepth_1876_);
lean_inc_ref(v_toCold_1875_);
v___x_1883_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1883_, 0, v_toCold_1875_);
lean_ctor_set(v___x_1883_, 1, v_currRecDepth_1876_);
lean_ctor_set(v___x_1883_, 2, v_ref_1882_);
lean_ctor_set_uint16(v___x_1883_, sizeof(void*)*3, v_optionFlags_1878_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*3 + 2, v_suppressElabErrors_1879_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*3 + 3, v_checkDeprecated_1880_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*3 + 4, v_isRecordingDeps_1881_);
lean_inc(v_s_1855_);
v___x_1884_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v___x_1883_, v_a_1861_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
if (lean_obj_tag(v_a_1885_) == 0)
{
lean_object* v___x_1886_; 
v___x_1886_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v___x_1883_, v_a_1861_);
lean_dec_ref_known(v___x_1883_, 3);
return v___x_1886_;
}
else
{
lean_object* v_val_1887_; lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v___x_1890_; lean_object* v___f_1891_; lean_object* v___x_1892_; 
v_val_1887_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v_val_1887_);
lean_dec_ref_known(v_a_1885_, 1);
v_fst_1888_ = lean_ctor_get(v_val_1887_, 0);
lean_inc(v_fst_1888_);
v_snd_1889_ = lean_ctor_get(v_val_1887_, 1);
lean_inc_n(v_snd_1889_, 3);
lean_dec(v_val_1887_);
v___x_1890_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed), 8, 1);
lean_closure_set(v___x_1890_, 0, v_snd_1889_);
lean_inc(v_s_1855_);
v___f_1891_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1891_, 0, v_s_1855_);
lean_closure_set(v___f_1891_, 1, v___x_1890_);
lean_closure_set(v___f_1891_, 2, v_fst_1888_);
lean_closure_set(v___f_1891_, 3, v_snd_1889_);
v___x_1892_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1855_, v_snd_1889_, v___f_1891_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v___x_1883_, v_a_1861_);
lean_dec_ref_known(v___x_1883_, 3);
return v___x_1892_;
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref_known(v___x_1883_, 3);
lean_dec(v_s_1855_);
v_a_1893_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1884_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1884_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1901_);
v___x_1903_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13));
lean_inc(v___x_1902_);
v___x_1904_ = l_Lean_Syntax_isOfKind(v___x_1902_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v_toCold_1905_; lean_object* v_currRecDepth_1906_; lean_object* v_ref_1907_; uint16_t v_optionFlags_1908_; uint8_t v_suppressElabErrors_1909_; uint8_t v_checkDeprecated_1910_; uint8_t v_isRecordingDeps_1911_; lean_object* v_ref_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec(v___x_1902_);
v_toCold_1905_ = lean_ctor_get(v_a_1860_, 0);
v_currRecDepth_1906_ = lean_ctor_get(v_a_1860_, 1);
v_ref_1907_ = lean_ctor_get(v_a_1860_, 2);
v_optionFlags_1908_ = lean_ctor_get_uint16(v_a_1860_, sizeof(void*)*3);
v_suppressElabErrors_1909_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 2);
v_checkDeprecated_1910_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1911_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 4);
v_ref_1912_ = l_Lean_replaceRef(v_s_1855_, v_ref_1907_);
lean_inc(v_currRecDepth_1906_);
lean_inc_ref(v_toCold_1905_);
v___x_1913_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1913_, 0, v_toCold_1905_);
lean_ctor_set(v___x_1913_, 1, v_currRecDepth_1906_);
lean_ctor_set(v___x_1913_, 2, v_ref_1912_);
lean_ctor_set_uint16(v___x_1913_, sizeof(void*)*3, v_optionFlags_1908_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*3 + 2, v_suppressElabErrors_1909_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*3 + 3, v_checkDeprecated_1910_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*3 + 4, v_isRecordingDeps_1911_);
lean_inc(v_s_1855_);
v___x_1914_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v___x_1913_, v_a_1861_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
if (lean_obj_tag(v_a_1915_) == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v___x_1913_, v_a_1861_);
lean_dec_ref_known(v___x_1913_, 3);
return v___x_1916_;
}
else
{
lean_object* v_val_1917_; lean_object* v_fst_1918_; lean_object* v_snd_1919_; lean_object* v___x_1920_; lean_object* v___f_1921_; lean_object* v___x_1922_; 
v_val_1917_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v_a_1915_, 1);
v_fst_1918_ = lean_ctor_get(v_val_1917_, 0);
lean_inc(v_fst_1918_);
v_snd_1919_ = lean_ctor_get(v_val_1917_, 1);
lean_inc_n(v_snd_1919_, 3);
lean_dec(v_val_1917_);
v___x_1920_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed), 8, 1);
lean_closure_set(v___x_1920_, 0, v_snd_1919_);
lean_inc(v_s_1855_);
v___f_1921_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1921_, 0, v_s_1855_);
lean_closure_set(v___f_1921_, 1, v___x_1920_);
lean_closure_set(v___f_1921_, 2, v_fst_1918_);
lean_closure_set(v___f_1921_, 3, v_snd_1919_);
v___x_1922_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1855_, v_snd_1919_, v___f_1921_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v___x_1913_, v_a_1861_);
lean_dec_ref_known(v___x_1913_, 3);
return v___x_1922_;
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref_known(v___x_1913_, 3);
lean_dec(v_s_1855_);
v_a_1923_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1914_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1914_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v___x_1931_; lean_object* v_h_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1931_ = lean_unsigned_to_nat(1u);
v_h_1932_ = l_Lean_Syntax_getArg(v___x_1902_, v___x_1931_);
lean_dec(v___x_1902_);
v___x_1933_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__15));
lean_inc(v_h_1932_);
v___x_1934_ = l_Lean_Syntax_isOfKind(v_h_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v_toCold_1935_; lean_object* v_currRecDepth_1936_; lean_object* v_ref_1937_; uint16_t v_optionFlags_1938_; uint8_t v_suppressElabErrors_1939_; uint8_t v_checkDeprecated_1940_; uint8_t v_isRecordingDeps_1941_; lean_object* v_ref_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v_h_1932_);
v_toCold_1935_ = lean_ctor_get(v_a_1860_, 0);
v_currRecDepth_1936_ = lean_ctor_get(v_a_1860_, 1);
v_ref_1937_ = lean_ctor_get(v_a_1860_, 2);
v_optionFlags_1938_ = lean_ctor_get_uint16(v_a_1860_, sizeof(void*)*3);
v_suppressElabErrors_1939_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 2);
v_checkDeprecated_1940_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1941_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 4);
v_ref_1942_ = l_Lean_replaceRef(v_s_1855_, v_ref_1937_);
lean_inc(v_currRecDepth_1936_);
lean_inc_ref(v_toCold_1935_);
v___x_1943_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1943_, 0, v_toCold_1935_);
lean_ctor_set(v___x_1943_, 1, v_currRecDepth_1936_);
lean_ctor_set(v___x_1943_, 2, v_ref_1942_);
lean_ctor_set_uint16(v___x_1943_, sizeof(void*)*3, v_optionFlags_1938_);
lean_ctor_set_uint8(v___x_1943_, sizeof(void*)*3 + 2, v_suppressElabErrors_1939_);
lean_ctor_set_uint8(v___x_1943_, sizeof(void*)*3 + 3, v_checkDeprecated_1940_);
lean_ctor_set_uint8(v___x_1943_, sizeof(void*)*3 + 4, v_isRecordingDeps_1941_);
lean_inc(v_s_1855_);
v___x_1944_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v___x_1943_, v_a_1861_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
if (lean_obj_tag(v_a_1945_) == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v___x_1943_, v_a_1861_);
lean_dec_ref_known(v___x_1943_, 3);
return v___x_1946_;
}
else
{
lean_object* v_val_1947_; lean_object* v_fst_1948_; lean_object* v_snd_1949_; lean_object* v___x_1950_; lean_object* v___f_1951_; lean_object* v___x_1952_; 
v_val_1947_ = lean_ctor_get(v_a_1945_, 0);
lean_inc(v_val_1947_);
lean_dec_ref_known(v_a_1945_, 1);
v_fst_1948_ = lean_ctor_get(v_val_1947_, 0);
lean_inc(v_fst_1948_);
v_snd_1949_ = lean_ctor_get(v_val_1947_, 1);
lean_inc_n(v_snd_1949_, 3);
lean_dec(v_val_1947_);
v___x_1950_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed), 8, 1);
lean_closure_set(v___x_1950_, 0, v_snd_1949_);
lean_inc(v_s_1855_);
v___f_1951_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1951_, 0, v_s_1855_);
lean_closure_set(v___f_1951_, 1, v___x_1950_);
lean_closure_set(v___f_1951_, 2, v_fst_1948_);
lean_closure_set(v___f_1951_, 3, v_snd_1949_);
v___x_1952_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1855_, v_snd_1949_, v___f_1951_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v___x_1943_, v_a_1861_);
lean_dec_ref_known(v___x_1943_, 3);
return v___x_1952_;
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref_known(v___x_1943_, 3);
lean_dec(v_s_1855_);
v_a_1953_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1944_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1944_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1961_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1931_);
v___x_1962_ = l_Lean_TSyntax_getHygieneInfo(v_h_1932_);
lean_dec(v_h_1932_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_inc(v___x_1961_);
v___x_1964_ = l_Lean_Elab_Term_hasCDot(v___x_1961_, v___x_1963_);
lean_dec_ref_known(v___x_1963_, 1);
if (v___x_1964_ == 0)
{
lean_dec(v_s_1855_);
v_s_1855_ = v___x_1961_;
goto _start;
}
else
{
lean_object* v___x_1966_; 
lean_dec(v___x_1961_);
v___x_1966_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1966_;
}
}
}
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1967_);
v___x_1969_ = lean_unsigned_to_nat(2u);
v___x_1970_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1969_);
v___x_1971_ = lean_unsigned_to_nat(3u);
v___x_1972_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1971_);
v___x_1973_ = 3;
v___x_1974_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1855_, v___x_1973_, v___x_1968_, v___x_1970_, v___x_1972_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1974_;
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1975_ = lean_unsigned_to_nat(1u);
v___x_1976_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1975_);
v___x_1977_ = lean_unsigned_to_nat(2u);
v___x_1978_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1977_);
v___x_1979_ = lean_unsigned_to_nat(3u);
v___x_1980_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1979_);
v___x_1981_ = 2;
v___x_1982_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1855_, v___x_1981_, v___x_1976_, v___x_1978_, v___x_1980_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1982_;
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1983_);
v___x_1985_ = lean_unsigned_to_nat(2u);
v___x_1986_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1985_);
v___x_1987_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(v_s_1855_, v___x_1984_, v___x_1986_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1987_;
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; 
v___x_1988_ = lean_unsigned_to_nat(1u);
v___x_1989_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1988_);
v___x_1990_ = lean_unsigned_to_nat(2u);
v___x_1991_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1990_);
v___x_1992_ = lean_unsigned_to_nat(3u);
v___x_1993_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1992_);
v___x_1994_ = 1;
v___x_1995_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1855_, v___x_1994_, v___x_1989_, v___x_1991_, v___x_1993_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1995_;
}
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; 
v___x_1996_ = lean_unsigned_to_nat(1u);
v___x_1997_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1996_);
v___x_1998_ = lean_unsigned_to_nat(2u);
v___x_1999_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_1998_);
v___x_2000_ = lean_unsigned_to_nat(3u);
v___x_2001_ = l_Lean_Syntax_getArg(v_s_1855_, v___x_2000_);
v___x_2002_ = 0;
v___x_2003_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1855_, v___x_2002_, v___x_1997_, v___x_1999_, v___x_2001_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(lean_object* v_ref_2004_, lean_object* v_f_2005_, lean_object* v_arg_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_2015_ = 0;
lean_inc(v_f_2005_);
v___x_2016_ = l_Lean_Elab_Term_resolveId_x3f(v_f_2005_, v___x_2014_, v___x_2015_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
if (lean_obj_tag(v_a_2017_) == 1)
{
lean_object* v_val_2018_; lean_object* v___x_2019_; 
lean_dec(v_f_2005_);
v_val_2018_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_val_2018_);
lean_dec_ref_known(v_a_2017_, 1);
v___x_2019_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_arg_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2024_, 0, v_ref_2004_);
lean_ctor_set(v___x_2024_, 1, v_val_2018_);
lean_ctor_set(v___x_2024_, 2, v_a_2020_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_dec(v_val_2018_);
lean_dec(v_ref_2004_);
return v___x_2019_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v_a_2017_);
lean_dec(v_arg_2006_);
lean_dec(v_ref_2004_);
v___x_2029_ = l_Lean_Syntax_getId(v_f_2005_);
v___x_2030_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_f_2005_, v___x_2029_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_f_2005_);
return v___x_2030_;
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_arg_2006_);
lean_dec(v_f_2005_);
lean_dec(v_ref_2004_);
v_a_2031_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2016_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2016_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___boxed(lean_object* v_ref_2039_, lean_object* v_f_2040_, lean_object* v_arg_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(v_ref_2039_, v_f_2040_, v_arg_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp___boxed(lean_object* v_ref_2050_, lean_object* v_kind_2051_, lean_object* v_f_2052_, lean_object* v_lhs_2053_, lean_object* v_rhs_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
uint8_t v_kind_boxed_2062_; lean_object* v_res_2063_; 
v_kind_boxed_2062_ = lean_unbox(v_kind_2051_);
v_res_2063_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_ref_2050_, v_kind_boxed_2062_, v_f_2052_, v_lhs_2053_, v_rhs_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2(lean_object* v_00_u03b1_2064_, lean_object* v_ref_2065_, lean_object* v_constName_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_ref_2065_, v_constName_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___boxed(lean_object* v_00_u03b1_2075_, lean_object* v_ref_2076_, lean_object* v_constName_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2(v_00_u03b1_2075_, v_ref_2076_, v_constName_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v_ref_2076_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2(lean_object* v_00_u03b1_2086_, lean_object* v_ref_2087_, lean_object* v_msg_2088_, lean_object* v_declHint_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_2087_, v_msg_2088_, v_declHint_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2098_, lean_object* v_ref_2099_, lean_object* v_msg_2100_, lean_object* v_declHint_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2(v_00_u03b1_2098_, v_ref_2099_, v_msg_2100_, v_declHint_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v_ref_2099_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5(lean_object* v_msg_2110_, lean_object* v_declHint_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_2110_, v_declHint_2111_, v___y_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_2120_, lean_object* v_declHint_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5(v_msg_2120_, v_declHint_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_2130_, lean_object* v_ref_2131_, lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_2131_, v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2141_, lean_object* v_ref_2142_, lean_object* v_msg_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5(v_00_u03b1_2141_, v_ref_2142_, v_msg_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v_ref_2142_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(lean_object* v_s_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_s_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; uint8_t v___x_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = 0;
v___x_2163_ = 0;
v___x_2164_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_2162_, v___x_2163_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; 
v_unused_2172_ = lean_ctor_get(v___x_2164_, 0);
lean_dec(v_unused_2172_);
v___x_2166_ = v___x_2164_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_dec(v___x_2164_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v_a_2161_);
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2161_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2161_);
v_a_2173_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2164_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2164_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree___boxed(lean_object* v_s_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v_s_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0(lean_object* v_toType_2190_, uint8_t v___x_2191_, lean_object* v_x_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_Meta_coerceSimple_x3f(v_x_2192_, v_toType_2190_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2214_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2214_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2214_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
if (lean_obj_tag(v_a_2201_) == 1)
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
lean_dec_ref_known(v_a_2201_, 1);
v___x_2205_ = lean_box(v___x_2191_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2205_);
v___x_2207_ = v___x_2203_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
else
{
uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
lean_dec(v_a_2201_);
v___x_2209_ = 0;
v___x_2210_ = lean_box(v___x_2209_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2210_);
v___x_2212_ = v___x_2203_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
v_a_2215_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2200_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2200_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0___boxed(lean_object* v_toType_2223_, lean_object* v___x_2224_, lean_object* v_x_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v___x_1721__boxed_2233_; lean_object* v_res_2234_; 
v___x_1721__boxed_2233_ = lean_unbox(v___x_2224_);
v_res_2234_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0(v_toType_2223_, v___x_1721__boxed_2233_, v_x_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v_b_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2237_);
lean_inc_ref(v___y_2236_);
v___x_2244_ = lean_apply_8(v_k_2235_, v_b_2238_, v___y_2236_, v___y_2237_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, lean_box(0));
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v_b_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0(v_k_2245_, v___y_2246_, v___y_2247_, v_b_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(lean_object* v_name_2255_, uint8_t v_bi_2256_, lean_object* v_type_2257_, lean_object* v_k_2258_, uint8_t v_kind_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___f_2267_; lean_object* v___x_2268_; 
lean_inc(v___y_2261_);
lean_inc_ref(v___y_2260_);
v___f_2267_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2267_, 0, v_k_2258_);
lean_closure_set(v___f_2267_, 1, v___y_2260_);
lean_closure_set(v___f_2267_, 2, v___y_2261_);
v___x_2268_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2255_, v_bi_2256_, v_type_2257_, v___f_2267_, v_kind_2259_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2268_) == 0)
{
return v___x_2268_;
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___boxed(lean_object* v_name_2277_, lean_object* v_bi_2278_, lean_object* v_type_2279_, lean_object* v_k_2280_, lean_object* v_kind_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
uint8_t v_bi_boxed_2289_; uint8_t v_kind_boxed_2290_; lean_object* v_res_2291_; 
v_bi_boxed_2289_ = lean_unbox(v_bi_2278_);
v_kind_boxed_2290_ = lean_unbox(v_kind_2281_);
v_res_2291_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_2277_, v_bi_boxed_2289_, v_type_2279_, v_k_2280_, v_kind_boxed_2290_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(lean_object* v_name_2292_, lean_object* v_type_2293_, lean_object* v_k_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
uint8_t v___x_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = 0;
v___x_2303_ = 0;
v___x_2304_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_2292_, v___x_2302_, v_type_2293_, v_k_2294_, v___x_2303_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg___boxed(lean_object* v_name_2305_, lean_object* v_type_2306_, lean_object* v_k_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v_name_2305_, v_type_2306_, v_k_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(lean_object* v_fromType_2319_, lean_object* v_toType_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v___x_2328_; lean_object* v_env_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; uint8_t v___x_2332_; 
v___x_2328_ = lean_st_ref_get(v_a_2326_);
v_env_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc_ref(v_env_2329_);
lean_dec(v___x_2328_);
v___x_2330_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__1));
v___x_2331_ = 1;
v___x_2332_ = l_Lean_Environment_contains(v_env_2329_, v___x_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec_ref(v_toType_2320_);
lean_dec_ref(v_fromType_2319_);
v___x_2333_ = lean_box(v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
return v___x_2334_;
}
else
{
lean_object* v___x_2335_; lean_object* v___f_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2335_ = lean_box(v___x_2331_);
v___f_2336_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2336_, 0, v_toType_2320_);
lean_closure_set(v___f_2336_, 1, v___x_2335_);
v___x_2337_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__1));
v___x_2338_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v___x_2337_, v_fromType_2319_, v___f_2336_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___boxed(lean_object* v_fromType_2339_, lean_object* v_toType_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v_fromType_2339_, v_toType_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0(lean_object* v_00_u03b1_2349_, lean_object* v_name_2350_, uint8_t v_bi_2351_, lean_object* v_type_2352_, lean_object* v_k_2353_, uint8_t v_kind_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_2350_, v_bi_2351_, v_type_2352_, v_k_2353_, v_kind_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2363_, lean_object* v_name_2364_, lean_object* v_bi_2365_, lean_object* v_type_2366_, lean_object* v_k_2367_, lean_object* v_kind_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
uint8_t v_bi_boxed_2376_; uint8_t v_kind_boxed_2377_; lean_object* v_res_2378_; 
v_bi_boxed_2376_ = lean_unbox(v_bi_2365_);
v_kind_boxed_2377_ = lean_unbox(v_kind_2368_);
v_res_2378_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0(v_00_u03b1_2363_, v_name_2364_, v_bi_boxed_2376_, v_type_2366_, v_k_2367_, v_kind_boxed_2377_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0(lean_object* v_00_u03b1_2379_, lean_object* v_name_2380_, lean_object* v_type_2381_, lean_object* v_k_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v_name_2380_, v_type_2381_, v_k_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___boxed(lean_object* v_00_u03b1_2391_, lean_object* v_name_2392_, lean_object* v_type_2393_, lean_object* v_k_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0(v_00_u03b1_2391_, v_name_2392_, v_type_2393_, v_k_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2402_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(lean_object* v_x_2403_){
_start:
{
switch(lean_obj_tag(v_x_2403_))
{
case 2:
{
uint8_t v___x_2404_; 
v___x_2404_ = 1;
return v___x_2404_;
}
case 5:
{
lean_object* v_fn_2405_; 
v_fn_2405_ = lean_ctor_get(v_x_2403_, 0);
v_x_2403_ = v_fn_2405_;
goto _start;
}
case 8:
{
lean_object* v_body_2407_; 
v_body_2407_ = lean_ctor_get(v_x_2403_, 3);
v_x_2403_ = v_body_2407_;
goto _start;
}
case 10:
{
lean_object* v_expr_2409_; 
v_expr_2409_ = lean_ctor_get(v_x_2403_, 1);
v_x_2403_ = v_expr_2409_;
goto _start;
}
default: 
{
uint8_t v___x_2411_; 
v___x_2411_ = 0;
return v___x_2411_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown___boxed(lean_object* v_x_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v_x_2412_);
lean_dec_ref(v_x_2412_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(lean_object* v_e_2415_, lean_object* v___y_2416_){
_start:
{
uint8_t v___x_2418_; 
v___x_2418_ = l_Lean_Expr_hasMVar(v_e_2415_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v_e_2415_);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; lean_object* v_mctx_2421_; lean_object* v___x_2422_; lean_object* v_fst_2423_; lean_object* v_snd_2424_; lean_object* v___x_2425_; lean_object* v_cache_2426_; lean_object* v_zetaDeltaFVarIds_2427_; lean_object* v_postponed_2428_; lean_object* v_diag_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2438_; 
v___x_2420_ = lean_st_ref_get(v___y_2416_);
v_mctx_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc_ref(v_mctx_2421_);
lean_dec(v___x_2420_);
v___x_2422_ = l_Lean_instantiateMVarsCore(v_mctx_2421_, v_e_2415_);
v_fst_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_fst_2423_);
v_snd_2424_ = lean_ctor_get(v___x_2422_, 1);
lean_inc(v_snd_2424_);
lean_dec_ref(v___x_2422_);
v___x_2425_ = lean_st_ref_take(v___y_2416_);
v_cache_2426_ = lean_ctor_get(v___x_2425_, 1);
v_zetaDeltaFVarIds_2427_ = lean_ctor_get(v___x_2425_, 2);
v_postponed_2428_ = lean_ctor_get(v___x_2425_, 3);
v_diag_2429_ = lean_ctor_get(v___x_2425_, 4);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2438_ == 0)
{
lean_object* v_unused_2439_; 
v_unused_2439_ = lean_ctor_get(v___x_2425_, 0);
lean_dec(v_unused_2439_);
v___x_2431_ = v___x_2425_;
v_isShared_2432_ = v_isSharedCheck_2438_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_diag_2429_);
lean_inc(v_postponed_2428_);
lean_inc(v_zetaDeltaFVarIds_2427_);
lean_inc(v_cache_2426_);
lean_dec(v___x_2425_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2438_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v_snd_2424_);
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_snd_2424_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_cache_2426_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_zetaDeltaFVarIds_2427_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_postponed_2428_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_diag_2429_);
v___x_2434_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_st_ref_put(v___y_2416_, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_fst_2423_);
return v___x_2436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg___boxed(lean_object* v_e_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_e_2440_, v___y_2441_);
lean_dec(v___y_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0(lean_object* v_e_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_e_2444_, v___y_2449_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___boxed(lean_object* v_e_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0(v_e_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0(lean_object* v_k_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
lean_inc(v___y_2467_);
lean_inc_ref(v___y_2466_);
lean_inc(v___y_2465_);
v___x_2473_ = lean_apply_8(v_k_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, lean_box(0));
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0(v_k_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(lean_object* v_k_2484_, uint8_t v_allowLevelAssignments_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___f_2494_; lean_object* v___x_2495_; 
lean_inc(v___y_2488_);
lean_inc_ref(v___y_2487_);
lean_inc(v___y_2486_);
v___f_2494_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2494_, 0, v_k_2484_);
lean_closure_set(v___f_2494_, 1, v___y_2486_);
lean_closure_set(v___f_2494_, 2, v___y_2487_);
lean_closure_set(v___f_2494_, 3, v___y_2488_);
v___x_2495_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2485_, v___f_2494_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2495_) == 0)
{
return v___x_2495_;
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___boxed(lean_object* v_k_2504_, lean_object* v_allowLevelAssignments_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2514_; lean_object* v_res_2515_; 
v_allowLevelAssignments_boxed_2514_ = lean_unbox(v_allowLevelAssignments_2505_);
v_res_2515_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v_k_2504_, v_allowLevelAssignments_boxed_2514_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1(lean_object* v_00_u03b1_2516_, lean_object* v_k_2517_, uint8_t v_allowLevelAssignments_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v_k_2517_, v_allowLevelAssignments_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___boxed(lean_object* v_00_u03b1_2528_, lean_object* v_k_2529_, lean_object* v_allowLevelAssignments_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2539_; lean_object* v_res_2540_; 
v_allowLevelAssignments_boxed_2539_ = lean_unbox(v_allowLevelAssignments_2530_);
v_res_2540_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1(v_00_u03b1_2528_, v_k_2529_, v_allowLevelAssignments_boxed_2539_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0(uint8_t v___x_2541_, lean_object* v_val_2542_, lean_object* v___x_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___x_2552_; uint8_t v_foApprox_2553_; uint8_t v_ctxApprox_2554_; uint8_t v_quasiPatternApprox_2555_; uint8_t v_constApprox_2556_; uint8_t v_unificationHints_2557_; uint8_t v_proofIrrelevance_2558_; uint8_t v_assignSyntheticOpaque_2559_; uint8_t v_offsetCnstrs_2560_; uint8_t v_transparency_2561_; uint8_t v_etaStruct_2562_; uint8_t v_univApprox_2563_; uint8_t v_iota_2564_; uint8_t v_beta_2565_; uint8_t v_proj_2566_; uint8_t v_zeta_2567_; uint8_t v_zetaDelta_2568_; uint8_t v_zetaUnused_2569_; uint8_t v_zetaHave_2570_; uint8_t v_canUnfoldPredicateConfig_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2592_; 
v___x_2552_ = l_Lean_Meta_Context_config(v___y_2547_);
v_foApprox_2553_ = lean_ctor_get_uint8(v___x_2552_, 0);
v_ctxApprox_2554_ = lean_ctor_get_uint8(v___x_2552_, 1);
v_quasiPatternApprox_2555_ = lean_ctor_get_uint8(v___x_2552_, 2);
v_constApprox_2556_ = lean_ctor_get_uint8(v___x_2552_, 3);
v_unificationHints_2557_ = lean_ctor_get_uint8(v___x_2552_, 5);
v_proofIrrelevance_2558_ = lean_ctor_get_uint8(v___x_2552_, 6);
v_assignSyntheticOpaque_2559_ = lean_ctor_get_uint8(v___x_2552_, 7);
v_offsetCnstrs_2560_ = lean_ctor_get_uint8(v___x_2552_, 8);
v_transparency_2561_ = lean_ctor_get_uint8(v___x_2552_, 9);
v_etaStruct_2562_ = lean_ctor_get_uint8(v___x_2552_, 10);
v_univApprox_2563_ = lean_ctor_get_uint8(v___x_2552_, 11);
v_iota_2564_ = lean_ctor_get_uint8(v___x_2552_, 12);
v_beta_2565_ = lean_ctor_get_uint8(v___x_2552_, 13);
v_proj_2566_ = lean_ctor_get_uint8(v___x_2552_, 14);
v_zeta_2567_ = lean_ctor_get_uint8(v___x_2552_, 15);
v_zetaDelta_2568_ = lean_ctor_get_uint8(v___x_2552_, 16);
v_zetaUnused_2569_ = lean_ctor_get_uint8(v___x_2552_, 17);
v_zetaHave_2570_ = lean_ctor_get_uint8(v___x_2552_, 18);
v_canUnfoldPredicateConfig_2571_ = lean_ctor_get_uint8(v___x_2552_, 19);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2573_ = v___x_2552_;
v_isShared_2574_ = v_isSharedCheck_2592_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v___x_2552_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2592_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
uint8_t v_trackZetaDelta_2575_; lean_object* v_zetaDeltaSet_2576_; lean_object* v_lctx_2577_; lean_object* v_localInstances_2578_; lean_object* v_defEqCtx_x3f_2579_; lean_object* v_synthPendingDepth_2580_; lean_object* v_customCanUnfoldPredicate_x3f_2581_; uint8_t v_univApprox_2582_; uint8_t v_inTypeClassResolution_2583_; uint8_t v_cacheInferType_2584_; lean_object* v___x_2586_; 
v_trackZetaDelta_2575_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7);
v_zetaDeltaSet_2576_ = lean_ctor_get(v___y_2547_, 1);
v_lctx_2577_ = lean_ctor_get(v___y_2547_, 2);
v_localInstances_2578_ = lean_ctor_get(v___y_2547_, 3);
v_defEqCtx_x3f_2579_ = lean_ctor_get(v___y_2547_, 4);
v_synthPendingDepth_2580_ = lean_ctor_get(v___y_2547_, 5);
v_customCanUnfoldPredicate_x3f_2581_ = lean_ctor_get(v___y_2547_, 6);
v_univApprox_2582_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2583_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7 + 2);
v_cacheInferType_2584_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7 + 3);
if (v_isShared_2574_ == 0)
{
v___x_2586_ = v___x_2573_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 0, v_foApprox_2553_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 1, v_ctxApprox_2554_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 2, v_quasiPatternApprox_2555_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 3, v_constApprox_2556_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 5, v_unificationHints_2557_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 6, v_proofIrrelevance_2558_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 7, v_assignSyntheticOpaque_2559_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 8, v_offsetCnstrs_2560_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 9, v_transparency_2561_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 10, v_etaStruct_2562_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 11, v_univApprox_2563_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 12, v_iota_2564_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 13, v_beta_2565_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 14, v_proj_2566_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 15, v_zeta_2567_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 16, v_zetaDelta_2568_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 17, v_zetaUnused_2569_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 18, v_zetaHave_2570_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, 19, v_canUnfoldPredicateConfig_2571_);
v___x_2586_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
uint64_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_ctor_set_uint8(v___x_2586_, 4, v___x_2541_);
v___x_2587_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2586_);
v___x_2588_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set_uint64(v___x_2588_, sizeof(void*)*1, v___x_2587_);
lean_inc(v_customCanUnfoldPredicate_x3f_2581_);
lean_inc(v_synthPendingDepth_2580_);
lean_inc(v_defEqCtx_x3f_2579_);
lean_inc_ref(v_localInstances_2578_);
lean_inc_ref(v_lctx_2577_);
lean_inc(v_zetaDeltaSet_2576_);
v___x_2589_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set(v___x_2589_, 1, v_zetaDeltaSet_2576_);
lean_ctor_set(v___x_2589_, 2, v_lctx_2577_);
lean_ctor_set(v___x_2589_, 3, v_localInstances_2578_);
lean_ctor_set(v___x_2589_, 4, v_defEqCtx_x3f_2579_);
lean_ctor_set(v___x_2589_, 5, v_synthPendingDepth_2580_);
lean_ctor_set(v___x_2589_, 6, v_customCanUnfoldPredicate_x3f_2581_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*7, v_trackZetaDelta_2575_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*7 + 1, v_univApprox_2582_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2583_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*7 + 3, v_cacheInferType_2584_);
v___x_2590_ = l_Lean_Meta_isExprDefEqGuarded(v_val_2542_, v___x_2543_, v___x_2589_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref_known(v___x_2589_, 7);
return v___x_2590_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0___boxed(lean_object* v___x_2593_, lean_object* v_val_2594_, lean_object* v___x_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
uint8_t v___x_14785__boxed_2604_; lean_object* v_res_2605_; 
v___x_14785__boxed_2604_ = lean_unbox(v___x_2593_);
v_res_2605_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0(v___x_14785__boxed_2604_, v_val_2594_, v___x_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
return v_res_2605_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2606_; double v___x_2607_; 
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_float_of_nat(v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(lean_object* v_cls_2611_, lean_object* v_msg_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_ref_2618_; lean_object* v___x_2619_; lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2665_; 
v_ref_2618_ = lean_ctor_get(v___y_2615_, 2);
v___x_2619_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2665_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2665_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v_traceState_2625_; lean_object* v_env_2626_; lean_object* v_nextMacroScope_2627_; lean_object* v_ngen_2628_; lean_object* v_auxDeclNGen_2629_; lean_object* v_cache_2630_; lean_object* v_recordedDeps_2631_; lean_object* v_messages_2632_; lean_object* v_infoState_2633_; lean_object* v_snapshotTasks_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2664_; 
v___x_2624_ = lean_st_ref_take(v___y_2616_);
v_traceState_2625_ = lean_ctor_get(v___x_2624_, 4);
v_env_2626_ = lean_ctor_get(v___x_2624_, 0);
v_nextMacroScope_2627_ = lean_ctor_get(v___x_2624_, 1);
v_ngen_2628_ = lean_ctor_get(v___x_2624_, 2);
v_auxDeclNGen_2629_ = lean_ctor_get(v___x_2624_, 3);
v_cache_2630_ = lean_ctor_get(v___x_2624_, 5);
v_recordedDeps_2631_ = lean_ctor_get(v___x_2624_, 6);
v_messages_2632_ = lean_ctor_get(v___x_2624_, 7);
v_infoState_2633_ = lean_ctor_get(v___x_2624_, 8);
v_snapshotTasks_2634_ = lean_ctor_get(v___x_2624_, 9);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2636_ = v___x_2624_;
v_isShared_2637_ = v_isSharedCheck_2664_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_snapshotTasks_2634_);
lean_inc(v_infoState_2633_);
lean_inc(v_messages_2632_);
lean_inc(v_recordedDeps_2631_);
lean_inc(v_cache_2630_);
lean_inc(v_traceState_2625_);
lean_inc(v_auxDeclNGen_2629_);
lean_inc(v_ngen_2628_);
lean_inc(v_nextMacroScope_2627_);
lean_inc(v_env_2626_);
lean_dec(v___x_2624_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2664_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
uint64_t v_tid_2638_; lean_object* v_traces_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2663_; 
v_tid_2638_ = lean_ctor_get_uint64(v_traceState_2625_, sizeof(void*)*1);
v_traces_2639_ = lean_ctor_get(v_traceState_2625_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_traceState_2625_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2641_ = v_traceState_2625_;
v_isShared_2642_ = v_isSharedCheck_2663_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_traces_2639_);
lean_dec(v_traceState_2625_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2663_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; double v___x_2645_; uint8_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2643_ = lean_box(0);
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0);
v___x_2646_ = 0;
v___x_2647_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1));
v___x_2648_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2648_, 0, v_cls_2611_);
lean_ctor_set(v___x_2648_, 1, v___x_2644_);
lean_ctor_set(v___x_2648_, 2, v___x_2647_);
lean_ctor_set_float(v___x_2648_, sizeof(void*)*3, v___x_2645_);
lean_ctor_set_float(v___x_2648_, sizeof(void*)*3 + 8, v___x_2645_);
lean_ctor_set_uint8(v___x_2648_, sizeof(void*)*3 + 16, v___x_2646_);
v___x_2649_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2));
v___x_2650_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2648_);
lean_ctor_set(v___x_2650_, 1, v_a_2620_);
lean_ctor_set(v___x_2650_, 2, v___x_2649_);
lean_inc(v_ref_2618_);
v___x_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2651_, 0, v_ref_2618_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Lean_PersistentArray_push___redArg(v_traces_2639_, v___x_2651_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2652_);
v___x_2654_ = v___x_2641_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2652_);
lean_ctor_set_uint64(v_reuseFailAlloc_2662_, sizeof(void*)*1, v_tid_2638_);
v___x_2654_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2656_; 
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 4, v___x_2654_);
v___x_2656_ = v___x_2636_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_env_2626_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_nextMacroScope_2627_);
lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_ngen_2628_);
lean_ctor_set(v_reuseFailAlloc_2661_, 3, v_auxDeclNGen_2629_);
lean_ctor_set(v_reuseFailAlloc_2661_, 4, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2661_, 5, v_cache_2630_);
lean_ctor_set(v_reuseFailAlloc_2661_, 6, v_recordedDeps_2631_);
lean_ctor_set(v_reuseFailAlloc_2661_, 7, v_messages_2632_);
lean_ctor_set(v_reuseFailAlloc_2661_, 8, v_infoState_2633_);
lean_ctor_set(v_reuseFailAlloc_2661_, 9, v_snapshotTasks_2634_);
v___x_2656_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = lean_st_ref_put(v___y_2616_, v___x_2656_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2643_);
v___x_2659_ = v___x_2622_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2643_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___boxed(lean_object* v_cls_2666_, lean_object* v_msg_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v_cls_2666_, v_msg_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
return v_res_2673_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_2681_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2));
v___x_2682_ = l_Lean_Name_append(v___x_2681_, v___x_2680_);
return v___x_2682_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__4));
v___x_2685_ = l_Lean_stringToMessageData(v___x_2684_);
return v___x_2685_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__6));
v___x_2688_ = l_Lean_stringToMessageData(v___x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(lean_object* v_t_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v___x_2698_; uint8_t v_hasUncomparable_2699_; 
v___x_2698_ = lean_st_ref_get(v_a_2690_);
v_hasUncomparable_2699_ = lean_ctor_get_uint8(v___x_2698_, sizeof(void*)*1);
lean_dec(v___x_2698_);
if (v_hasUncomparable_2699_ == 0)
{
switch(lean_obj_tag(v_t_2689_))
{
case 0:
{
lean_object* v_val_2700_; uint8_t v___x_2701_; lean_object* v___y_2703_; lean_object* v___x_2717_; 
v_val_2700_ = lean_ctor_get(v_t_2689_, 2);
lean_inc_ref(v_val_2700_);
lean_dec_ref_known(v_t_2689_, 3);
v___x_2701_ = 1;
lean_inc(v_a_2696_);
lean_inc_ref(v_a_2695_);
lean_inc(v_a_2694_);
lean_inc_ref(v_a_2693_);
v___x_2717_ = lean_infer_type(v_val_2700_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2719_; lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2854_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_a_2718_, v_a_2694_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2854_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2854_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = l_Lean_Expr_cleanupAnnotations(v_a_2720_);
lean_dec(v_a_2720_);
v___x_2725_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v_max_x3f_2727_; 
v___x_2726_ = lean_st_ref_get(v_a_2690_);
v_max_x3f_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_max_x3f_2727_);
lean_dec(v___x_2726_);
if (lean_obj_tag(v_max_x3f_2727_) == 0)
{
lean_object* v___x_2728_; uint8_t v_hasUncomparable_2729_; uint8_t v_hasUnknown_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2743_; 
v___x_2728_ = lean_st_ref_take(v_a_2690_);
v_hasUncomparable_2729_ = lean_ctor_get_uint8(v___x_2728_, sizeof(void*)*1);
v_hasUnknown_2730_ = lean_ctor_get_uint8(v___x_2728_, sizeof(void*)*1 + 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v___x_2728_, 0);
lean_dec(v_unused_2744_);
v___x_2732_ = v___x_2728_;
v_isShared_2733_ = v_isSharedCheck_2743_;
goto v_resetjp_2731_;
}
else
{
lean_dec(v___x_2728_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2743_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2724_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2735_);
v___x_2737_ = v___x_2732_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2742_, sizeof(void*)*1, v_hasUncomparable_2729_);
lean_ctor_set_uint8(v_reuseFailAlloc_2742_, sizeof(void*)*1 + 1, v_hasUnknown_2730_);
v___x_2737_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = lean_st_ref_put(v_a_2690_, v___x_2737_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2734_);
v___x_2740_ = v___x_2722_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2734_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_val_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2838_; 
lean_del_object(v___x_2722_);
v_val_2745_ = lean_ctor_get(v_max_x3f_2727_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_max_x3f_2727_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2747_ = v_max_x3f_2727_;
v_isShared_2748_ = v_isSharedCheck_2838_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_val_2745_);
lean_dec(v_max_x3f_2727_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2838_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2749_; lean_object* v___f_2750_; lean_object* v___x_2751_; 
v___x_2749_ = lean_box(v___x_2701_);
lean_inc_ref(v___x_2724_);
lean_inc(v_val_2745_);
v___f_2750_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2750_, 0, v___x_2749_);
lean_closure_set(v___f_2750_, 1, v_val_2745_);
lean_closure_set(v___f_2750_, 2, v___x_2724_);
v___x_2751_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v___f_2750_, v___x_2725_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2829_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2829_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2829_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
uint8_t v___x_2756_; 
v___x_2756_ = lean_unbox(v_a_2752_);
lean_dec(v_a_2752_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; 
lean_del_object(v___x_2754_);
lean_inc(v_val_2745_);
lean_inc_ref(v___x_2724_);
v___x_2757_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v___x_2724_, v_val_2745_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2816_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2816_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2816_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
uint8_t v___x_2762_; 
v___x_2762_ = lean_unbox(v_a_2758_);
lean_dec(v_a_2758_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; 
lean_del_object(v___x_2760_);
lean_inc_ref(v___x_2724_);
lean_inc(v_val_2745_);
v___x_2763_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v_val_2745_, v___x_2724_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2803_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2803_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2803_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
uint8_t v___x_2768_; 
v___x_2768_ = lean_unbox(v_a_2764_);
lean_dec(v_a_2764_);
if (v___x_2768_ == 0)
{
lean_object* v_toCold_2769_; lean_object* v_options_2770_; uint8_t v_hasTrace_2771_; 
lean_del_object(v___x_2766_);
lean_del_object(v___x_2747_);
v_toCold_2769_ = lean_ctor_get(v_a_2695_, 0);
v_options_2770_ = lean_ctor_get(v_toCold_2769_, 2);
v_hasTrace_2771_ = lean_ctor_get_uint8(v_options_2770_, sizeof(void*)*1);
if (v_hasTrace_2771_ == 0)
{
lean_dec(v_val_2745_);
lean_dec_ref(v___x_2724_);
v___y_2703_ = v_a_2690_;
goto v___jp_2702_;
}
else
{
lean_object* v_inheritedTraceOptions_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v_inheritedTraceOptions_2772_ = lean_ctor_get(v_toCold_2769_, 11);
v___x_2773_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_2774_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_2775_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2772_, v_options_2770_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_dec(v_val_2745_);
lean_dec_ref(v___x_2724_);
v___y_2703_ = v_a_2690_;
goto v___jp_2702_;
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2776_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5);
v___x_2777_ = l_Lean_MessageData_ofExpr(v_val_2745_);
v___x_2778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7);
v___x_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = l_Lean_MessageData_ofExpr(v___x_2724_);
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v___x_2773_, v___x_2782_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_dec_ref_known(v___x_2783_, 1);
v___y_2703_ = v_a_2690_;
goto v___jp_2702_;
}
else
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v___x_2784_; uint8_t v_hasUncomparable_2785_; uint8_t v_hasUnknown_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v_val_2745_);
v___x_2784_ = lean_st_ref_take(v_a_2690_);
v_hasUncomparable_2785_ = lean_ctor_get_uint8(v___x_2784_, sizeof(void*)*1);
v_hasUnknown_2786_ = lean_ctor_get_uint8(v___x_2784_, sizeof(void*)*1 + 1);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2801_ == 0)
{
lean_object* v_unused_2802_; 
v_unused_2802_ = lean_ctor_get(v___x_2784_, 0);
lean_dec(v_unused_2802_);
v___x_2788_ = v___x_2784_;
v_isShared_2789_ = v_isSharedCheck_2801_;
goto v_resetjp_2787_;
}
else
{
lean_dec(v___x_2784_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2801_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2790_ = lean_box(0);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2724_);
v___x_2792_ = v___x_2747_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2724_);
v___x_2792_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2794_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v___x_2792_);
v___x_2794_ = v___x_2788_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*1, v_hasUncomparable_2785_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*1 + 1, v_hasUnknown_2786_);
v___x_2794_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2795_ = lean_st_ref_put(v_a_2690_, v___x_2794_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2790_);
v___x_2797_ = v___x_2766_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2790_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_del_object(v___x_2747_);
lean_dec(v_val_2745_);
lean_dec_ref(v___x_2724_);
v_a_2804_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2763_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2763_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
lean_del_object(v___x_2747_);
lean_dec(v_val_2745_);
lean_dec_ref(v___x_2724_);
v___x_2812_ = lean_box(0);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2812_);
v___x_2814_ = v___x_2760_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_del_object(v___x_2747_);
lean_dec(v_val_2745_);
lean_dec_ref(v___x_2724_);
v_a_2817_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2757_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2757_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
lean_del_object(v___x_2747_);
lean_dec(v_val_2745_);
lean_dec_ref(v___x_2724_);
v___x_2825_ = lean_box(0);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2825_);
v___x_2827_ = v___x_2754_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_del_object(v___x_2747_);
lean_dec(v_val_2745_);
lean_dec_ref(v___x_2724_);
v_a_2830_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2751_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2751_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
}
else
{
lean_object* v___x_2839_; lean_object* v_max_x3f_2840_; uint8_t v_hasUncomparable_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v___x_2724_);
v___x_2839_ = lean_st_ref_take(v_a_2690_);
v_max_x3f_2840_ = lean_ctor_get(v___x_2839_, 0);
v_hasUncomparable_2841_ = lean_ctor_get_uint8(v___x_2839_, sizeof(void*)*1);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2843_ = v___x_2839_;
v_isShared_2844_ = v_isSharedCheck_2853_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_max_x3f_2840_);
lean_dec(v___x_2839_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2853_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2845_ = lean_box(0);
if (v_isShared_2844_ == 0)
{
v___x_2847_ = v___x_2843_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_max_x3f_2840_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*1, v_hasUncomparable_2841_);
v___x_2847_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*1 + 1, v___x_2701_);
v___x_2848_ = lean_st_ref_put(v_a_2690_, v___x_2847_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2845_);
v___x_2850_ = v___x_2722_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
v_a_2855_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2717_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2717_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
v___jp_2702_:
{
lean_object* v___x_2704_; lean_object* v_max_x3f_2705_; uint8_t v_hasUnknown_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2716_; 
v___x_2704_ = lean_st_ref_take(v___y_2703_);
v_max_x3f_2705_ = lean_ctor_get(v___x_2704_, 0);
v_hasUnknown_2706_ = lean_ctor_get_uint8(v___x_2704_, sizeof(void*)*1 + 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2708_ = v___x_2704_;
v_isShared_2709_ = v_isSharedCheck_2716_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_max_x3f_2705_);
lean_dec(v___x_2704_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2716_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2710_ = lean_box(0);
if (v_isShared_2709_ == 0)
{
v___x_2712_ = v___x_2708_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_max_x3f_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2715_, sizeof(void*)*1 + 1, v_hasUnknown_2706_);
v___x_2712_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*1, v___x_2701_);
v___x_2713_ = lean_st_ref_put(v___y_2703_, v___x_2712_);
v___x_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2710_);
return v___x_2714_;
}
}
}
}
case 1:
{
uint8_t v_kind_2863_; 
v_kind_2863_ = lean_ctor_get_uint8(v_t_2689_, sizeof(void*)*4);
switch(v_kind_2863_)
{
case 2:
{
lean_object* v_rhs_2864_; 
v_rhs_2864_ = lean_ctor_get(v_t_2689_, 3);
lean_inc_ref(v_rhs_2864_);
lean_dec_ref_known(v_t_2689_, 4);
v_t_2689_ = v_rhs_2864_;
goto _start;
}
case 3:
{
lean_object* v_lhs_2866_; 
v_lhs_2866_ = lean_ctor_get(v_t_2689_, 2);
lean_inc_ref(v_lhs_2866_);
lean_dec_ref_known(v_t_2689_, 4);
v_t_2689_ = v_lhs_2866_;
goto _start;
}
default: 
{
lean_object* v_lhs_2868_; lean_object* v_rhs_2869_; lean_object* v___x_2870_; 
v_lhs_2868_ = lean_ctor_get(v_t_2689_, 2);
lean_inc_ref(v_lhs_2868_);
v_rhs_2869_ = lean_ctor_get(v_t_2689_, 3);
lean_inc_ref(v_rhs_2869_);
lean_dec_ref_known(v_t_2689_, 4);
v___x_2870_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_lhs_2868_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_dec_ref_known(v___x_2870_, 1);
v_t_2689_ = v_rhs_2869_;
goto _start;
}
else
{
lean_dec_ref(v_rhs_2869_);
return v___x_2870_;
}
}
}
}
case 2:
{
lean_object* v_arg_2872_; 
v_arg_2872_ = lean_ctor_get(v_t_2689_, 2);
lean_inc_ref(v_arg_2872_);
lean_dec_ref_known(v_t_2689_, 3);
v_t_2689_ = v_arg_2872_;
goto _start;
}
default: 
{
lean_object* v_nested_2874_; 
v_nested_2874_ = lean_ctor_get(v_t_2689_, 3);
lean_inc_ref(v_nested_2874_);
lean_dec_ref_known(v_t_2689_, 4);
v_t_2689_ = v_nested_2874_;
goto _start;
}
}
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec_ref(v_t_2689_);
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___boxed(lean_object* v_t_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_t_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2(lean_object* v_cls_2888_, lean_object* v_msg_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v_cls_2888_, v_msg_2889_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___boxed(lean_object* v_cls_2899_, lean_object* v_msg_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2(v_cls_2899_, v_msg_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(lean_object* v_t_2910_, lean_object* v_expectedType_x3f_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_max_x3f_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; 
if (lean_obj_tag(v_expectedType_x3f_2911_) == 0)
{
v_max_x3f_2920_ = v_expectedType_x3f_2911_;
v___y_2921_ = v_a_2912_;
v___y_2922_ = v_a_2913_;
v___y_2923_ = v_a_2914_;
v___y_2924_ = v_a_2915_;
v___y_2925_ = v_a_2916_;
v___y_2926_ = v_a_2917_;
goto v___jp_2919_;
}
else
{
lean_object* v_val_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2961_; 
v_val_2949_ = lean_ctor_get(v_expectedType_x3f_2911_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_expectedType_x3f_2911_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2951_ = v_expectedType_x3f_2911_;
v_isShared_2952_ = v_isSharedCheck_2961_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_val_2949_);
lean_dec(v_expectedType_x3f_2911_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2961_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v_a_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2953_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(v_val_2949_, v_a_2915_);
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref(v___x_2953_);
v___x_2955_ = l_Lean_Expr_cleanupAnnotations(v_a_2954_);
lean_dec(v_a_2954_);
v___x_2956_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2958_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2955_);
v___x_2958_ = v___x_2951_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2955_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
v_max_x3f_2920_ = v___x_2958_;
v___y_2921_ = v_a_2912_;
v___y_2922_ = v_a_2913_;
v___y_2923_ = v_a_2914_;
v___y_2924_ = v_a_2915_;
v___y_2925_ = v_a_2916_;
v___y_2926_ = v_a_2917_;
goto v___jp_2919_;
}
}
else
{
lean_object* v___x_2960_; 
lean_dec_ref(v___x_2955_);
lean_del_object(v___x_2951_);
v___x_2960_ = lean_box(0);
v_max_x3f_2920_ = v___x_2960_;
v___y_2921_ = v_a_2912_;
v___y_2922_ = v_a_2913_;
v___y_2923_ = v_a_2914_;
v___y_2924_ = v_a_2915_;
v___y_2925_ = v_a_2916_;
v___y_2926_ = v_a_2917_;
goto v___jp_2919_;
}
}
}
v___jp_2919_:
{
uint8_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2927_ = 0;
v___x_2928_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2928_, 0, v_max_x3f_2920_);
lean_ctor_set_uint8(v___x_2928_, sizeof(void*)*1, v___x_2927_);
lean_ctor_set_uint8(v___x_2928_, sizeof(void*)*1 + 1, v___x_2927_);
v___x_2929_ = lean_st_mk_ref(v___x_2928_);
v___x_2930_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_t_2910_, v___x_2929_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2939_; 
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; 
v_unused_2940_ = lean_ctor_get(v___x_2930_, 0);
lean_dec(v_unused_2940_);
v___x_2932_ = v___x_2930_;
v_isShared_2933_ = v_isSharedCheck_2939_;
goto v_resetjp_2931_;
}
else
{
lean_dec(v___x_2930_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2939_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2934_ = lean_st_ref_get(v___x_2929_);
v___x_2935_ = lean_st_ref_get(v___x_2929_);
lean_dec(v___x_2929_);
lean_dec(v___x_2935_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2934_);
v___x_2937_ = v___x_2932_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2934_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v___x_2929_);
v_a_2941_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2930_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2930_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze___boxed(lean_object* v_t_2962_, lean_object* v_expectedType_x3f_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v_t_2962_, v_expectedType_x3f_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(uint8_t v_lazy_2974_, lean_object* v_f_2975_, lean_object* v_lhs_2976_, lean_object* v_rhs_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_rhs_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; 
if (v_lazy_2974_ == 0)
{
v_rhs_2986_ = v_rhs_2977_;
v___y_2987_ = v_a_2978_;
v___y_2988_ = v_a_2979_;
v___y_2989_ = v_a_2980_;
v___y_2990_ = v_a_2981_;
v___y_2991_ = v_a_2982_;
v___y_2992_ = v_a_2983_;
goto v___jp_2985_;
}
else
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Meta_mkFunUnit___redArg(v_rhs_2977_, v_a_2982_, v_a_2983_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v_rhs_2986_ = v_a_3004_;
v___y_2987_ = v_a_2978_;
v___y_2988_ = v_a_2979_;
v___y_2989_ = v_a_2980_;
v___y_2990_ = v_a_2981_;
v___y_2991_ = v_a_2982_;
v___y_2992_ = v_a_2983_;
goto v___jp_2985_;
}
else
{
lean_dec_ref(v_lhs_2976_);
lean_dec_ref(v_f_2975_);
return v___x_3003_;
}
}
v___jp_2985_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; 
v___x_2993_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v_lhs_2976_);
v___x_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2995_, 0, v_rhs_2986_);
v___x_2996_ = lean_unsigned_to_nat(2u);
v___x_2997_ = lean_mk_empty_array_with_capacity(v___x_2996_);
v___x_2998_ = lean_array_push(v___x_2997_, v___x_2994_);
v___x_2999_ = lean_array_push(v___x_2998_, v___x_2995_);
v___x_3000_ = lean_box(0);
v___x_3001_ = 0;
v___x_3002_ = l_Lean_Elab_Term_elabAppArgs(v_f_2975_, v___x_2993_, v___x_2999_, v___x_3000_, v___x_3001_, v___x_3001_, v___x_3001_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
return v___x_3002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___boxed(lean_object* v_lazy_3005_, lean_object* v_f_3006_, lean_object* v_lhs_3007_, lean_object* v_rhs_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
uint8_t v_lazy_boxed_3016_; lean_object* v_res_3017_; 
v_lazy_boxed_3016_ = lean_unbox(v_lazy_3005_);
v_res_3017_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v_lazy_boxed_3016_, v_f_3006_, v_lhs_3007_, v_rhs_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(lean_object* v_f_3018_, lean_object* v_arg_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; 
v___x_3027_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
v___x_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3028_, 0, v_arg_3019_);
v___x_3029_ = lean_unsigned_to_nat(1u);
v___x_3030_ = lean_mk_empty_array_with_capacity(v___x_3029_);
v___x_3031_ = lean_array_push(v___x_3030_, v___x_3028_);
v___x_3032_ = lean_box(0);
v___x_3033_ = 0;
v___x_3034_ = l_Lean_Elab_Term_elabAppArgs(v_f_3018_, v___x_3027_, v___x_3031_, v___x_3032_, v___x_3033_, v___x_3033_, v___x_3033_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp___boxed(lean_object* v_f_3035_, lean_object* v_arg_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(v_f_3035_, v_arg_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___y_3045_, lean_object* v_mkInfoTree_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v_a_3052_, lean_object* v_a_x3f_3053_){
_start:
{
lean_object* v___x_3055_; lean_object* v_infoState_3056_; lean_object* v_trees_3057_; lean_object* v___x_3058_; 
v___x_3055_ = lean_st_ref_get(v___y_3045_);
v_infoState_3056_ = lean_ctor_get(v___x_3055_, 8);
lean_inc_ref(v_infoState_3056_);
lean_dec(v___x_3055_);
v_trees_3057_ = lean_ctor_get(v_infoState_3056_, 2);
lean_inc_ref(v_trees_3057_);
lean_dec_ref(v_infoState_3056_);
lean_inc(v___y_3045_);
lean_inc_ref(v___y_3051_);
lean_inc(v___y_3050_);
lean_inc_ref(v___y_3049_);
lean_inc(v___y_3048_);
lean_inc_ref(v___y_3047_);
v___x_3058_ = lean_apply_8(v_mkInfoTree_3046_, v_trees_3057_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3045_, lean_box(0));
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3098_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3098_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3098_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v_infoState_3064_; lean_object* v_env_3065_; lean_object* v_nextMacroScope_3066_; lean_object* v_ngen_3067_; lean_object* v_auxDeclNGen_3068_; lean_object* v_traceState_3069_; lean_object* v_cache_3070_; lean_object* v_recordedDeps_3071_; lean_object* v_messages_3072_; lean_object* v_snapshotTasks_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3097_; 
v___x_3063_ = lean_st_ref_take(v___y_3045_);
v_infoState_3064_ = lean_ctor_get(v___x_3063_, 8);
v_env_3065_ = lean_ctor_get(v___x_3063_, 0);
v_nextMacroScope_3066_ = lean_ctor_get(v___x_3063_, 1);
v_ngen_3067_ = lean_ctor_get(v___x_3063_, 2);
v_auxDeclNGen_3068_ = lean_ctor_get(v___x_3063_, 3);
v_traceState_3069_ = lean_ctor_get(v___x_3063_, 4);
v_cache_3070_ = lean_ctor_get(v___x_3063_, 5);
v_recordedDeps_3071_ = lean_ctor_get(v___x_3063_, 6);
v_messages_3072_ = lean_ctor_get(v___x_3063_, 7);
v_snapshotTasks_3073_ = lean_ctor_get(v___x_3063_, 9);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3075_ = v___x_3063_;
v_isShared_3076_ = v_isSharedCheck_3097_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_snapshotTasks_3073_);
lean_inc(v_infoState_3064_);
lean_inc(v_messages_3072_);
lean_inc(v_recordedDeps_3071_);
lean_inc(v_cache_3070_);
lean_inc(v_traceState_3069_);
lean_inc(v_auxDeclNGen_3068_);
lean_inc(v_ngen_3067_);
lean_inc(v_nextMacroScope_3066_);
lean_inc(v_env_3065_);
lean_dec(v___x_3063_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3097_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
uint8_t v_enabled_3077_; lean_object* v_assignment_3078_; lean_object* v_lazyAssignment_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3095_; 
v_enabled_3077_ = lean_ctor_get_uint8(v_infoState_3064_, sizeof(void*)*3);
v_assignment_3078_ = lean_ctor_get(v_infoState_3064_, 0);
v_lazyAssignment_3079_ = lean_ctor_get(v_infoState_3064_, 1);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_infoState_3064_);
if (v_isSharedCheck_3095_ == 0)
{
lean_object* v_unused_3096_; 
v_unused_3096_ = lean_ctor_get(v_infoState_3064_, 2);
lean_dec(v_unused_3096_);
v___x_3081_ = v_infoState_3064_;
v_isShared_3082_ = v_isSharedCheck_3095_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_lazyAssignment_3079_);
lean_inc(v_assignment_3078_);
lean_dec(v_infoState_3064_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3095_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3083_ = lean_box(0);
v___x_3084_ = l_Lean_PersistentArray_push___redArg(v_a_3052_, v_a_3059_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 2, v___x_3084_);
v___x_3086_ = v___x_3081_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_assignment_3078_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_lazyAssignment_3079_);
lean_ctor_set(v_reuseFailAlloc_3094_, 2, v___x_3084_);
lean_ctor_set_uint8(v_reuseFailAlloc_3094_, sizeof(void*)*3, v_enabled_3077_);
v___x_3086_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 8, v___x_3086_);
v___x_3088_ = v___x_3075_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_env_3065_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_nextMacroScope_3066_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v_ngen_3067_);
lean_ctor_set(v_reuseFailAlloc_3093_, 3, v_auxDeclNGen_3068_);
lean_ctor_set(v_reuseFailAlloc_3093_, 4, v_traceState_3069_);
lean_ctor_set(v_reuseFailAlloc_3093_, 5, v_cache_3070_);
lean_ctor_set(v_reuseFailAlloc_3093_, 6, v_recordedDeps_3071_);
lean_ctor_set(v_reuseFailAlloc_3093_, 7, v_messages_3072_);
lean_ctor_set(v_reuseFailAlloc_3093_, 8, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3093_, 9, v_snapshotTasks_3073_);
v___x_3088_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_st_ref_put(v___y_3045_, v___x_3088_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3083_);
v___x_3091_ = v___x_3061_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3083_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v_a_3052_);
v_a_3099_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3058_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3058_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_3107_, lean_object* v_mkInfoTree_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v_a_3114_, lean_object* v_a_x3f_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_3107_, v_mkInfoTree_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v_a_3114_, v_a_x3f_3115_);
lean_dec(v_a_x3f_3115_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3107_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3118_, lean_object* v_mkInfoTree_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; lean_object* v_infoState_3128_; uint8_t v_enabled_3129_; 
v___x_3127_ = lean_st_ref_get(v___y_3125_);
v_infoState_3128_ = lean_ctor_get(v___x_3127_, 8);
lean_inc_ref(v_infoState_3128_);
lean_dec(v___x_3127_);
v_enabled_3129_ = lean_ctor_get_uint8(v_infoState_3128_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3128_);
if (v_enabled_3129_ == 0)
{
lean_object* v___x_3130_; 
lean_dec_ref(v_mkInfoTree_3119_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3124_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
lean_inc_ref(v___y_3120_);
v___x_3130_ = lean_apply_7(v_x_3118_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, lean_box(0));
return v___x_3130_;
}
else
{
lean_object* v___x_3131_; lean_object* v_a_3132_; lean_object* v_r_3133_; 
v___x_3131_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v___y_3125_);
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref(v___x_3131_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3124_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
lean_inc_ref(v___y_3120_);
v_r_3133_ = lean_apply_7(v_x_3118_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, lean_box(0));
if (lean_obj_tag(v_r_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3158_; 
v_a_3134_ = lean_ctor_get(v_r_3133_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_r_3133_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3136_ = v_r_3133_;
v_isShared_3137_ = v_isSharedCheck_3158_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v_r_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3158_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
lean_inc(v_a_3134_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set_tag(v___x_3136_, 1);
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_3125_, v_mkInfoTree_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v_a_3132_, v___x_3139_);
lean_dec_ref(v___x_3139_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v___x_3140_, 0);
lean_dec(v_unused_3148_);
v___x_3142_ = v___x_3140_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_dec(v___x_3140_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v_a_3134_);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3134_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec(v_a_3134_);
v_a_3149_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3140_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3140_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_a_3159_ = lean_ctor_get(v_r_3133_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v_r_3133_, 1);
v___x_3160_ = lean_box(0);
v___x_3161_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_3125_, v_mkInfoTree_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v_a_3132_, v___x_3160_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; 
v_unused_3169_ = lean_ctor_get(v___x_3161_, 0);
lean_dec(v_unused_3169_);
v___x_3163_ = v___x_3161_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_dec(v___x_3161_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 1);
lean_ctor_set(v___x_3163_, 0, v_a_3159_);
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3159_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec(v_a_3159_);
v_a_3170_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3161_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3161_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3178_, lean_object* v_mkInfoTree_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_3178_, v_mkInfoTree_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0(lean_object* v_stx_3188_, lean_object* v_output_3189_, lean_object* v_trees_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_lctx_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_lctx_3198_ = lean_ctor_get(v___y_3193_, 2);
lean_inc_ref(v_lctx_3198_);
v___x_3199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3199_, 0, v_lctx_3198_);
lean_ctor_set(v___x_3199_, 1, v_stx_3188_);
lean_ctor_set(v___x_3199_, 2, v_output_3189_);
v___x_3200_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
lean_ctor_set(v___x_3201_, 1, v_trees_3190_);
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_stx_3203_, lean_object* v_output_3204_, lean_object* v_trees_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0(v_stx_3203_, v_output_3204_, v_trees_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(lean_object* v_stx_3214_, lean_object* v_output_3215_, lean_object* v_x_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___f_3224_; lean_object* v___x_3225_; 
v___f_3224_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3224_, 0, v_stx_3214_);
lean_closure_set(v___f_3224_, 1, v_output_3215_);
v___x_3225_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_3216_, v___f_3224_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___boxed(lean_object* v_stx_3226_, lean_object* v_output_3227_, lean_object* v_x_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_stx_3226_, v_output_3227_, v_x_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(lean_object* v_beforeStx_3237_, lean_object* v_afterStx_3238_, lean_object* v_x_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_inc(v_afterStx_3238_);
lean_inc(v_beforeStx_3237_);
v___x_3247_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___boxed), 11, 4);
lean_closure_set(v___x_3247_, 0, lean_box(0));
lean_closure_set(v___x_3247_, 1, v_beforeStx_3237_);
lean_closure_set(v___x_3247_, 2, v_afterStx_3238_);
lean_closure_set(v___x_3247_, 3, v_x_3239_);
v___x_3248_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_beforeStx_3237_, v_afterStx_3238_, v___x_3247_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3248_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
v_a_3257_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3248_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3248_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg___boxed(lean_object* v_beforeStx_3265_, lean_object* v_afterStx_3266_, lean_object* v_x_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(v_beforeStx_3265_, v_afterStx_3266_, v_x_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0(lean_object* v_00_u03b1_3276_, lean_object* v_beforeStx_3277_, lean_object* v_afterStx_3278_, lean_object* v_x_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(v_beforeStx_3277_, v_afterStx_3278_, v_x_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___boxed(lean_object* v_00_u03b1_3288_, lean_object* v_beforeStx_3289_, lean_object* v_afterStx_3290_, lean_object* v_x_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0(v_00_u03b1_3288_, v_beforeStx_3289_, v_afterStx_3290_, v_x_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0(lean_object* v_lhs_3300_, lean_object* v_rhs_3301_, uint8_t v_kind_3302_, lean_object* v_f_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_lhs_3300_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3311_, 1);
v___x_3313_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_rhs_3301_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; uint8_t v___x_3315_; uint8_t v___x_3316_; lean_object* v___x_3317_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3313_, 1);
v___x_3315_ = 1;
v___x_3316_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_3302_, v___x_3315_);
v___x_3317_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v___x_3316_, v_f_3303_, v_a_3312_, v_a_3314_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
return v___x_3317_;
}
else
{
lean_dec(v_a_3312_);
lean_dec_ref(v_f_3303_);
return v___x_3313_;
}
}
else
{
lean_dec_ref(v_f_3303_);
lean_dec_ref(v_rhs_3301_);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0___boxed(lean_object* v_lhs_3318_, lean_object* v_rhs_3319_, lean_object* v_kind_3320_, lean_object* v_f_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v_kind_7882__boxed_3329_; lean_object* v_res_3330_; 
v_kind_7882__boxed_3329_ = lean_unbox(v_kind_3320_);
v_res_3330_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0(v_lhs_3318_, v_rhs_3319_, v_kind_7882__boxed_3329_, v_f_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1___boxed(lean_object* v_arg_3331_, lean_object* v_f_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1(v_arg_3331_, v_f_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___boxed(lean_object* v_t_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_t_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(lean_object* v_t_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_){
_start:
{
switch(lean_obj_tag(v_t_3350_))
{
case 0:
{
lean_object* v_infoTrees_3358_; lean_object* v_val_3359_; lean_object* v___x_3360_; lean_object* v_infoState_3361_; lean_object* v_env_3362_; lean_object* v_nextMacroScope_3363_; lean_object* v_ngen_3364_; lean_object* v_auxDeclNGen_3365_; lean_object* v_traceState_3366_; lean_object* v_cache_3367_; lean_object* v_recordedDeps_3368_; lean_object* v_messages_3369_; lean_object* v_snapshotTasks_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3391_; 
v_infoTrees_3358_ = lean_ctor_get(v_t_3350_, 1);
lean_inc_ref(v_infoTrees_3358_);
v_val_3359_ = lean_ctor_get(v_t_3350_, 2);
lean_inc_ref(v_val_3359_);
lean_dec_ref_known(v_t_3350_, 3);
v___x_3360_ = lean_st_ref_take(v_a_3356_);
v_infoState_3361_ = lean_ctor_get(v___x_3360_, 8);
v_env_3362_ = lean_ctor_get(v___x_3360_, 0);
v_nextMacroScope_3363_ = lean_ctor_get(v___x_3360_, 1);
v_ngen_3364_ = lean_ctor_get(v___x_3360_, 2);
v_auxDeclNGen_3365_ = lean_ctor_get(v___x_3360_, 3);
v_traceState_3366_ = lean_ctor_get(v___x_3360_, 4);
v_cache_3367_ = lean_ctor_get(v___x_3360_, 5);
v_recordedDeps_3368_ = lean_ctor_get(v___x_3360_, 6);
v_messages_3369_ = lean_ctor_get(v___x_3360_, 7);
v_snapshotTasks_3370_ = lean_ctor_get(v___x_3360_, 9);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3372_ = v___x_3360_;
v_isShared_3373_ = v_isSharedCheck_3391_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_snapshotTasks_3370_);
lean_inc(v_infoState_3361_);
lean_inc(v_messages_3369_);
lean_inc(v_recordedDeps_3368_);
lean_inc(v_cache_3367_);
lean_inc(v_traceState_3366_);
lean_inc(v_auxDeclNGen_3365_);
lean_inc(v_ngen_3364_);
lean_inc(v_nextMacroScope_3363_);
lean_inc(v_env_3362_);
lean_dec(v___x_3360_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3391_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
uint8_t v_enabled_3374_; lean_object* v_assignment_3375_; lean_object* v_lazyAssignment_3376_; lean_object* v_trees_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3390_; 
v_enabled_3374_ = lean_ctor_get_uint8(v_infoState_3361_, sizeof(void*)*3);
v_assignment_3375_ = lean_ctor_get(v_infoState_3361_, 0);
v_lazyAssignment_3376_ = lean_ctor_get(v_infoState_3361_, 1);
v_trees_3377_ = lean_ctor_get(v_infoState_3361_, 2);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_infoState_3361_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3379_ = v_infoState_3361_;
v_isShared_3380_ = v_isSharedCheck_3390_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_trees_3377_);
lean_inc(v_lazyAssignment_3376_);
lean_inc(v_assignment_3375_);
lean_dec(v_infoState_3361_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3390_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3381_ = l_Lean_PersistentArray_append___redArg(v_trees_3377_, v_infoTrees_3358_);
lean_dec_ref(v_infoTrees_3358_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 2, v___x_3381_);
v___x_3383_ = v___x_3379_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_assignment_3375_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_lazyAssignment_3376_);
lean_ctor_set(v_reuseFailAlloc_3389_, 2, v___x_3381_);
lean_ctor_set_uint8(v_reuseFailAlloc_3389_, sizeof(void*)*3, v_enabled_3374_);
v___x_3383_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 8, v___x_3383_);
v___x_3385_ = v___x_3372_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_env_3362_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_nextMacroScope_3363_);
lean_ctor_set(v_reuseFailAlloc_3388_, 2, v_ngen_3364_);
lean_ctor_set(v_reuseFailAlloc_3388_, 3, v_auxDeclNGen_3365_);
lean_ctor_set(v_reuseFailAlloc_3388_, 4, v_traceState_3366_);
lean_ctor_set(v_reuseFailAlloc_3388_, 5, v_cache_3367_);
lean_ctor_set(v_reuseFailAlloc_3388_, 6, v_recordedDeps_3368_);
lean_ctor_set(v_reuseFailAlloc_3388_, 7, v_messages_3369_);
lean_ctor_set(v_reuseFailAlloc_3388_, 8, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3388_, 9, v_snapshotTasks_3370_);
v___x_3385_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = lean_st_ref_put(v_a_3356_, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v_val_3359_);
return v___x_3387_;
}
}
}
}
}
case 1:
{
lean_object* v_ref_3392_; uint8_t v_kind_3393_; lean_object* v_f_3394_; lean_object* v_lhs_3395_; lean_object* v_rhs_3396_; lean_object* v_toCold_3397_; lean_object* v_currRecDepth_3398_; lean_object* v_ref_3399_; uint16_t v_optionFlags_3400_; uint8_t v_suppressElabErrors_3401_; uint8_t v_checkDeprecated_3402_; uint8_t v_isRecordingDeps_3403_; lean_object* v___x_3404_; lean_object* v___f_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; lean_object* v_ref_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v_ref_3392_ = lean_ctor_get(v_t_3350_, 0);
lean_inc(v_ref_3392_);
v_kind_3393_ = lean_ctor_get_uint8(v_t_3350_, sizeof(void*)*4);
v_f_3394_ = lean_ctor_get(v_t_3350_, 1);
lean_inc_ref(v_f_3394_);
v_lhs_3395_ = lean_ctor_get(v_t_3350_, 2);
lean_inc_ref(v_lhs_3395_);
v_rhs_3396_ = lean_ctor_get(v_t_3350_, 3);
lean_inc_ref(v_rhs_3396_);
lean_dec_ref_known(v_t_3350_, 4);
v_toCold_3397_ = lean_ctor_get(v_a_3355_, 0);
v_currRecDepth_3398_ = lean_ctor_get(v_a_3355_, 1);
v_ref_3399_ = lean_ctor_get(v_a_3355_, 2);
v_optionFlags_3400_ = lean_ctor_get_uint16(v_a_3355_, sizeof(void*)*3);
v_suppressElabErrors_3401_ = lean_ctor_get_uint8(v_a_3355_, sizeof(void*)*3 + 2);
v_checkDeprecated_3402_ = lean_ctor_get_uint8(v_a_3355_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3403_ = lean_ctor_get_uint8(v_a_3355_, sizeof(void*)*3 + 4);
v___x_3404_ = lean_box(v_kind_3393_);
v___f_3405_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3405_, 0, v_lhs_3395_);
lean_closure_set(v___f_3405_, 1, v_rhs_3396_);
lean_closure_set(v___f_3405_, 2, v___x_3404_);
lean_closure_set(v___f_3405_, 3, v_f_3394_);
v___x_3406_ = lean_box(0);
v___x_3407_ = lean_box(0);
v___x_3408_ = 0;
v_ref_3409_ = l_Lean_replaceRef(v_ref_3392_, v_ref_3399_);
lean_inc(v_currRecDepth_3398_);
lean_inc_ref(v_toCold_3397_);
v___x_3410_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3410_, 0, v_toCold_3397_);
lean_ctor_set(v___x_3410_, 1, v_currRecDepth_3398_);
lean_ctor_set(v___x_3410_, 2, v_ref_3409_);
lean_ctor_set_uint16(v___x_3410_, sizeof(void*)*3, v_optionFlags_3400_);
lean_ctor_set_uint8(v___x_3410_, sizeof(void*)*3 + 2, v_suppressElabErrors_3401_);
lean_ctor_set_uint8(v___x_3410_, sizeof(void*)*3 + 3, v_checkDeprecated_3402_);
lean_ctor_set_uint8(v___x_3410_, sizeof(void*)*3 + 4, v_isRecordingDeps_3403_);
v___x_3411_ = l_Lean_Elab_Term_withTermInfoContext_x27(v___x_3406_, v_ref_3392_, v___f_3405_, v___x_3407_, v___x_3407_, v___x_3408_, v___x_3408_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v___x_3410_, v_a_3356_);
lean_dec_ref_known(v___x_3410_, 3);
return v___x_3411_;
}
case 2:
{
lean_object* v_ref_3412_; lean_object* v_f_3413_; lean_object* v_arg_3414_; lean_object* v_toCold_3415_; lean_object* v_currRecDepth_3416_; lean_object* v_ref_3417_; uint16_t v_optionFlags_3418_; uint8_t v_suppressElabErrors_3419_; uint8_t v_checkDeprecated_3420_; uint8_t v_isRecordingDeps_3421_; lean_object* v___f_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; lean_object* v_ref_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_ref_3412_ = lean_ctor_get(v_t_3350_, 0);
lean_inc(v_ref_3412_);
v_f_3413_ = lean_ctor_get(v_t_3350_, 1);
lean_inc_ref(v_f_3413_);
v_arg_3414_ = lean_ctor_get(v_t_3350_, 2);
lean_inc_ref(v_arg_3414_);
lean_dec_ref_known(v_t_3350_, 3);
v_toCold_3415_ = lean_ctor_get(v_a_3355_, 0);
v_currRecDepth_3416_ = lean_ctor_get(v_a_3355_, 1);
v_ref_3417_ = lean_ctor_get(v_a_3355_, 2);
v_optionFlags_3418_ = lean_ctor_get_uint16(v_a_3355_, sizeof(void*)*3);
v_suppressElabErrors_3419_ = lean_ctor_get_uint8(v_a_3355_, sizeof(void*)*3 + 2);
v_checkDeprecated_3420_ = lean_ctor_get_uint8(v_a_3355_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3421_ = lean_ctor_get_uint8(v_a_3355_, sizeof(void*)*3 + 4);
v___f_3422_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3422_, 0, v_arg_3414_);
lean_closure_set(v___f_3422_, 1, v_f_3413_);
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_box(0);
v___x_3425_ = 0;
v_ref_3426_ = l_Lean_replaceRef(v_ref_3412_, v_ref_3417_);
lean_inc(v_currRecDepth_3416_);
lean_inc_ref(v_toCold_3415_);
v___x_3427_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3427_, 0, v_toCold_3415_);
lean_ctor_set(v___x_3427_, 1, v_currRecDepth_3416_);
lean_ctor_set(v___x_3427_, 2, v_ref_3426_);
lean_ctor_set_uint16(v___x_3427_, sizeof(void*)*3, v_optionFlags_3418_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*3 + 2, v_suppressElabErrors_3419_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*3 + 3, v_checkDeprecated_3420_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*3 + 4, v_isRecordingDeps_3421_);
v___x_3428_ = l_Lean_Elab_Term_withTermInfoContext_x27(v___x_3423_, v_ref_3412_, v___f_3422_, v___x_3424_, v___x_3424_, v___x_3425_, v___x_3425_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v___x_3427_, v_a_3356_);
lean_dec_ref_known(v___x_3427_, 3);
return v___x_3428_;
}
default: 
{
lean_object* v_macroName_3429_; lean_object* v_stx_3430_; lean_object* v_stx_x27_3431_; lean_object* v_nested_3432_; lean_object* v_toCold_3433_; lean_object* v_currRecDepth_3434_; lean_object* v_ref_3435_; uint16_t v_optionFlags_3436_; uint8_t v_suppressElabErrors_3437_; uint8_t v_checkDeprecated_3438_; uint8_t v_isRecordingDeps_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; lean_object* v_ref_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_macroName_3429_ = lean_ctor_get(v_t_3350_, 0);
lean_inc(v_macroName_3429_);
v_stx_3430_ = lean_ctor_get(v_t_3350_, 1);
lean_inc_n(v_stx_3430_, 2);
v_stx_x27_3431_ = lean_ctor_get(v_t_3350_, 2);
lean_inc(v_stx_x27_3431_);
v_nested_3432_ = lean_ctor_get(v_t_3350_, 3);
lean_inc_ref(v_nested_3432_);
lean_dec_ref_known(v_t_3350_, 4);
v_toCold_3433_ = lean_ctor_get(v_a_3355_, 0);
v_currRecDepth_3434_ = lean_ctor_get(v_a_3355_, 1);
v_ref_3435_ = lean_ctor_get(v_a_3355_, 2);
v_optionFlags_3436_ = lean_ctor_get_uint16(v_a_3355_, sizeof(void*)*3);
v_suppressElabErrors_3437_ = lean_ctor_get_uint8(v_a_3355_, sizeof(void*)*3 + 2);
v_checkDeprecated_3438_ = lean_ctor_get_uint8(v_a_3355_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3439_ = lean_ctor_get_uint8(v_a_3355_, sizeof(void*)*3 + 4);
v___x_3440_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___boxed), 8, 1);
lean_closure_set(v___x_3440_, 0, v_nested_3432_);
v___x_3441_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___boxed), 11, 4);
lean_closure_set(v___x_3441_, 0, lean_box(0));
lean_closure_set(v___x_3441_, 1, v_stx_3430_);
lean_closure_set(v___x_3441_, 2, v_stx_x27_3431_);
lean_closure_set(v___x_3441_, 3, v___x_3440_);
v___x_3442_ = lean_box(0);
v___x_3443_ = 0;
v_ref_3444_ = l_Lean_replaceRef(v_stx_3430_, v_ref_3435_);
lean_inc(v_currRecDepth_3434_);
lean_inc_ref(v_toCold_3433_);
v___x_3445_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3445_, 0, v_toCold_3433_);
lean_ctor_set(v___x_3445_, 1, v_currRecDepth_3434_);
lean_ctor_set(v___x_3445_, 2, v_ref_3444_);
lean_ctor_set_uint16(v___x_3445_, sizeof(void*)*3, v_optionFlags_3436_);
lean_ctor_set_uint8(v___x_3445_, sizeof(void*)*3 + 2, v_suppressElabErrors_3437_);
lean_ctor_set_uint8(v___x_3445_, sizeof(void*)*3 + 3, v_checkDeprecated_3438_);
lean_ctor_set_uint8(v___x_3445_, sizeof(void*)*3 + 4, v_isRecordingDeps_3439_);
v___x_3446_ = l_Lean_Elab_Term_withTermInfoContext_x27(v_macroName_3429_, v_stx_3430_, v___x_3441_, v___x_3442_, v___x_3442_, v___x_3443_, v___x_3443_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v___x_3445_, v_a_3356_);
lean_dec_ref_known(v___x_3445_, 3);
return v___x_3446_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1(lean_object* v_arg_3447_, lean_object* v_f_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_arg_3447_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(v_f_3448_, v_a_3457_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
return v___x_3458_;
}
else
{
lean_dec_ref(v_f_3448_);
return v___x_3456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0(lean_object* v_00_u03b1_3459_, lean_object* v_stx_3460_, lean_object* v_output_3461_, lean_object* v_x_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_stx_3460_, v_output_3461_, v_x_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3471_, lean_object* v_stx_3472_, lean_object* v_output_3473_, lean_object* v_x_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0(v_00_u03b1_3471_, v_stx_3472_, v_output_3473_, v_x_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3483_, lean_object* v_x_3484_, lean_object* v_mkInfoTree_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_3484_, v_mkInfoTree_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3494_, lean_object* v_x_3495_, lean_object* v_mkInfoTree_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1(v_00_u03b1_3494_, v_x_3495_, v_mkInfoTree_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(lean_object* v___x_3505_, uint8_t v___x_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
if (lean_obj_tag(v_a_3507_) == 0)
{
lean_object* v___x_3509_; 
lean_dec_ref(v___x_3505_);
v___x_3509_ = l_List_reverse___redArg(v_a_3508_);
return v___x_3509_;
}
else
{
lean_object* v_head_3510_; lean_object* v_tail_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3522_; 
v_head_3510_ = lean_ctor_get(v_a_3507_, 0);
v_tail_3511_ = lean_ctor_get(v_a_3507_, 1);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_a_3507_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3513_ = v_a_3507_;
v_isShared_3514_ = v_isSharedCheck_3522_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_tail_3511_);
lean_inc(v_head_3510_);
lean_dec(v_a_3507_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3522_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v_fst_3515_; uint8_t v___x_3516_; 
v_fst_3515_ = lean_ctor_get(v_head_3510_, 0);
lean_inc(v_fst_3515_);
lean_inc_ref(v___x_3505_);
v___x_3516_ = l_Lean_Environment_contains(v___x_3505_, v_fst_3515_, v___x_3506_);
if (v___x_3516_ == 0)
{
lean_del_object(v___x_3513_);
lean_dec(v_head_3510_);
v_a_3507_ = v_tail_3511_;
goto _start;
}
else
{
lean_object* v___x_3519_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 1, v_a_3508_);
v___x_3519_ = v___x_3513_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_head_3510_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_a_3508_);
v___x_3519_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
v_a_3507_ = v_tail_3511_;
v_a_3508_ = v___x_3519_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0___boxed(lean_object* v___x_3523_, lean_object* v___x_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
uint8_t v___x_5474__boxed_3527_; lean_object* v_res_3528_; 
v___x_5474__boxed_3527_ = lean_unbox(v___x_3524_);
v_res_3528_ = l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(v___x_3523_, v___x_5474__boxed_3527_, v_a_3525_, v_a_3526_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(lean_object* v_className_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v_env_3534_; lean_object* v___y_3536_; lean_object* v___x_3542_; lean_object* v_toEnvExtension_3543_; lean_object* v_asyncMode_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v_defaultInstances_3547_; lean_object* v___x_3548_; 
v___x_3532_ = l_Lean_Meta_instInhabitedDefaultInstances_default;
v___x_3533_ = lean_st_ref_get(v___y_3530_);
v_env_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc_ref_n(v_env_3534_, 2);
lean_dec(v___x_3533_);
v___x_3542_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_3543_ = lean_ctor_get(v___x_3542_, 0);
v_asyncMode_3544_ = lean_ctor_get(v_toEnvExtension_3543_, 2);
v___x_3545_ = lean_box(0);
v___x_3546_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3532_, v___x_3542_, v_env_3534_, v_asyncMode_3544_, v___x_3545_);
v_defaultInstances_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_defaultInstances_3547_);
lean_dec(v___x_3546_);
v___x_3548_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_3547_, v_className_3529_);
lean_dec(v_defaultInstances_3547_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v___x_3549_; 
v___x_3549_ = lean_box(0);
v___y_3536_ = v___x_3549_;
goto v___jp_3535_;
}
else
{
lean_object* v_val_3550_; 
v_val_3550_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_val_3550_);
lean_dec_ref_known(v___x_3548_, 1);
v___y_3536_ = v_val_3550_;
goto v___jp_3535_;
}
v___jp_3535_:
{
uint8_t v_isExporting_3537_; 
v_isExporting_3537_ = lean_ctor_get_uint8(v_env_3534_, sizeof(void*)*13);
if (v_isExporting_3537_ == 0)
{
lean_object* v___x_3538_; 
lean_dec_ref(v_env_3534_);
v___x_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___y_3536_);
return v___x_3538_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_box(0);
v___x_3540_ = l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(v_env_3534_, v_isExporting_3537_, v___y_3536_, v___x_3539_);
v___x_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
return v___x_3541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg___boxed(lean_object* v_className_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec(v_className_3551_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3555_, lean_object* v_declHint_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v_env_3561_; uint8_t v___x_3562_; 
v___x_3559_ = lean_box(0);
v___x_3560_ = lean_st_ref_get(v___y_3557_);
v_env_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc_ref(v_env_3561_);
lean_dec(v___x_3560_);
v___x_3562_ = l_Lean_Name_isAnonymous(v_declHint_3556_);
if (v___x_3562_ == 0)
{
uint8_t v_isExporting_3563_; 
v_isExporting_3563_ = lean_ctor_get_uint8(v_env_3561_, sizeof(void*)*13);
if (v_isExporting_3563_ == 0)
{
lean_object* v___x_3564_; 
lean_dec_ref(v_env_3561_);
lean_dec(v_declHint_3556_);
v___x_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3564_, 0, v_msg_3555_);
return v___x_3564_;
}
else
{
lean_object* v___x_3565_; uint8_t v___x_3566_; 
lean_inc_ref(v_env_3561_);
v___x_3565_ = l_Lean_Environment_setExporting(v_env_3561_, v___x_3562_);
lean_inc(v_declHint_3556_);
lean_inc_ref(v___x_3565_);
v___x_3566_ = l_Lean_Environment_contains(v___x_3565_, v_declHint_3556_, v_isExporting_3563_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; 
lean_dec_ref(v___x_3565_);
lean_dec_ref(v_env_3561_);
lean_dec(v_declHint_3556_);
v___x_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3567_, 0, v_msg_3555_);
return v___x_3567_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v_c_3575_; lean_object* v___x_3576_; 
v___x_3568_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3569_ = lean_unsigned_to_nat(32u);
v___x_3570_ = lean_mk_empty_array_with_capacity(v___x_3569_);
lean_dec_ref(v___x_3570_);
v___x_3571_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5);
v___x_3572_ = l_Lean_Options_empty;
lean_inc_ref(v___x_3565_);
v___x_3573_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3565_);
lean_ctor_set(v___x_3573_, 1, v___x_3568_);
lean_ctor_set(v___x_3573_, 2, v___x_3571_);
lean_ctor_set(v___x_3573_, 3, v___x_3572_);
lean_inc(v_declHint_3556_);
v___x_3574_ = l_Lean_MessageData_ofConstName(v_declHint_3556_, v___x_3562_);
v_c_3575_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3575_, 0, v___x_3573_);
lean_ctor_set(v_c_3575_, 1, v___x_3574_);
v___x_3576_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3565_, v_declHint_3556_);
lean_dec_ref(v___x_3565_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec_ref(v_env_3561_);
lean_dec(v_declHint_3556_);
v___x_3577_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v_c_3575_);
v___x_3579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9);
v___x_3580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = l_Lean_MessageData_note(v___x_3580_);
v___x_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3582_, 0, v_msg_3555_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
return v___x_3583_;
}
else
{
lean_object* v_val_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3618_; 
v_val_3584_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3586_ = v___x_3576_;
v_isShared_3587_ = v_isSharedCheck_3618_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_val_3584_);
lean_dec(v___x_3576_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3618_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v_moduleNames_3589_; lean_object* v_mod_3590_; uint8_t v___x_3591_; 
v___x_3588_ = l_Lean_Environment_header(v_env_3561_);
lean_dec_ref(v_env_3561_);
v_moduleNames_3589_ = lean_ctor_get(v___x_3588_, 4);
lean_inc_ref(v_moduleNames_3589_);
lean_dec_ref(v___x_3588_);
v_mod_3590_ = lean_array_get(v___x_3559_, v_moduleNames_3589_, v_val_3584_);
lean_dec(v_val_3584_);
lean_dec_ref(v_moduleNames_3589_);
v___x_3591_ = l_Lean_isPrivateName(v_declHint_3556_);
lean_dec(v_declHint_3556_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11);
v___x_3593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set(v___x_3593_, 1, v_c_3575_);
v___x_3594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13);
v___x_3595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3593_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
v___x_3596_ = l_Lean_MessageData_ofName(v_mod_3590_);
v___x_3597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15);
v___x_3599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = l_Lean_MessageData_note(v___x_3599_);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v_msg_3555_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3601_);
v___x_3603_ = v___x_3586_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
else
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3616_; 
v___x_3605_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v_c_3575_);
v___x_3607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = l_Lean_MessageData_ofName(v_mod_3590_);
v___x_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19);
v___x_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = l_Lean_MessageData_note(v___x_3612_);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v_msg_3555_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3614_);
v___x_3616_ = v___x_3586_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3619_; 
lean_dec_ref(v_env_3561_);
lean_dec(v_declHint_3556_);
v___x_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3619_, 0, v_msg_3555_);
return v___x_3619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3620_, lean_object* v_declHint_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3620_, v_declHint_3621_, v___y_3622_);
lean_dec(v___y_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_msg_3625_, lean_object* v_declHint_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3642_; 
v___x_3632_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3625_, v_declHint_3626_, v___y_3630_);
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3642_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3642_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3640_; 
v___x_3637_ = l_Lean_unknownIdentifierMessageTag;
v___x_3638_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
lean_ctor_set(v___x_3638_, 1, v_a_3633_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3638_);
v___x_3640_ = v___x_3635_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3643_, lean_object* v_declHint_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_3643_, v_declHint_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v_ref_3657_; lean_object* v___x_3658_; lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3667_; 
v_ref_3657_ = lean_ctor_get(v___y_3654_, 2);
v___x_3658_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3667_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3667_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v___x_3665_; 
lean_inc(v_ref_3657_);
v___x_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3663_, 0, v_ref_3657_);
lean_ctor_set(v___x_3663_, 1, v_a_3659_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 1);
lean_ctor_set(v___x_3661_, 0, v___x_3663_);
v___x_3665_ = v___x_3661_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_3675_, lean_object* v_msg_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v_toCold_3682_; lean_object* v_currRecDepth_3683_; lean_object* v_ref_3684_; uint16_t v_optionFlags_3685_; uint8_t v_suppressElabErrors_3686_; uint8_t v_checkDeprecated_3687_; uint8_t v_isRecordingDeps_3688_; lean_object* v_ref_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_toCold_3682_ = lean_ctor_get(v___y_3679_, 0);
v_currRecDepth_3683_ = lean_ctor_get(v___y_3679_, 1);
v_ref_3684_ = lean_ctor_get(v___y_3679_, 2);
v_optionFlags_3685_ = lean_ctor_get_uint16(v___y_3679_, sizeof(void*)*3);
v_suppressElabErrors_3686_ = lean_ctor_get_uint8(v___y_3679_, sizeof(void*)*3 + 2);
v_checkDeprecated_3687_ = lean_ctor_get_uint8(v___y_3679_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3688_ = lean_ctor_get_uint8(v___y_3679_, sizeof(void*)*3 + 4);
v_ref_3689_ = l_Lean_replaceRef(v_ref_3675_, v_ref_3684_);
lean_inc(v_currRecDepth_3683_);
lean_inc_ref(v_toCold_3682_);
v___x_3690_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3690_, 0, v_toCold_3682_);
lean_ctor_set(v___x_3690_, 1, v_currRecDepth_3683_);
lean_ctor_set(v___x_3690_, 2, v_ref_3689_);
lean_ctor_set_uint16(v___x_3690_, sizeof(void*)*3, v_optionFlags_3685_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*3 + 2, v_suppressElabErrors_3686_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*3 + 3, v_checkDeprecated_3687_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*3 + 4, v_isRecordingDeps_3688_);
v___x_3691_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3676_, v___y_3677_, v___y_3678_, v___x_3690_, v___y_3680_);
lean_dec_ref_known(v___x_3690_, 3);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3692_, lean_object* v_msg_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3692_, v_msg_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v_ref_3692_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_3700_, lean_object* v_msg_3701_, lean_object* v_declHint_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; lean_object* v_a_3709_; lean_object* v___x_3710_; 
v___x_3708_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_3701_, v_declHint_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref(v___x_3708_);
v___x_3710_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3700_, v_a_3709_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3711_, lean_object* v_msg_3712_, lean_object* v_declHint_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3711_, v_msg_3712_, v_declHint_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v_ref_3711_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_3720_, lean_object* v_constName_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3727_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1);
v___x_3728_ = 0;
lean_inc(v_constName_3721_);
v___x_3729_ = l_Lean_MessageData_ofConstName(v_constName_3721_, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3727_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3);
v___x_3732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3720_, v___x_3732_, v_constName_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_3734_, lean_object* v_constName_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3734_, v_constName_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v_ref_3734_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(lean_object* v_constName_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_ref_3748_; lean_object* v___x_3749_; 
v_ref_3748_ = lean_ctor_get(v___y_3745_, 2);
v___x_3749_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3748_, v_constName_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(lean_object* v_constName_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v___x_3763_; lean_object* v_env_3764_; uint8_t v___x_3765_; lean_object* v___x_3766_; 
v___x_3763_ = lean_st_ref_get(v___y_3761_);
v_env_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc_ref(v_env_3764_);
lean_dec(v___x_3763_);
v___x_3765_ = 0;
lean_inc(v_constName_3757_);
v___x_3766_ = l_Lean_Environment_find_x3f(v_env_3764_, v_constName_3757_, v___x_3765_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
return v___x_3767_;
}
else
{
lean_object* v_val_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec(v_constName_3757_);
v_val_3768_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3766_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_val_3768_);
lean_dec(v___x_3766_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set_tag(v___x_3770_, 0);
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_val_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1___boxed(lean_object* v_constName_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(v_constName_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(lean_object* v_declName_3786_, uint8_t v_lhs_3787_, lean_object* v___x_3788_, lean_object* v_as_x27_3789_, lean_object* v_b_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
if (lean_obj_tag(v_as_x27_3789_) == 0)
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3796_, 0, v_b_3790_);
return v___x_3796_;
}
else
{
lean_object* v_head_3797_; lean_object* v_tail_3798_; lean_object* v_fst_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; uint8_t v___x_3803_; lean_object* v___x_3804_; 
lean_dec_ref(v_b_3790_);
v_head_3797_ = lean_ctor_get(v_as_x27_3789_, 0);
v_tail_3798_ = lean_ctor_get(v_as_x27_3789_, 1);
v_fst_3799_ = lean_ctor_get(v_head_3797_, 0);
v___x_3800_ = lean_box(0);
v___x_3801_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0));
v___x_3802_ = lean_unsigned_to_nat(1u);
v___x_3803_ = lean_nat_dec_le(v___x_3788_, v___x_3802_);
lean_inc(v_fst_3799_);
v___x_3804_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(v_fst_3799_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3837_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3837_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3837_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = l_Lean_ConstantInfo_type(v_a_3805_);
lean_dec(v_a_3805_);
v___x_3810_ = l_Lean_Expr_getForallBody(v___x_3809_);
lean_dec_ref(v___x_3809_);
if (lean_obj_tag(v___x_3810_) == 5)
{
lean_object* v_fn_3811_; 
v_fn_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc_ref(v_fn_3811_);
lean_dec_ref_known(v___x_3810_, 2);
if (lean_obj_tag(v_fn_3811_) == 5)
{
lean_object* v_fn_3812_; 
v_fn_3812_ = lean_ctor_get(v_fn_3811_, 0);
lean_inc_ref(v_fn_3812_);
if (lean_obj_tag(v_fn_3812_) == 5)
{
lean_object* v_arg_3813_; lean_object* v_arg_3814_; uint8_t v___y_3816_; uint8_t v___y_3826_; 
v_arg_3813_ = lean_ctor_get(v_fn_3811_, 1);
lean_inc_ref(v_arg_3813_);
lean_dec_ref_known(v_fn_3811_, 2);
v_arg_3814_ = lean_ctor_get(v_fn_3812_, 1);
lean_inc_ref(v_arg_3814_);
lean_dec_ref_known(v_fn_3812_, 2);
if (v_lhs_3787_ == 0)
{
lean_dec_ref(v_arg_3813_);
v___y_3826_ = v___x_3803_;
goto v___jp_3825_;
}
else
{
uint8_t v___x_3829_; 
v___x_3829_ = l_Lean_Expr_isAppOf(v_arg_3813_, v_declName_3786_);
lean_dec_ref(v_arg_3813_);
if (v___x_3829_ == 0)
{
v___y_3826_ = v___x_3829_;
goto v___jp_3825_;
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_dec_ref(v_arg_3814_);
lean_del_object(v___x_3807_);
v___x_3830_ = lean_box(v_lhs_3787_);
v___x_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
v___x_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
lean_ctor_set(v___x_3832_, 1, v___x_3800_);
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
return v___x_3833_;
}
}
v___jp_3815_:
{
uint8_t v___x_3817_; 
v___x_3817_ = l_Lean_Expr_isAppOf(v_arg_3814_, v_declName_3786_);
lean_dec_ref(v_arg_3814_);
if (v___x_3817_ == 0)
{
lean_del_object(v___x_3807_);
v_as_x27_3789_ = v_tail_3798_;
v_b_3790_ = v___x_3801_;
goto _start;
}
else
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3819_ = lean_box(v___y_3816_);
v___x_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
lean_ctor_set(v___x_3821_, 1, v___x_3800_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3821_);
v___x_3823_ = v___x_3807_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
v___jp_3825_:
{
uint8_t v___x_3827_; 
v___x_3827_ = 1;
if (v_lhs_3787_ == 0)
{
v___y_3816_ = v___x_3827_;
goto v___jp_3815_;
}
else
{
if (v___y_3826_ == 0)
{
lean_dec_ref(v_arg_3814_);
lean_del_object(v___x_3807_);
v_as_x27_3789_ = v_tail_3798_;
v_b_3790_ = v___x_3801_;
goto _start;
}
else
{
v___y_3816_ = v___x_3827_;
goto v___jp_3815_;
}
}
}
}
else
{
lean_dec_ref_known(v_fn_3811_, 2);
lean_dec_ref(v_fn_3812_);
lean_del_object(v___x_3807_);
v_as_x27_3789_ = v_tail_3798_;
v_b_3790_ = v___x_3801_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_3811_);
lean_del_object(v___x_3807_);
v_as_x27_3789_ = v_tail_3798_;
v_b_3790_ = v___x_3801_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_3810_);
lean_del_object(v___x_3807_);
v_as_x27_3789_ = v_tail_3798_;
v_b_3790_ = v___x_3801_;
goto _start;
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
v_a_3838_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3804_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3804_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___boxed(lean_object* v_declName_3846_, lean_object* v_lhs_3847_, lean_object* v___x_3848_, lean_object* v_as_x27_3849_, lean_object* v_b_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
uint8_t v_lhs_boxed_3856_; lean_object* v_res_3857_; 
v_lhs_boxed_3856_ = lean_unbox(v_lhs_3847_);
v_res_3857_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3846_, v_lhs_boxed_3856_, v___x_3848_, v_as_x27_3849_, v_b_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v_as_x27_3849_);
lean_dec(v___x_3848_);
lean_dec(v_declName_3846_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(lean_object* v_f_3858_, lean_object* v_maxType_3859_, uint8_t v_lhs_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
if (lean_obj_tag(v_f_3858_) == 4)
{
lean_object* v_declName_3866_; lean_object* v___x_3867_; 
v_declName_3866_ = lean_ctor_get(v_f_3858_, 0);
v___x_3867_ = l_Lean_Expr_getAppFn(v_maxType_3859_);
if (lean_obj_tag(v___x_3867_) == 4)
{
lean_object* v_declName_3868_; lean_object* v_className_3869_; lean_object* v___x_3870_; lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3907_; 
v_declName_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_declName_3868_);
lean_dec_ref_known(v___x_3867_, 2);
v_className_3869_ = l_Lean_Name_getPrefix(v_declName_3866_);
v___x_3870_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3869_, v_a_3864_);
lean_dec(v_className_3869_);
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3873_ = v___x_3870_;
v_isShared_3874_ = v_isSharedCheck_3907_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3870_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3907_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3875_ = l_List_lengthTR___redArg(v_a_3871_);
v___x_3876_ = lean_unsigned_to_nat(1u);
v___x_3877_ = lean_nat_dec_le(v___x_3875_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_del_object(v___x_3873_);
v___x_3878_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0));
v___x_3879_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3868_, v_lhs_3860_, v___x_3875_, v_a_3871_, v___x_3878_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
lean_dec(v_a_3871_);
lean_dec(v___x_3875_);
lean_dec(v_declName_3868_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3893_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3882_ = v___x_3879_;
v_isShared_3883_ = v_isSharedCheck_3893_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3893_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v_fst_3884_; 
v_fst_3884_ = lean_ctor_get(v_a_3880_, 0);
lean_inc(v_fst_3884_);
lean_dec(v_a_3880_);
if (lean_obj_tag(v_fst_3884_) == 0)
{
lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3885_ = lean_box(v___x_3877_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v___x_3885_);
v___x_3887_ = v___x_3882_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
else
{
lean_object* v_val_3889_; lean_object* v___x_3891_; 
v_val_3889_ = lean_ctor_get(v_fst_3884_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v_fst_3884_, 1);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v_val_3889_);
v___x_3891_ = v___x_3882_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_val_3889_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
else
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
v_a_3894_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3879_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3879_);
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
else
{
uint8_t v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
lean_dec(v___x_3875_);
lean_dec(v_a_3871_);
lean_dec(v_declName_3868_);
v___x_3902_ = 0;
v___x_3903_ = lean_box(v___x_3902_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 0, v___x_3903_);
v___x_3905_ = v___x_3873_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
else
{
uint8_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
lean_dec_ref(v___x_3867_);
v___x_3908_ = 0;
v___x_3909_ = lean_box(v___x_3908_);
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
return v___x_3910_;
}
}
else
{
uint8_t v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3911_ = 0;
v___x_3912_ = lean_box(v___x_3911_);
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
return v___x_3913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances___boxed(lean_object* v_f_3914_, lean_object* v_maxType_3915_, lean_object* v_lhs_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_){
_start:
{
uint8_t v_lhs_boxed_3922_; lean_object* v_res_3923_; 
v_lhs_boxed_3922_ = lean_unbox(v_lhs_3916_);
v_res_3923_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(v_f_3914_, v_maxType_3915_, v_lhs_boxed_3922_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec(v_a_3918_);
lean_dec_ref(v_a_3917_);
lean_dec_ref(v_maxType_3915_);
lean_dec_ref(v_f_3914_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0(lean_object* v_className_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3924_, v___y_3928_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___boxed(lean_object* v_className_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0(v_className_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v_className_3931_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2(lean_object* v_declName_3938_, uint8_t v_lhs_3939_, lean_object* v___x_3940_, lean_object* v_as_3941_, lean_object* v_as_x27_3942_, lean_object* v_b_3943_, lean_object* v_a_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3938_, v_lhs_3939_, v___x_3940_, v_as_x27_3942_, v_b_3943_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___boxed(lean_object* v_declName_3951_, lean_object* v_lhs_3952_, lean_object* v___x_3953_, lean_object* v_as_3954_, lean_object* v_as_x27_3955_, lean_object* v_b_3956_, lean_object* v_a_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
uint8_t v_lhs_boxed_3963_; lean_object* v_res_3964_; 
v_lhs_boxed_3963_ = lean_unbox(v_lhs_3952_);
v_res_3964_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2(v_declName_3951_, v_lhs_boxed_3963_, v___x_3953_, v_as_3954_, v_as_x27_3955_, v_b_3956_, v_a_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v_as_x27_3955_);
lean_dec(v_as_3954_);
lean_dec(v___x_3953_);
lean_dec(v_declName_3951_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2(lean_object* v_00_u03b1_3965_, lean_object* v_constName_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3973_, lean_object* v_constName_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2(v_00_u03b1_3973_, v_constName_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_3981_, lean_object* v_ref_3982_, lean_object* v_constName_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3982_, v_constName_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3990_, lean_object* v_ref_3991_, lean_object* v_constName_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3(v_00_u03b1_3990_, v_ref_3991_, v_constName_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v_ref_3991_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_3999_, lean_object* v_ref_4000_, lean_object* v_msg_4001_, lean_object* v_declHint_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_4000_, v_msg_4001_, v_declHint_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4009_, lean_object* v_ref_4010_, lean_object* v_msg_4011_, lean_object* v_declHint_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_4009_, v_ref_4010_, v_msg_4011_, v_declHint_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v_ref_4010_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_4019_, lean_object* v_declHint_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_4019_, v_declHint_4020_, v___y_4024_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_4027_, lean_object* v_declHint_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_4027_, v_declHint_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_4035_, lean_object* v_ref_4036_, lean_object* v_msg_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_4036_, v_msg_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4044_, lean_object* v_ref_4045_, lean_object* v_msg_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_4044_, v_ref_4045_, v_msg_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v_ref_4045_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_4053_, lean_object* v_msg_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4061_, lean_object* v_msg_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_4061_, v_msg_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(lean_object* v_f_4069_, lean_object* v_maxType_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v_a_4077_; 
if (lean_obj_tag(v_f_4069_) == 4)
{
lean_object* v_declName_4084_; lean_object* v_className_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v_declName_4084_ = lean_ctor_get(v_f_4069_, 0);
v_className_4085_ = l_Lean_Name_getPrefix(v_declName_4084_);
v___x_4086_ = lean_unsigned_to_nat(3u);
v___x_4087_ = lean_mk_empty_array_with_capacity(v___x_4086_);
lean_inc_ref_n(v_maxType_4070_, 2);
v___x_4088_ = lean_array_push(v___x_4087_, v_maxType_4070_);
v___x_4089_ = lean_array_push(v___x_4088_, v_maxType_4070_);
v___x_4090_ = lean_array_push(v___x_4089_, v_maxType_4070_);
v___x_4091_ = l_Lean_Meta_mkAppM(v_className_4085_, v___x_4090_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref_known(v___x_4091_, 1);
v___x_4093_ = lean_box(0);
v___x_4094_ = l_Lean_Meta_trySynthInstance(v_a_4092_, v___x_4093_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4109_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4097_ = v___x_4094_;
v_isShared_4098_ = v_isSharedCheck_4109_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4094_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4109_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
if (lean_obj_tag(v_a_4095_) == 1)
{
uint8_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4102_; 
lean_dec_ref_known(v_a_4095_, 1);
v___x_4099_ = 1;
v___x_4100_ = lean_box(v___x_4099_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4100_);
v___x_4102_ = v___x_4097_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4100_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
else
{
uint8_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4107_; 
lean_dec(v_a_4095_);
v___x_4104_ = 0;
v___x_4105_ = lean_box(v___x_4104_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4105_);
v___x_4107_ = v___x_4097_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
else
{
lean_object* v_a_4110_; 
v_a_4110_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4094_, 1);
v_a_4077_ = v_a_4110_;
goto v___jp_4076_;
}
}
else
{
lean_object* v_a_4111_; 
v_a_4111_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4111_);
lean_dec_ref_known(v___x_4091_, 1);
v_a_4077_ = v_a_4111_;
goto v___jp_4076_;
}
}
else
{
uint8_t v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
lean_dec_ref(v_maxType_4070_);
v___x_4112_ = 0;
v___x_4113_ = lean_box(v___x_4112_);
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
return v___x_4114_;
}
v___jp_4076_:
{
uint8_t v___x_4078_; 
v___x_4078_ = l_Lean_Exception_isInterrupt(v_a_4077_);
if (v___x_4078_ == 0)
{
uint8_t v___x_4079_; 
lean_inc_ref(v_a_4077_);
v___x_4079_ = l_Lean_Exception_isRuntime(v_a_4077_);
if (v___x_4079_ == 0)
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
lean_dec_ref(v_a_4077_);
v___x_4080_ = lean_box(v___x_4079_);
v___x_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
return v___x_4081_;
}
else
{
lean_object* v___x_4082_; 
v___x_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4082_, 0, v_a_4077_);
return v___x_4082_;
}
}
else
{
lean_object* v___x_4083_; 
v___x_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4083_, 0, v_a_4077_);
return v___x_4083_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance___boxed(lean_object* v_f_4115_, lean_object* v_maxType_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(v_f_4115_, v_maxType_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
lean_dec(v_a_4118_);
lean_dec_ref(v_a_4117_);
lean_dec_ref(v_f_4115_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(lean_object* v_cls_4123_, lean_object* v_msg_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_ref_4130_; lean_object* v___x_4131_; lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4177_; 
v_ref_4130_ = lean_ctor_get(v___y_4127_, 2);
v___x_4131_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4134_ = v___x_4131_;
v_isShared_4135_ = v_isSharedCheck_4177_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4131_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4177_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v_traceState_4137_; lean_object* v_env_4138_; lean_object* v_nextMacroScope_4139_; lean_object* v_ngen_4140_; lean_object* v_auxDeclNGen_4141_; lean_object* v_cache_4142_; lean_object* v_recordedDeps_4143_; lean_object* v_messages_4144_; lean_object* v_infoState_4145_; lean_object* v_snapshotTasks_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4176_; 
v___x_4136_ = lean_st_ref_take(v___y_4128_);
v_traceState_4137_ = lean_ctor_get(v___x_4136_, 4);
v_env_4138_ = lean_ctor_get(v___x_4136_, 0);
v_nextMacroScope_4139_ = lean_ctor_get(v___x_4136_, 1);
v_ngen_4140_ = lean_ctor_get(v___x_4136_, 2);
v_auxDeclNGen_4141_ = lean_ctor_get(v___x_4136_, 3);
v_cache_4142_ = lean_ctor_get(v___x_4136_, 5);
v_recordedDeps_4143_ = lean_ctor_get(v___x_4136_, 6);
v_messages_4144_ = lean_ctor_get(v___x_4136_, 7);
v_infoState_4145_ = lean_ctor_get(v___x_4136_, 8);
v_snapshotTasks_4146_ = lean_ctor_get(v___x_4136_, 9);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4148_ = v___x_4136_;
v_isShared_4149_ = v_isSharedCheck_4176_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_snapshotTasks_4146_);
lean_inc(v_infoState_4145_);
lean_inc(v_messages_4144_);
lean_inc(v_recordedDeps_4143_);
lean_inc(v_cache_4142_);
lean_inc(v_traceState_4137_);
lean_inc(v_auxDeclNGen_4141_);
lean_inc(v_ngen_4140_);
lean_inc(v_nextMacroScope_4139_);
lean_inc(v_env_4138_);
lean_dec(v___x_4136_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4176_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
uint64_t v_tid_4150_; lean_object* v_traces_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4175_; 
v_tid_4150_ = lean_ctor_get_uint64(v_traceState_4137_, sizeof(void*)*1);
v_traces_4151_ = lean_ctor_get(v_traceState_4137_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_traceState_4137_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4153_ = v_traceState_4137_;
v_isShared_4154_ = v_isSharedCheck_4175_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_traces_4151_);
lean_dec(v_traceState_4137_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4175_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; double v___x_4157_; uint8_t v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4155_ = lean_box(0);
v___x_4156_ = lean_box(0);
v___x_4157_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0);
v___x_4158_ = 0;
v___x_4159_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1));
v___x_4160_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4160_, 0, v_cls_4123_);
lean_ctor_set(v___x_4160_, 1, v___x_4156_);
lean_ctor_set(v___x_4160_, 2, v___x_4159_);
lean_ctor_set_float(v___x_4160_, sizeof(void*)*3, v___x_4157_);
lean_ctor_set_float(v___x_4160_, sizeof(void*)*3 + 8, v___x_4157_);
lean_ctor_set_uint8(v___x_4160_, sizeof(void*)*3 + 16, v___x_4158_);
v___x_4161_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2));
v___x_4162_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4160_);
lean_ctor_set(v___x_4162_, 1, v_a_4132_);
lean_ctor_set(v___x_4162_, 2, v___x_4161_);
lean_inc(v_ref_4130_);
v___x_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4163_, 0, v_ref_4130_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = l_Lean_PersistentArray_push___redArg(v_traces_4151_, v___x_4163_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v___x_4164_);
v___x_4166_ = v___x_4153_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4164_);
lean_ctor_set_uint64(v_reuseFailAlloc_4174_, sizeof(void*)*1, v_tid_4150_);
v___x_4166_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4168_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 4, v___x_4166_);
v___x_4168_ = v___x_4148_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_env_4138_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_nextMacroScope_4139_);
lean_ctor_set(v_reuseFailAlloc_4173_, 2, v_ngen_4140_);
lean_ctor_set(v_reuseFailAlloc_4173_, 3, v_auxDeclNGen_4141_);
lean_ctor_set(v_reuseFailAlloc_4173_, 4, v___x_4166_);
lean_ctor_set(v_reuseFailAlloc_4173_, 5, v_cache_4142_);
lean_ctor_set(v_reuseFailAlloc_4173_, 6, v_recordedDeps_4143_);
lean_ctor_set(v_reuseFailAlloc_4173_, 7, v_messages_4144_);
lean_ctor_set(v_reuseFailAlloc_4173_, 8, v_infoState_4145_);
lean_ctor_set(v_reuseFailAlloc_4173_, 9, v_snapshotTasks_4146_);
v___x_4168_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
lean_object* v___x_4169_; lean_object* v___x_4171_; 
v___x_4169_ = lean_st_ref_put(v___y_4128_, v___x_4168_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v___x_4155_);
v___x_4171_ = v___x_4134_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___x_4155_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg___boxed(lean_object* v_cls_4178_, lean_object* v_msg_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v_cls_4178_, v_msg_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
return v_res_4185_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__0));
v___x_4188_ = l_Lean_stringToMessageData(v___x_4187_);
return v___x_4188_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__2));
v___x_4191_ = l_Lean_stringToMessageData(v___x_4190_);
return v___x_4191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5(void){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__4));
v___x_4194_ = l_Lean_stringToMessageData(v___x_4193_);
return v___x_4194_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7(void){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__6));
v___x_4197_ = l_Lean_stringToMessageData(v___x_4196_);
return v___x_4197_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__8));
v___x_4200_ = l_Lean_stringToMessageData(v___x_4199_);
return v___x_4200_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__0));
v___x_4203_ = l_Lean_stringToMessageData(v___x_4202_);
return v___x_4203_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__2));
v___x_4206_ = l_Lean_stringToMessageData(v___x_4205_);
return v___x_4206_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__5));
v___x_4211_ = l_Lean_MessageData_ofFormat(v___x_4210_);
return v___x_4211_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__7));
v___x_4214_ = l_Lean_stringToMessageData(v___x_4213_);
return v___x_4214_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10(void){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4216_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__9));
v___x_4217_ = l_Lean_stringToMessageData(v___x_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(lean_object* v_tree_4220_, lean_object* v_expectedType_x3f_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_){
_start:
{
lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___x_4250_; 
lean_inc(v_expectedType_x3f_4221_);
lean_inc_ref(v_tree_4220_);
v___x_4250_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v_tree_4220_, v_expectedType_x3f_4221_, v_a_4222_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_toCold_4251_; lean_object* v_options_4252_; lean_object* v_a_4253_; lean_object* v_inheritedTraceOptions_4254_; uint8_t v_hasTrace_4255_; lean_object* v___x_4256_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4319_; lean_object* v___y_4320_; 
v_toCold_4251_ = lean_ctor_get(v_a_4226_, 0);
v_options_4252_ = lean_ctor_get(v_toCold_4251_, 2);
v_a_4253_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4253_);
lean_dec_ref_known(v___x_4250_, 1);
v_inheritedTraceOptions_4254_ = lean_ctor_get(v_toCold_4251_, 11);
v_hasTrace_4255_ = lean_ctor_get_uint8(v_options_4252_, sizeof(void*)*1);
v___x_4256_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
if (v_hasTrace_4255_ == 0)
{
v___y_4284_ = v_a_4222_;
v___y_4285_ = v_a_4223_;
v___y_4286_ = v_a_4224_;
v___y_4287_ = v_a_4225_;
v___y_4288_ = v_a_4226_;
v___y_4289_ = v_a_4227_;
goto v___jp_4283_;
}
else
{
lean_object* v___x_4331_; uint8_t v___x_4332_; 
v___x_4331_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4332_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4254_, v_options_4252_, v___x_4331_);
if (v___x_4332_ == 0)
{
v___y_4284_ = v_a_4222_;
v___y_4285_ = v_a_4223_;
v___y_4286_ = v_a_4224_;
v___y_4287_ = v_a_4225_;
v___y_4288_ = v_a_4226_;
v___y_4289_ = v_a_4227_;
goto v___jp_4283_;
}
else
{
lean_object* v_max_x3f_4333_; uint8_t v_hasUncomparable_4334_; uint8_t v_hasUnknown_4335_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___x_4347_; lean_object* v___y_4349_; 
v_max_x3f_4333_ = lean_ctor_get(v_a_4253_, 0);
v_hasUncomparable_4334_ = lean_ctor_get_uint8(v_a_4253_, sizeof(void*)*1);
v_hasUnknown_4335_ = lean_ctor_get_uint8(v_a_4253_, sizeof(void*)*1 + 1);
v___x_4347_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8);
if (v_hasUncomparable_4334_ == 0)
{
lean_object* v___x_4357_; 
v___x_4357_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_4349_ = v___x_4357_;
goto v___jp_4348_;
}
else
{
lean_object* v___x_4358_; 
v___x_4358_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_4349_ = v___x_4358_;
goto v___jp_4348_;
}
v___jp_4336_:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
lean_inc_ref(v___y_4338_);
v___x_4339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4339_, 0, v___y_4338_);
v___x_4340_ = l_Lean_MessageData_ofFormat(v___x_4339_);
v___x_4341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___y_4337_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
v___x_4342_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3);
v___x_4343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4341_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
if (lean_obj_tag(v_max_x3f_4333_) == 0)
{
lean_object* v___x_4344_; 
v___x_4344_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6);
v___y_4319_ = v___x_4343_;
v___y_4320_ = v___x_4344_;
goto v___jp_4318_;
}
else
{
lean_object* v_val_4345_; lean_object* v___x_4346_; 
v_val_4345_ = lean_ctor_get(v_max_x3f_4333_, 0);
lean_inc(v_val_4345_);
v___x_4346_ = l_Lean_MessageData_ofExpr(v_val_4345_);
v___y_4319_ = v___x_4343_;
v___y_4320_ = v___x_4346_;
goto v___jp_4318_;
}
}
v___jp_4348_:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
lean_inc_ref(v___y_4349_);
v___x_4350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4350_, 0, v___y_4349_);
v___x_4351_ = l_Lean_MessageData_ofFormat(v___x_4350_);
v___x_4352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4347_);
lean_ctor_set(v___x_4352_, 1, v___x_4351_);
v___x_4353_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10);
v___x_4354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4352_);
lean_ctor_set(v___x_4354_, 1, v___x_4353_);
if (v_hasUnknown_4335_ == 0)
{
lean_object* v___x_4355_; 
v___x_4355_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_4337_ = v___x_4354_;
v___y_4338_ = v___x_4355_;
goto v___jp_4336_;
}
else
{
lean_object* v___x_4356_; 
v___x_4356_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_4337_ = v___x_4354_;
v___y_4338_ = v___x_4356_;
goto v___jp_4336_;
}
}
}
}
v___jp_4257_:
{
lean_object* v_toCold_4265_; lean_object* v_options_4266_; uint8_t v_hasTrace_4267_; 
v_toCold_4265_ = lean_ctor_get(v___y_4263_, 0);
v_options_4266_ = lean_ctor_get(v_toCold_4265_, 2);
v_hasTrace_4267_ = lean_ctor_get_uint8(v_options_4266_, sizeof(void*)*1);
if (v_hasTrace_4267_ == 0)
{
v___y_4241_ = v___y_4258_;
v___y_4242_ = v___y_4259_;
v___y_4243_ = v___y_4260_;
v___y_4244_ = v___y_4261_;
v___y_4245_ = v___y_4262_;
v___y_4246_ = v___y_4263_;
v___y_4247_ = v___y_4264_;
goto v___jp_4240_;
}
else
{
lean_object* v_inheritedTraceOptions_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v_inheritedTraceOptions_4268_ = lean_ctor_get(v_toCold_4265_, 11);
v___x_4269_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4270_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4268_, v_options_4266_, v___x_4269_);
if (v___x_4270_ == 0)
{
v___y_4241_ = v___y_4258_;
v___y_4242_ = v___y_4259_;
v___y_4243_ = v___y_4260_;
v___y_4244_ = v___y_4261_;
v___y_4245_ = v___y_4262_;
v___y_4246_ = v___y_4263_;
v___y_4247_ = v___y_4264_;
goto v___jp_4240_;
}
else
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4271_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1);
lean_inc_ref(v___y_4258_);
v___x_4272_ = l_Lean_MessageData_ofExpr(v___y_4258_);
v___x_4273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4271_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4256_, v___x_4273_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_dec_ref_known(v___x_4274_, 1);
v___y_4241_ = v___y_4258_;
v___y_4242_ = v___y_4259_;
v___y_4243_ = v___y_4260_;
v___y_4244_ = v___y_4261_;
v___y_4245_ = v___y_4262_;
v___y_4246_ = v___y_4263_;
v___y_4247_ = v___y_4264_;
goto v___jp_4240_;
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec_ref(v___y_4258_);
lean_dec(v_expectedType_x3f_4221_);
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4274_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4274_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
}
}
v___jp_4283_:
{
uint8_t v_hasUncomparable_4290_; 
v_hasUncomparable_4290_ = lean_ctor_get_uint8(v_a_4253_, sizeof(void*)*1);
if (v_hasUncomparable_4290_ == 0)
{
lean_object* v_max_x3f_4291_; 
v_max_x3f_4291_ = lean_ctor_get(v_a_4253_, 0);
lean_inc(v_max_x3f_4291_);
if (lean_obj_tag(v_max_x3f_4291_) == 0)
{
lean_dec(v_a_4253_);
v___y_4230_ = v___y_4288_;
v___y_4231_ = v___y_4287_;
v___y_4232_ = v___y_4284_;
v___y_4233_ = v___y_4289_;
v___y_4234_ = v___y_4286_;
v___y_4235_ = v___y_4285_;
goto v___jp_4229_;
}
else
{
uint8_t v_hasUnknown_4292_; lean_object* v_val_4293_; lean_object* v___x_4294_; 
v_hasUnknown_4292_ = lean_ctor_get_uint8(v_a_4253_, sizeof(void*)*1 + 1);
lean_dec(v_a_4253_);
v_val_4293_ = lean_ctor_get(v_max_x3f_4291_, 0);
lean_inc_n(v_val_4293_, 2);
lean_dec_ref_known(v_max_x3f_4291_, 1);
v___x_4294_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v_tree_4220_, v_val_4293_, v_hasUncomparable_4290_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4296_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
lean_inc(v_a_4295_);
lean_dec_ref_known(v___x_4294_, 1);
v___x_4296_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_4295_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4296_) == 0)
{
if (v_hasUnknown_4292_ == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4298_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc_n(v_a_4297_, 2);
lean_dec_ref_known(v___x_4296_, 1);
lean_inc(v___y_4289_);
lean_inc_ref(v___y_4288_);
lean_inc(v___y_4287_);
lean_inc_ref(v___y_4286_);
v___x_4298_ = lean_infer_type(v_a_4297_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4300_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v___x_4298_, 1);
v___x_4300_ = l_Lean_Meta_isExprDefEqGuarded(v_a_4299_, v_val_4293_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_dec_ref_known(v___x_4300_, 1);
v___y_4258_ = v_a_4297_;
v___y_4259_ = v___y_4284_;
v___y_4260_ = v___y_4285_;
v___y_4261_ = v___y_4286_;
v___y_4262_ = v___y_4287_;
v___y_4263_ = v___y_4288_;
v___y_4264_ = v___y_4289_;
goto v___jp_4257_;
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v_a_4297_);
lean_dec(v_expectedType_x3f_4221_);
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4300_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4300_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
else
{
lean_dec(v_a_4297_);
lean_dec(v_val_4293_);
lean_dec(v_expectedType_x3f_4221_);
return v___x_4298_;
}
}
else
{
lean_object* v_a_4309_; 
lean_dec(v_val_4293_);
v_a_4309_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4296_, 1);
v___y_4258_ = v_a_4309_;
v___y_4259_ = v___y_4284_;
v___y_4260_ = v___y_4285_;
v___y_4261_ = v___y_4286_;
v___y_4262_ = v___y_4287_;
v___y_4263_ = v___y_4288_;
v___y_4264_ = v___y_4289_;
goto v___jp_4257_;
}
}
else
{
lean_dec(v_val_4293_);
lean_dec(v_expectedType_x3f_4221_);
return v___x_4296_;
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_dec(v_val_4293_);
lean_dec(v_expectedType_x3f_4221_);
v_a_4310_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4294_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4294_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
}
else
{
lean_dec(v_a_4253_);
v___y_4230_ = v___y_4288_;
v___y_4231_ = v___y_4287_;
v___y_4232_ = v___y_4284_;
v___y_4233_ = v___y_4289_;
v___y_4234_ = v___y_4286_;
v___y_4235_ = v___y_4285_;
goto v___jp_4229_;
}
}
v___jp_4318_:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___y_4319_);
lean_ctor_set(v___x_4321_, 1, v___y_4320_);
v___x_4322_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4256_, v___x_4321_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_dec_ref_known(v___x_4322_, 1);
v___y_4284_ = v_a_4222_;
v___y_4285_ = v_a_4223_;
v___y_4286_ = v_a_4224_;
v___y_4287_ = v_a_4225_;
v___y_4288_ = v_a_4226_;
v___y_4289_ = v_a_4227_;
goto v___jp_4283_;
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v_a_4253_);
lean_dec(v_expectedType_x3f_4221_);
lean_dec_ref(v_tree_4220_);
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4322_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4322_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec(v_expectedType_x3f_4221_);
lean_dec_ref(v_tree_4220_);
v_a_4359_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4250_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4250_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
v___jp_4229_:
{
lean_object* v___x_4236_; 
v___x_4236_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_tree_4220_, v___y_4232_, v___y_4235_, v___y_4234_, v___y_4231_, v___y_4230_, v___y_4233_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
v___x_4238_ = lean_box(0);
v___x_4239_ = l_Lean_Elab_Term_ensureHasType(v_expectedType_x3f_4221_, v_a_4237_, v___x_4238_, v___x_4238_, v___y_4232_, v___y_4235_, v___y_4234_, v___y_4231_, v___y_4230_, v___y_4233_);
return v___x_4239_;
}
else
{
lean_dec(v_expectedType_x3f_4221_);
return v___x_4236_;
}
}
v___jp_4240_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4248_ = lean_box(0);
v___x_4249_ = l_Lean_Elab_Term_ensureHasType(v_expectedType_x3f_4221_, v___y_4241_, v___x_4248_, v___x_4248_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
return v___x_4249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0(lean_object* v_maxType_4367_, lean_object* v_nested_4368_, lean_object* v_f_x3f_4369_, uint8_t v_lhs_4370_, uint8_t v_isPred_4371_, lean_object* v_macroName_4372_, lean_object* v_stx_4373_, lean_object* v_stx_x27_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4367_, v_nested_4368_, v_f_x3f_4369_, v_lhs_4370_, v_isPred_4371_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4391_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4385_ = v___x_4382_;
v_isShared_4386_ = v_isSharedCheck_4391_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4382_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4391_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4387_; lean_object* v___x_4389_; 
v___x_4387_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4387_, 0, v_macroName_4372_);
lean_ctor_set(v___x_4387_, 1, v_stx_4373_);
lean_ctor_set(v___x_4387_, 2, v_stx_x27_4374_);
lean_ctor_set(v___x_4387_, 3, v_a_4383_);
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 0, v___x_4387_);
v___x_4389_ = v___x_4385_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
else
{
lean_dec(v_stx_x27_4374_);
lean_dec(v_stx_4373_);
lean_dec(v_macroName_4372_);
return v___x_4382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0___boxed(lean_object* v_maxType_4392_, lean_object* v_nested_4393_, lean_object* v_f_x3f_4394_, lean_object* v_lhs_4395_, lean_object* v_isPred_4396_, lean_object* v_macroName_4397_, lean_object* v_stx_4398_, lean_object* v_stx_x27_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
uint8_t v_lhs_boxed_4407_; uint8_t v_isPred_boxed_4408_; lean_object* v_res_4409_; 
v_lhs_boxed_4407_ = lean_unbox(v_lhs_4395_);
v_isPred_boxed_4408_ = lean_unbox(v_isPred_4396_);
v_res_4409_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0(v_maxType_4392_, v_nested_4393_, v_f_x3f_4394_, v_lhs_boxed_4407_, v_isPred_boxed_4408_, v_macroName_4397_, v_stx_4398_, v_stx_x27_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(lean_object* v_maxType_4410_, lean_object* v_t_4411_, lean_object* v_f_x3f_4412_, uint8_t v_lhs_4413_, uint8_t v_isPred_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
switch(lean_obj_tag(v_t_4411_))
{
case 0:
{
lean_object* v_ref_4422_; lean_object* v_infoTrees_4423_; lean_object* v_val_4424_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v_toCold_4430_; lean_object* v_currRecDepth_4431_; lean_object* v_ref_4432_; uint16_t v_optionFlags_4433_; uint8_t v_suppressElabErrors_4434_; uint8_t v_checkDeprecated_4435_; uint8_t v_isRecordingDeps_4436_; lean_object* v___y_4437_; lean_object* v___x_4459_; 
v_ref_4422_ = lean_ctor_get(v_t_4411_, 0);
v_infoTrees_4423_ = lean_ctor_get(v_t_4411_, 1);
v_val_4424_ = lean_ctor_get(v_t_4411_, 2);
lean_inc(v_a_4420_);
lean_inc_ref(v_a_4419_);
lean_inc(v_a_4418_);
lean_inc_ref(v_a_4417_);
lean_inc_ref(v_val_4424_);
v___x_4459_ = lean_infer_type(v_val_4424_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4461_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v___x_4461_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(v_a_4460_, v_a_4418_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_toCold_4462_; lean_object* v_options_4463_; lean_object* v_a_4464_; lean_object* v_inheritedTraceOptions_4465_; uint8_t v_hasTrace_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; 
v_toCold_4462_ = lean_ctor_get(v_a_4419_, 0);
v_options_4463_ = lean_ctor_get(v_toCold_4462_, 2);
v_a_4464_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4464_);
lean_dec_ref_known(v___x_4461_, 1);
v_inheritedTraceOptions_4465_ = lean_ctor_get(v_toCold_4462_, 11);
v_hasTrace_4466_ = lean_ctor_get_uint8(v_options_4463_, sizeof(void*)*1);
v___x_4467_ = l_Lean_Expr_cleanupAnnotations(v_a_4464_);
lean_dec(v_a_4464_);
v___x_4468_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
if (v_hasTrace_4466_ == 0)
{
v___y_4533_ = v_a_4415_;
v___y_4534_ = v_a_4416_;
v___y_4535_ = v_a_4417_;
v___y_4536_ = v_a_4418_;
v___y_4537_ = v_a_4419_;
v___y_4538_ = v_a_4420_;
goto v___jp_4532_;
}
else
{
lean_object* v___x_4559_; uint8_t v___x_4560_; 
v___x_4559_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4560_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4465_, v_options_4463_, v___x_4559_);
if (v___x_4560_ == 0)
{
v___y_4533_ = v_a_4415_;
v___y_4534_ = v_a_4416_;
v___y_4535_ = v_a_4417_;
v___y_4536_ = v_a_4418_;
v___y_4537_ = v_a_4419_;
v___y_4538_ = v_a_4420_;
goto v___jp_4532_;
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4561_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7);
lean_inc_ref(v_val_4424_);
v___x_4562_ = l_Lean_MessageData_ofExpr(v_val_4424_);
v___x_4563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4561_);
lean_ctor_set(v___x_4563_, 1, v___x_4562_);
v___x_4564_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3);
v___x_4565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4563_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
lean_inc_ref(v___x_4467_);
v___x_4566_ = l_Lean_MessageData_ofExpr(v___x_4467_);
v___x_4567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4565_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9);
v___x_4569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4567_);
lean_ctor_set(v___x_4569_, 1, v___x_4568_);
lean_inc_ref(v_maxType_4410_);
v___x_4570_ = l_Lean_MessageData_ofExpr(v_maxType_4410_);
v___x_4571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4569_);
lean_ctor_set(v___x_4571_, 1, v___x_4570_);
v___x_4572_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4468_, v___x_4571_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_dec_ref_known(v___x_4572_, 1);
v___y_4533_ = v_a_4415_;
v___y_4534_ = v_a_4416_;
v___y_4535_ = v_a_4417_;
v___y_4536_ = v_a_4418_;
v___y_4537_ = v_a_4419_;
v___y_4538_ = v_a_4420_;
goto v___jp_4532_;
}
else
{
lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
lean_dec_ref(v___x_4467_);
lean_dec_ref_known(v_t_4411_, 3);
lean_dec(v_f_x3f_4412_);
lean_dec_ref(v_maxType_4410_);
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4572_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4572_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
}
v___jp_4469_:
{
lean_object* v___x_4476_; 
lean_inc_ref(v___x_4467_);
lean_inc_ref(v_maxType_4410_);
v___x_4476_ = l_Lean_Meta_isExprDefEqGuarded(v_maxType_4410_, v___x_4467_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4523_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4479_ = v___x_4476_;
v_isShared_4480_ = v_isSharedCheck_4523_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4476_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4523_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
uint8_t v___x_4481_; 
v___x_4481_ = lean_unbox(v_a_4477_);
lean_dec(v_a_4477_);
if (v___x_4481_ == 0)
{
lean_object* v_toCold_4482_; lean_object* v_options_4483_; uint8_t v_hasTrace_4484_; 
lean_inc_ref(v_val_4424_);
lean_inc_ref(v_infoTrees_4423_);
lean_inc(v_ref_4422_);
lean_del_object(v___x_4479_);
lean_dec_ref_known(v_t_4411_, 3);
v_toCold_4482_ = lean_ctor_get(v___y_4474_, 0);
v_options_4483_ = lean_ctor_get(v_toCold_4482_, 2);
v_hasTrace_4484_ = lean_ctor_get_uint8(v_options_4483_, sizeof(void*)*1);
if (v_hasTrace_4484_ == 0)
{
lean_object* v_currRecDepth_4485_; lean_object* v_ref_4486_; uint16_t v_optionFlags_4487_; uint8_t v_suppressElabErrors_4488_; uint8_t v_checkDeprecated_4489_; uint8_t v_isRecordingDeps_4490_; 
lean_dec_ref(v___x_4467_);
v_currRecDepth_4485_ = lean_ctor_get(v___y_4474_, 1);
v_ref_4486_ = lean_ctor_get(v___y_4474_, 2);
v_optionFlags_4487_ = lean_ctor_get_uint16(v___y_4474_, sizeof(void*)*3);
v_suppressElabErrors_4488_ = lean_ctor_get_uint8(v___y_4474_, sizeof(void*)*3 + 2);
v_checkDeprecated_4489_ = lean_ctor_get_uint8(v___y_4474_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4490_ = lean_ctor_get_uint8(v___y_4474_, sizeof(void*)*3 + 4);
v___y_4426_ = v___y_4470_;
v___y_4427_ = v___y_4471_;
v___y_4428_ = v___y_4472_;
v___y_4429_ = v___y_4473_;
v_toCold_4430_ = v_toCold_4482_;
v_currRecDepth_4431_ = v_currRecDepth_4485_;
v_ref_4432_ = v_ref_4486_;
v_optionFlags_4433_ = v_optionFlags_4487_;
v_suppressElabErrors_4434_ = v_suppressElabErrors_4488_;
v_checkDeprecated_4435_ = v_checkDeprecated_4489_;
v_isRecordingDeps_4436_ = v_isRecordingDeps_4490_;
v___y_4437_ = v___y_4475_;
goto v___jp_4425_;
}
else
{
lean_object* v_currRecDepth_4491_; lean_object* v_ref_4492_; uint16_t v_optionFlags_4493_; uint8_t v_suppressElabErrors_4494_; uint8_t v_checkDeprecated_4495_; uint8_t v_isRecordingDeps_4496_; lean_object* v_inheritedTraceOptions_4497_; lean_object* v___x_4498_; uint8_t v___x_4499_; 
v_currRecDepth_4491_ = lean_ctor_get(v___y_4474_, 1);
v_ref_4492_ = lean_ctor_get(v___y_4474_, 2);
v_optionFlags_4493_ = lean_ctor_get_uint16(v___y_4474_, sizeof(void*)*3);
v_suppressElabErrors_4494_ = lean_ctor_get_uint8(v___y_4474_, sizeof(void*)*3 + 2);
v_checkDeprecated_4495_ = lean_ctor_get_uint8(v___y_4474_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4496_ = lean_ctor_get_uint8(v___y_4474_, sizeof(void*)*3 + 4);
v_inheritedTraceOptions_4497_ = lean_ctor_get(v_toCold_4482_, 11);
v___x_4498_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4499_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4497_, v_options_4483_, v___x_4498_);
if (v___x_4499_ == 0)
{
lean_dec_ref(v___x_4467_);
v___y_4426_ = v___y_4470_;
v___y_4427_ = v___y_4471_;
v___y_4428_ = v___y_4472_;
v___y_4429_ = v___y_4473_;
v_toCold_4430_ = v_toCold_4482_;
v_currRecDepth_4431_ = v_currRecDepth_4491_;
v_ref_4432_ = v_ref_4492_;
v_optionFlags_4433_ = v_optionFlags_4493_;
v_suppressElabErrors_4434_ = v_suppressElabErrors_4494_;
v_checkDeprecated_4435_ = v_checkDeprecated_4495_;
v_isRecordingDeps_4436_ = v_isRecordingDeps_4496_;
v___y_4437_ = v___y_4475_;
goto v___jp_4425_;
}
else
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4500_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1);
lean_inc_ref(v_val_4424_);
v___x_4501_ = l_Lean_MessageData_ofExpr(v_val_4424_);
v___x_4502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4500_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
v___x_4503_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3);
v___x_4504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4502_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
v___x_4505_ = l_Lean_MessageData_ofExpr(v___x_4467_);
v___x_4506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4504_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
v___x_4507_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5);
v___x_4508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4506_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
lean_inc_ref(v_maxType_4410_);
v___x_4509_ = l_Lean_MessageData_ofExpr(v_maxType_4410_);
v___x_4510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4468_, v___x_4510_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_dec_ref_known(v___x_4511_, 1);
v___y_4426_ = v___y_4470_;
v___y_4427_ = v___y_4471_;
v___y_4428_ = v___y_4472_;
v___y_4429_ = v___y_4473_;
v_toCold_4430_ = v_toCold_4482_;
v_currRecDepth_4431_ = v_currRecDepth_4491_;
v_ref_4432_ = v_ref_4492_;
v_optionFlags_4433_ = v_optionFlags_4493_;
v_suppressElabErrors_4434_ = v_suppressElabErrors_4494_;
v_checkDeprecated_4435_ = v_checkDeprecated_4495_;
v_isRecordingDeps_4436_ = v_isRecordingDeps_4496_;
v___y_4437_ = v___y_4475_;
goto v___jp_4425_;
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_dec_ref(v_val_4424_);
lean_dec_ref(v_infoTrees_4423_);
lean_dec(v_ref_4422_);
lean_dec_ref(v_maxType_4410_);
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4511_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4511_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
}
}
else
{
lean_object* v___x_4521_; 
lean_dec_ref(v___x_4467_);
lean_dec_ref(v_maxType_4410_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v_t_4411_);
v___x_4521_ = v___x_4479_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_t_4411_);
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
lean_dec_ref(v___x_4467_);
lean_dec_ref_known(v_t_4411_, 3);
lean_dec_ref(v_maxType_4410_);
v_a_4524_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4476_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4476_);
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
v___jp_4532_:
{
uint8_t v___x_4539_; 
v___x_4539_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_4467_);
if (v___x_4539_ == 0)
{
lean_dec(v_f_x3f_4412_);
v___y_4470_ = v___y_4533_;
v___y_4471_ = v___y_4534_;
v___y_4472_ = v___y_4535_;
v___y_4473_ = v___y_4536_;
v___y_4474_ = v___y_4537_;
v___y_4475_ = v___y_4538_;
goto v___jp_4469_;
}
else
{
if (lean_obj_tag(v_f_x3f_4412_) == 1)
{
lean_object* v_val_4540_; lean_object* v___x_4541_; 
v_val_4540_ = lean_ctor_get(v_f_x3f_4412_, 0);
lean_inc(v_val_4540_);
lean_dec_ref_known(v_f_x3f_4412_, 1);
v___x_4541_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(v_val_4540_, v_maxType_4410_, v_lhs_4413_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v_val_4540_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4550_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4544_ = v___x_4541_;
v_isShared_4545_ = v_isSharedCheck_4550_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4541_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4550_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
uint8_t v___x_4546_; 
v___x_4546_ = lean_unbox(v_a_4542_);
lean_dec(v_a_4542_);
if (v___x_4546_ == 0)
{
lean_del_object(v___x_4544_);
v___y_4470_ = v___y_4533_;
v___y_4471_ = v___y_4534_;
v___y_4472_ = v___y_4535_;
v___y_4473_ = v___y_4536_;
v___y_4474_ = v___y_4537_;
v___y_4475_ = v___y_4538_;
goto v___jp_4469_;
}
else
{
lean_object* v___x_4548_; 
lean_dec_ref(v___x_4467_);
lean_dec_ref(v_maxType_4410_);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v_t_4411_);
v___x_4548_ = v___x_4544_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_t_4411_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec_ref(v___x_4467_);
lean_dec_ref_known(v_t_4411_, 3);
lean_dec_ref(v_maxType_4410_);
v_a_4551_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4541_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4541_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
else
{
lean_dec(v_f_x3f_4412_);
v___y_4470_ = v___y_4533_;
v___y_4471_ = v___y_4534_;
v___y_4472_ = v___y_4535_;
v___y_4473_ = v___y_4536_;
v___y_4474_ = v___y_4537_;
v___y_4475_ = v___y_4538_;
goto v___jp_4469_;
}
}
}
}
else
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4588_; 
lean_dec_ref_known(v_t_4411_, 3);
lean_dec(v_f_x3f_4412_);
lean_dec_ref(v_maxType_4410_);
v_a_4581_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4583_ = v___x_4461_;
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4461_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_a_4581_);
v___x_4586_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
return v___x_4586_;
}
}
}
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
lean_dec_ref_known(v_t_4411_, 3);
lean_dec(v_f_x3f_4412_);
lean_dec_ref(v_maxType_4410_);
v_a_4589_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___x_4459_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4459_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
v___jp_4425_:
{
lean_object* v___x_4438_; lean_object* v_ref_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4438_ = lean_box(0);
v_ref_4439_ = l_Lean_replaceRef(v_ref_4422_, v_ref_4432_);
lean_inc(v_currRecDepth_4431_);
lean_inc_ref(v_toCold_4430_);
v___x_4440_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4440_, 0, v_toCold_4430_);
lean_ctor_set(v___x_4440_, 1, v_currRecDepth_4431_);
lean_ctor_set(v___x_4440_, 2, v_ref_4439_);
lean_ctor_set_uint16(v___x_4440_, sizeof(void*)*3, v_optionFlags_4433_);
lean_ctor_set_uint8(v___x_4440_, sizeof(void*)*3 + 2, v_suppressElabErrors_4434_);
lean_ctor_set_uint8(v___x_4440_, sizeof(void*)*3 + 3, v_checkDeprecated_4435_);
lean_ctor_set_uint8(v___x_4440_, sizeof(void*)*3 + 4, v_isRecordingDeps_4436_);
v___x_4441_ = l_Lean_Elab_Term_mkCoe(v_maxType_4410_, v_val_4424_, v___x_4438_, v___x_4438_, v___x_4438_, v___x_4438_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___x_4440_, v___y_4437_);
lean_dec_ref_known(v___x_4440_, 3);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4450_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4444_ = v___x_4441_;
v_isShared_4445_ = v_isSharedCheck_4450_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4441_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4450_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4448_; 
v___x_4446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4446_, 0, v_ref_4422_);
lean_ctor_set(v___x_4446_, 1, v_infoTrees_4423_);
lean_ctor_set(v___x_4446_, 2, v_a_4442_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 0, v___x_4446_);
v___x_4448_ = v___x_4444_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec_ref(v_infoTrees_4423_);
lean_dec(v_ref_4422_);
v_a_4451_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4441_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4441_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
case 1:
{
lean_object* v_ref_4597_; uint8_t v_kind_4598_; lean_object* v_f_4599_; lean_object* v_lhs_4600_; lean_object* v_rhs_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4718_; 
lean_dec(v_f_x3f_4412_);
v_ref_4597_ = lean_ctor_get(v_t_4411_, 0);
v_kind_4598_ = lean_ctor_get_uint8(v_t_4411_, sizeof(void*)*4);
v_f_4599_ = lean_ctor_get(v_t_4411_, 1);
v_lhs_4600_ = lean_ctor_get(v_t_4411_, 2);
v_rhs_4601_ = lean_ctor_get(v_t_4411_, 3);
v_isSharedCheck_4718_ = !lean_is_exclusive(v_t_4411_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4603_ = v_t_4411_;
v_isShared_4604_ = v_isSharedCheck_4718_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_rhs_4601_);
lean_inc(v_lhs_4600_);
lean_inc(v_f_4599_);
lean_inc(v_ref_4597_);
lean_dec(v_t_4411_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4718_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
switch(v_kind_4598_)
{
case 2:
{
lean_object* v___x_4623_; uint8_t v___x_4624_; lean_object* v___x_4625_; 
lean_del_object(v___x_4603_);
v___x_4623_ = lean_box(0);
v___x_4624_ = 0;
v___x_4625_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4410_, v_rhs_4601_, v___x_4623_, v___x_4624_, v___x_4624_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4634_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4628_ = v___x_4625_;
v_isShared_4629_ = v_isSharedCheck_4634_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4625_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4634_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4630_; lean_object* v___x_4632_; 
v___x_4630_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_4630_, 0, v_ref_4597_);
lean_ctor_set(v___x_4630_, 1, v_f_4599_);
lean_ctor_set(v___x_4630_, 2, v_lhs_4600_);
lean_ctor_set(v___x_4630_, 3, v_a_4626_);
lean_ctor_set_uint8(v___x_4630_, sizeof(void*)*4, v_kind_4598_);
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 0, v___x_4630_);
v___x_4632_ = v___x_4628_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4630_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
else
{
lean_dec_ref(v_lhs_4600_);
lean_dec_ref(v_f_4599_);
lean_dec(v_ref_4597_);
return v___x_4625_;
}
}
case 3:
{
lean_object* v___x_4635_; uint8_t v___x_4636_; lean_object* v___x_4637_; 
lean_del_object(v___x_4603_);
v___x_4635_ = lean_box(0);
v___x_4636_ = 0;
v___x_4637_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4410_, v_lhs_4600_, v___x_4635_, v___x_4636_, v___x_4636_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4646_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4640_ = v___x_4637_;
v_isShared_4641_ = v_isSharedCheck_4646_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4637_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4646_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4642_; lean_object* v___x_4644_; 
v___x_4642_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_4642_, 0, v_ref_4597_);
lean_ctor_set(v___x_4642_, 1, v_f_4599_);
lean_ctor_set(v___x_4642_, 2, v_a_4638_);
lean_ctor_set(v___x_4642_, 3, v_rhs_4601_);
lean_ctor_set_uint8(v___x_4642_, sizeof(void*)*4, v_kind_4598_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 0, v___x_4642_);
v___x_4644_ = v___x_4640_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v___x_4642_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
else
{
lean_dec_ref(v_rhs_4601_);
lean_dec_ref(v_f_4599_);
lean_dec(v_ref_4597_);
return v___x_4637_;
}
}
default: 
{
if (v_isPred_4414_ == 0)
{
lean_object* v___x_4647_; 
lean_inc_ref(v_maxType_4410_);
v___x_4647_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(v_f_4599_, v_maxType_4410_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; uint8_t v___x_4649_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_a_4648_);
lean_dec_ref_known(v___x_4647_, 1);
v___x_4649_ = lean_unbox(v_a_4648_);
lean_dec(v_a_4648_);
if (v___x_4649_ == 0)
{
lean_object* v_toCold_4650_; lean_object* v_currRecDepth_4651_; lean_object* v_ref_4652_; uint16_t v_optionFlags_4653_; uint8_t v_suppressElabErrors_4654_; uint8_t v_checkDeprecated_4655_; uint8_t v_isRecordingDeps_4656_; lean_object* v___x_4657_; lean_object* v_ref_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
lean_del_object(v___x_4603_);
lean_dec_ref(v_maxType_4410_);
v_toCold_4650_ = lean_ctor_get(v_a_4419_, 0);
v_currRecDepth_4651_ = lean_ctor_get(v_a_4419_, 1);
v_ref_4652_ = lean_ctor_get(v_a_4419_, 2);
v_optionFlags_4653_ = lean_ctor_get_uint16(v_a_4419_, sizeof(void*)*3);
v_suppressElabErrors_4654_ = lean_ctor_get_uint8(v_a_4419_, sizeof(void*)*3 + 2);
v_checkDeprecated_4655_ = lean_ctor_get_uint8(v_a_4419_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4656_ = lean_ctor_get_uint8(v_a_4419_, sizeof(void*)*3 + 4);
v___x_4657_ = lean_box(0);
v_ref_4658_ = l_Lean_replaceRef(v_ref_4597_, v_ref_4652_);
lean_inc(v_currRecDepth_4651_);
lean_inc_ref(v_toCold_4650_);
v___x_4659_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4659_, 0, v_toCold_4650_);
lean_ctor_set(v___x_4659_, 1, v_currRecDepth_4651_);
lean_ctor_set(v___x_4659_, 2, v_ref_4658_);
lean_ctor_set_uint16(v___x_4659_, sizeof(void*)*3, v_optionFlags_4653_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*3 + 2, v_suppressElabErrors_4654_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*3 + 3, v_checkDeprecated_4655_);
lean_ctor_set_uint8(v___x_4659_, sizeof(void*)*3 + 4, v_isRecordingDeps_4656_);
v___x_4660_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_lhs_4600_, v___x_4657_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v___x_4659_, v_a_4420_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4662_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
v___x_4662_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_rhs_4601_, v___x_4657_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v___x_4659_, v_a_4420_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; uint8_t v___x_4664_; uint8_t v___x_4665_; lean_object* v___x_4666_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref_known(v___x_4662_, 1);
v___x_4664_ = 1;
v___x_4665_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_4598_, v___x_4664_);
v___x_4666_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v___x_4665_, v_f_4599_, v_a_4661_, v_a_4663_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v___x_4659_, v_a_4420_);
lean_dec_ref_known(v___x_4659_, 3);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; lean_object* v___x_4668_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc(v_a_4667_);
lean_dec_ref_known(v___x_4666_, 1);
v___x_4668_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v_a_4420_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4677_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4671_ = v___x_4668_;
v_isShared_4672_ = v_isSharedCheck_4677_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4668_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4677_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4675_; 
v___x_4673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4673_, 0, v_ref_4597_);
lean_ctor_set(v___x_4673_, 1, v_a_4669_);
lean_ctor_set(v___x_4673_, 2, v_a_4667_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 0, v___x_4673_);
v___x_4675_ = v___x_4671_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4673_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
lean_dec(v_a_4667_);
lean_dec(v_ref_4597_);
v_a_4678_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4668_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4668_);
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
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec(v_ref_4597_);
v_a_4686_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4666_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4666_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_dec(v_a_4661_);
lean_dec_ref_known(v___x_4659_, 3);
lean_dec_ref(v_f_4599_);
lean_dec(v_ref_4597_);
v_a_4694_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4662_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4662_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_dec_ref_known(v___x_4659_, 3);
lean_dec_ref(v_rhs_4601_);
lean_dec_ref(v_f_4599_);
lean_dec(v_ref_4597_);
v_a_4702_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4660_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4660_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
else
{
goto v___jp_4605_;
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
lean_del_object(v___x_4603_);
lean_dec_ref(v_rhs_4601_);
lean_dec_ref(v_lhs_4600_);
lean_dec_ref(v_f_4599_);
lean_dec(v_ref_4597_);
lean_dec_ref(v_maxType_4410_);
v_a_4710_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4647_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4647_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
else
{
goto v___jp_4605_;
}
}
}
v___jp_4605_:
{
uint8_t v___x_4606_; lean_object* v___x_4607_; uint8_t v___x_4608_; lean_object* v___x_4609_; 
v___x_4606_ = 1;
lean_inc_ref(v_f_4599_);
v___x_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4607_, 0, v_f_4599_);
v___x_4608_ = 0;
lean_inc_ref(v___x_4607_);
lean_inc_ref(v_maxType_4410_);
v___x_4609_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4410_, v_lhs_4600_, v___x_4607_, v___x_4606_, v___x_4608_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4611_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
lean_dec_ref_known(v___x_4609_, 1);
v___x_4611_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4410_, v_rhs_4601_, v___x_4607_, v___x_4608_, v___x_4608_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4622_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4614_ = v___x_4611_;
v_isShared_4615_ = v_isSharedCheck_4622_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4622_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 3, v_a_4612_);
lean_ctor_set(v___x_4603_, 2, v_a_4610_);
v___x_4617_ = v___x_4603_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_ref_4597_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_f_4599_);
lean_ctor_set(v_reuseFailAlloc_4621_, 2, v_a_4610_);
lean_ctor_set(v_reuseFailAlloc_4621_, 3, v_a_4612_);
lean_ctor_set_uint8(v_reuseFailAlloc_4621_, sizeof(void*)*4, v_kind_4598_);
v___x_4617_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
lean_object* v___x_4619_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v___x_4617_);
v___x_4619_ = v___x_4614_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
else
{
lean_dec(v_a_4610_);
lean_del_object(v___x_4603_);
lean_dec_ref(v_f_4599_);
lean_dec(v_ref_4597_);
return v___x_4611_;
}
}
else
{
lean_dec_ref_known(v___x_4607_, 1);
lean_del_object(v___x_4603_);
lean_dec_ref(v_rhs_4601_);
lean_dec_ref(v_f_4599_);
lean_dec(v_ref_4597_);
lean_dec_ref(v_maxType_4410_);
return v___x_4609_;
}
}
}
}
case 2:
{
lean_object* v_ref_4719_; lean_object* v_f_4720_; lean_object* v_arg_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4739_; 
lean_dec(v_f_x3f_4412_);
v_ref_4719_ = lean_ctor_get(v_t_4411_, 0);
v_f_4720_ = lean_ctor_get(v_t_4411_, 1);
v_arg_4721_ = lean_ctor_get(v_t_4411_, 2);
v_isSharedCheck_4739_ = !lean_is_exclusive(v_t_4411_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4723_ = v_t_4411_;
v_isShared_4724_ = v_isSharedCheck_4739_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_arg_4721_);
lean_inc(v_f_4720_);
lean_inc(v_ref_4719_);
lean_dec(v_t_4411_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4739_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4725_; uint8_t v___x_4726_; lean_object* v___x_4727_; 
v___x_4725_ = lean_box(0);
v___x_4726_ = 0;
v___x_4727_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4410_, v_arg_4721_, v___x_4725_, v___x_4726_, v___x_4726_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4738_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4727_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4730_ = v___x_4727_;
v_isShared_4731_ = v_isSharedCheck_4738_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4727_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4738_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 2, v_a_4728_);
v___x_4733_ = v___x_4723_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_ref_4719_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v_f_4720_);
lean_ctor_set(v_reuseFailAlloc_4737_, 2, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4735_; 
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 0, v___x_4733_);
v___x_4735_ = v___x_4730_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___x_4733_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
else
{
lean_del_object(v___x_4723_);
lean_dec_ref(v_f_4720_);
lean_dec(v_ref_4719_);
return v___x_4727_;
}
}
}
default: 
{
lean_object* v_macroName_4740_; lean_object* v_stx_4741_; lean_object* v_stx_x27_4742_; lean_object* v_nested_4743_; lean_object* v_toCold_4744_; lean_object* v_currRecDepth_4745_; lean_object* v_ref_4746_; uint16_t v_optionFlags_4747_; uint8_t v_suppressElabErrors_4748_; uint8_t v_checkDeprecated_4749_; uint8_t v_isRecordingDeps_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___f_4753_; lean_object* v_ref_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
v_macroName_4740_ = lean_ctor_get(v_t_4411_, 0);
lean_inc(v_macroName_4740_);
v_stx_4741_ = lean_ctor_get(v_t_4411_, 1);
lean_inc_n(v_stx_4741_, 2);
v_stx_x27_4742_ = lean_ctor_get(v_t_4411_, 2);
lean_inc_n(v_stx_x27_4742_, 2);
v_nested_4743_ = lean_ctor_get(v_t_4411_, 3);
lean_inc_ref(v_nested_4743_);
lean_dec_ref_known(v_t_4411_, 4);
v_toCold_4744_ = lean_ctor_get(v_a_4419_, 0);
v_currRecDepth_4745_ = lean_ctor_get(v_a_4419_, 1);
v_ref_4746_ = lean_ctor_get(v_a_4419_, 2);
v_optionFlags_4747_ = lean_ctor_get_uint16(v_a_4419_, sizeof(void*)*3);
v_suppressElabErrors_4748_ = lean_ctor_get_uint8(v_a_4419_, sizeof(void*)*3 + 2);
v_checkDeprecated_4749_ = lean_ctor_get_uint8(v_a_4419_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4750_ = lean_ctor_get_uint8(v_a_4419_, sizeof(void*)*3 + 4);
v___x_4751_ = lean_box(v_lhs_4413_);
v___x_4752_ = lean_box(v_isPred_4414_);
v___f_4753_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4753_, 0, v_maxType_4410_);
lean_closure_set(v___f_4753_, 1, v_nested_4743_);
lean_closure_set(v___f_4753_, 2, v_f_x3f_4412_);
lean_closure_set(v___f_4753_, 3, v___x_4751_);
lean_closure_set(v___f_4753_, 4, v___x_4752_);
lean_closure_set(v___f_4753_, 5, v_macroName_4740_);
lean_closure_set(v___f_4753_, 6, v_stx_4741_);
lean_closure_set(v___f_4753_, 7, v_stx_x27_4742_);
v_ref_4754_ = l_Lean_replaceRef(v_stx_4741_, v_ref_4746_);
lean_inc(v_currRecDepth_4745_);
lean_inc_ref(v_toCold_4744_);
v___x_4755_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4755_, 0, v_toCold_4744_);
lean_ctor_set(v___x_4755_, 1, v_currRecDepth_4745_);
lean_ctor_set(v___x_4755_, 2, v_ref_4754_);
lean_ctor_set_uint16(v___x_4755_, sizeof(void*)*3, v_optionFlags_4747_);
lean_ctor_set_uint8(v___x_4755_, sizeof(void*)*3 + 2, v_suppressElabErrors_4748_);
lean_ctor_set_uint8(v___x_4755_, sizeof(void*)*3 + 3, v_checkDeprecated_4749_);
lean_ctor_set_uint8(v___x_4755_, sizeof(void*)*3 + 4, v_isRecordingDeps_4750_);
v___x_4756_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_stx_4741_, v_stx_x27_4742_, v___f_4753_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v___x_4755_, v_a_4420_);
lean_dec_ref_known(v___x_4755_, 3);
return v___x_4756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(lean_object* v_t_4757_, lean_object* v_maxType_4758_, uint8_t v_isPred_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v___x_4767_; uint8_t v___x_4768_; lean_object* v___x_4769_; 
v___x_4767_ = lean_box(0);
v___x_4768_ = 0;
v___x_4769_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4758_, v_t_4757_, v___x_4767_, v___x_4768_, v_isPred_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe___boxed(lean_object* v_t_4770_, lean_object* v_maxType_4771_, lean_object* v_isPred_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
uint8_t v_isPred_boxed_4780_; lean_object* v_res_4781_; 
v_isPred_boxed_4780_ = lean_unbox(v_isPred_4772_);
v_res_4781_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v_t_4770_, v_maxType_4771_, v_isPred_boxed_4780_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___boxed(lean_object* v_tree_4782_, lean_object* v_expectedType_x3f_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_tree_4782_, v_expectedType_x3f_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_);
lean_dec(v_a_4789_);
lean_dec_ref(v_a_4788_);
lean_dec(v_a_4787_);
lean_dec_ref(v_a_4786_);
lean_dec(v_a_4785_);
lean_dec_ref(v_a_4784_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___boxed(lean_object* v_maxType_4792_, lean_object* v_t_4793_, lean_object* v_f_x3f_4794_, lean_object* v_lhs_4795_, lean_object* v_isPred_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_){
_start:
{
uint8_t v_lhs_boxed_4804_; uint8_t v_isPred_boxed_4805_; lean_object* v_res_4806_; 
v_lhs_boxed_4804_ = lean_unbox(v_lhs_4795_);
v_isPred_boxed_4805_ = lean_unbox(v_isPred_4796_);
v_res_4806_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4792_, v_t_4793_, v_f_x3f_4794_, v_lhs_boxed_4804_, v_isPred_boxed_4805_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr_spec__2(lean_object* v_msg_4807_){
_start:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = l_Lean_instInhabitedExpr;
v___x_4809_ = lean_panic_fn_borrowed(v___x_4808_, v_msg_4807_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0(lean_object* v_cls_4810_, lean_object* v_msg_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_){
_start:
{
lean_object* v___x_4819_; 
v___x_4819_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v_cls_4810_, v_msg_4811_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___boxed(lean_object* v_cls_4820_, lean_object* v_msg_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0(v_cls_4820_, v_msg_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp(lean_object* v_stx_4830_, lean_object* v_expectedType_x3f_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_){
_start:
{
lean_object* v___x_4839_; 
v___x_4839_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v_stx_4830_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_object* v_a_4840_; lean_object* v___x_4841_; 
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_a_4840_);
lean_dec_ref_known(v___x_4839_, 1);
v___x_4841_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_a_4840_, v_expectedType_x3f_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
return v___x_4841_;
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
lean_dec(v_expectedType_x3f_4831_);
v_a_4842_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___x_4839_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4839_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp___boxed(lean_object* v_stx_4850_, lean_object* v_expectedType_x3f_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Lean_Elab_Term_Op_elabOp(v_stx_4850_, v_expectedType_x3f_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp(lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Lean_Elab_Term_Op_elabOp(v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp___boxed(lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l_Lean_Elab_Term_Op_elabBinOp(v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
lean_dec(v_a_4877_);
lean_dec_ref(v_a_4876_);
lean_dec(v_a_4875_);
lean_dec_ref(v_a_4874_);
lean_dec(v_a_4873_);
lean_dec_ref(v_a_4872_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1(){
_start:
{
lean_object* v___f_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___f_4889_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4890_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4891_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1));
v___x_4892_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2));
v___x_4893_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4890_, v___x_4891_, v___x_4892_, v___f_4889_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___boxed(lean_object* v_a_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1();
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3(){
_start:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
v___x_4922_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2));
v___x_4923_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__6));
v___x_4924_ = l_Lean_addBuiltinDeclarationRanges(v___x_4922_, v___x_4923_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___boxed(lean_object* v_a_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3();
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy(lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = l_Lean_Elab_Term_Op_elabOp(v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy___boxed(lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_Elab_Term_Op_elabBinOpLazy(v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
lean_dec(v_a_4940_);
lean_dec_ref(v_a_4939_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1(){
_start:
{
lean_object* v___f_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___f_4955_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4956_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4957_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3));
v___x_4958_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1));
v___x_4959_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4956_, v___x_4957_, v___x_4958_, v___f_4955_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___boxed(lean_object* v_a_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1();
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3(){
_start:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4988_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1));
v___x_4989_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__6));
v___x_4990_ = l_Lean_addBuiltinDeclarationRanges(v___x_4988_, v___x_4989_);
return v___x_4990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___boxed(lean_object* v_a_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3();
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact(lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v___x_5002_; 
v___x_5002_ = l_Lean_Elab_Term_Op_elabOp(v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact___boxed(lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Lean_Elab_Term_Op_elabLeftact(v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
lean_dec(v_a_5006_);
lean_dec_ref(v_a_5005_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1(){
_start:
{
lean_object* v___f_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___f_5021_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_5022_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5023_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7));
v___x_5024_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1));
v___x_5025_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5022_, v___x_5023_, v___x_5024_, v___f_5021_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___boxed(lean_object* v_a_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1();
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3(){
_start:
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5054_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1));
v___x_5055_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__6));
v___x_5056_ = l_Lean_addBuiltinDeclarationRanges(v___x_5054_, v___x_5055_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___boxed(lean_object* v_a_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3();
return v_res_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact(lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_){
_start:
{
lean_object* v___x_5068_; 
v___x_5068_ = l_Lean_Elab_Term_Op_elabOp(v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_);
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact___boxed(lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Elab_Term_Op_elabRightact(v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
lean_dec(v_a_5076_);
lean_dec_ref(v_a_5075_);
lean_dec(v_a_5074_);
lean_dec_ref(v_a_5073_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1(){
_start:
{
lean_object* v___f_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___f_5087_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_5088_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5089_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9));
v___x_5090_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1));
v___x_5091_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5088_, v___x_5089_, v___x_5090_, v___f_5087_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___boxed(lean_object* v_a_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1();
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3(){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___x_5120_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1));
v___x_5121_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__6));
v___x_5122_ = l_Lean_addBuiltinDeclarationRanges(v___x_5120_, v___x_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___boxed(lean_object* v_a_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3();
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp(lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l_Lean_Elab_Term_Op_elabOp(v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp___boxed(lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_Lean_Elab_Term_Op_elabUnOp(v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_);
lean_dec(v_a_5142_);
lean_dec_ref(v_a_5141_);
lean_dec(v_a_5140_);
lean_dec_ref(v_a_5139_);
lean_dec(v_a_5138_);
lean_dec_ref(v_a_5137_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1(){
_start:
{
lean_object* v___f_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; 
v___f_5153_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_5154_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5155_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5));
v___x_5156_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1));
v___x_5157_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5154_, v___x_5155_, v___x_5156_, v___f_5153_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___boxed(lean_object* v_a_5158_){
_start:
{
lean_object* v_res_5159_; 
v_res_5159_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1();
return v_res_5159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3(){
_start:
{
lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v___x_5186_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1));
v___x_5187_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__6));
v___x_5188_ = l_Lean_addBuiltinDeclarationRanges(v___x_5186_, v___x_5187_);
return v___x_5188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___boxed(lean_object* v_a_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3();
return v_res_5190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0(lean_object* v_k_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
lean_object* v___x_5199_; 
lean_inc(v___y_5193_);
lean_inc_ref(v___y_5192_);
v___x_5199_ = lean_apply_7(v_k_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, lean_box(0));
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0___boxed(lean_object* v_k_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0(v_k_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(lean_object* v_k_5209_, uint8_t v_allowLevelAssignments_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v___f_5218_; lean_object* v___x_5219_; 
lean_inc(v___y_5212_);
lean_inc_ref(v___y_5211_);
v___f_5218_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5218_, 0, v_k_5209_);
lean_closure_set(v___f_5218_, 1, v___y_5211_);
lean_closure_set(v___f_5218_, 2, v___y_5212_);
v___x_5219_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_5210_, v___f_5218_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_);
if (lean_obj_tag(v___x_5219_) == 0)
{
return v___x_5219_;
}
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
v_a_5220_ = lean_ctor_get(v___x_5219_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5219_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5219_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5220_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___boxed(lean_object* v_k_5228_, lean_object* v_allowLevelAssignments_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5237_; lean_object* v_res_5238_; 
v_allowLevelAssignments_boxed_5237_ = lean_unbox(v_allowLevelAssignments_5229_);
v_res_5238_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v_k_5228_, v_allowLevelAssignments_boxed_5237_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0(lean_object* v_00_u03b1_5239_, lean_object* v_k_5240_, uint8_t v_allowLevelAssignments_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v___x_5249_; 
v___x_5249_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v_k_5240_, v_allowLevelAssignments_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___boxed(lean_object* v_00_u03b1_5250_, lean_object* v_k_5251_, lean_object* v_allowLevelAssignments_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5260_; lean_object* v_res_5261_; 
v_allowLevelAssignments_boxed_5260_ = lean_unbox(v_allowLevelAssignments_5252_);
v_res_5261_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0(v_00_u03b1_5250_, v_k_5251_, v_allowLevelAssignments_boxed_5260_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0(lean_object* v_a_5262_, lean_object* v___x_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_){
_start:
{
lean_object* v___x_5271_; 
v___x_5271_ = l_Lean_Meta_isExprDefEq(v_a_5262_, v___x_5263_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
return v___x_5271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0___boxed(lean_object* v_a_5272_, lean_object* v___x_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0(v_a_5272_, v___x_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec_ref(v___y_5274_);
return v_res_5281_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0(void){
_start:
{
lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___x_5282_ = lean_box(0);
v___x_5283_ = l_Lean_mkSort(v___x_5282_);
return v___x_5283_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3(void){
_start:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
v___x_5287_ = lean_box(0);
v___x_5288_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__2));
v___x_5289_ = l_Lean_mkConst(v___x_5288_, v___x_5287_);
return v___x_5289_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4(void){
_start:
{
lean_object* v___x_5290_; lean_object* v___x_5291_; 
v___x_5290_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3);
v___x_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5290_);
return v___x_5291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(uint8_t v_noProp_5292_, lean_object* v_e_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_){
_start:
{
if (v_noProp_5292_ == 0)
{
lean_object* v___x_5301_; 
v___x_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5301_, 0, v_e_5293_);
return v___x_5301_;
}
else
{
lean_object* v___x_5302_; 
lean_inc(v_a_5299_);
lean_inc_ref(v_a_5298_);
lean_inc(v_a_5297_);
lean_inc_ref(v_a_5296_);
lean_inc_ref(v_e_5293_);
v___x_5302_ = lean_infer_type(v_e_5293_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
if (lean_obj_tag(v___x_5302_) == 0)
{
lean_object* v_a_5303_; lean_object* v___x_5304_; lean_object* v___f_5305_; uint8_t v___x_5306_; lean_object* v___x_5307_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5303_);
lean_dec_ref_known(v___x_5302_, 1);
v___x_5304_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0);
v___f_5305_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5305_, 0, v_a_5303_);
lean_closure_set(v___f_5305_, 1, v___x_5304_);
v___x_5306_ = 0;
v___x_5307_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v___f_5305_, v___x_5306_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5319_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5310_ = v___x_5307_;
v_isShared_5311_ = v_isSharedCheck_5319_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5307_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5319_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
uint8_t v___x_5312_; 
v___x_5312_ = lean_unbox(v_a_5308_);
lean_dec(v_a_5308_);
if (v___x_5312_ == 0)
{
lean_object* v___x_5314_; 
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 0, v_e_5293_);
v___x_5314_ = v___x_5310_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_e_5293_);
v___x_5314_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
return v___x_5314_;
}
}
else
{
lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
lean_del_object(v___x_5310_);
v___x_5316_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4);
v___x_5317_ = lean_box(0);
v___x_5318_ = l_Lean_Elab_Term_ensureHasType(v___x_5316_, v_e_5293_, v___x_5317_, v___x_5317_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
return v___x_5318_;
}
}
}
else
{
lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5327_; 
lean_dec_ref(v_e_5293_);
v_a_5320_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5322_ = v___x_5307_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5307_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5325_; 
if (v_isShared_5323_ == 0)
{
v___x_5325_ = v___x_5322_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5320_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
return v___x_5325_;
}
}
}
}
else
{
lean_dec_ref(v_e_5293_);
return v___x_5302_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___boxed(lean_object* v_noProp_5328_, lean_object* v_e_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_){
_start:
{
uint8_t v_noProp_boxed_5337_; lean_object* v_res_5338_; 
v_noProp_boxed_5337_ = lean_unbox(v_noProp_5328_);
v_res_5338_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_boxed_5337_, v_e_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
lean_dec(v_a_5335_);
lean_dec_ref(v_a_5334_);
lean_dec(v_a_5333_);
lean_dec_ref(v_a_5332_);
lean_dec(v_a_5331_);
lean_dec_ref(v_a_5330_);
return v_res_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0(lean_object* v_val_5339_, lean_object* v___x_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v___x_5348_; 
v___x_5348_ = l_Lean_Meta_isExprDefEq(v_val_5339_, v___x_5340_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
return v___x_5348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0___boxed(lean_object* v_val_5349_, lean_object* v___x_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_Lean_Elab_Term_Op_elabBinRelCore___lam__0(v_val_5349_, v___x_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_);
lean_dec(v___y_5356_);
lean_dec_ref(v___y_5355_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
return v_res_5358_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2(void){
_start:
{
lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___x_5363_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
v___x_5364_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2));
v___x_5365_ = l_Lean_Name_append(v___x_5364_, v___x_5363_);
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1(lean_object* v___x_5366_, lean_object* v___x_5367_, lean_object* v_stx_5368_, lean_object* v_val_5369_, uint8_t v_noProp_5370_, lean_object* v___x_5371_, lean_object* v_expectedType_x3f_5372_, uint8_t v___x_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_){
_start:
{
lean_object* v_toCold_5381_; lean_object* v_currRecDepth_5382_; lean_object* v_ref_5383_; uint16_t v_optionFlags_5384_; uint8_t v_suppressElabErrors_5385_; uint8_t v_checkDeprecated_5386_; uint8_t v_isRecordingDeps_5387_; lean_object* v_ref_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; 
v_toCold_5381_ = lean_ctor_get(v___y_5378_, 0);
v_currRecDepth_5382_ = lean_ctor_get(v___y_5378_, 1);
v_ref_5383_ = lean_ctor_get(v___y_5378_, 2);
v_optionFlags_5384_ = lean_ctor_get_uint16(v___y_5378_, sizeof(void*)*3);
v_suppressElabErrors_5385_ = lean_ctor_get_uint8(v___y_5378_, sizeof(void*)*3 + 2);
v_checkDeprecated_5386_ = lean_ctor_get_uint8(v___y_5378_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5387_ = lean_ctor_get_uint8(v___y_5378_, sizeof(void*)*3 + 4);
v_ref_5388_ = l_Lean_replaceRef(v___x_5366_, v_ref_5383_);
lean_inc(v_currRecDepth_5382_);
lean_inc_ref(v_toCold_5381_);
v___x_5389_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5389_, 0, v_toCold_5381_);
lean_ctor_set(v___x_5389_, 1, v_currRecDepth_5382_);
lean_ctor_set(v___x_5389_, 2, v_ref_5388_);
lean_ctor_set_uint16(v___x_5389_, sizeof(void*)*3, v_optionFlags_5384_);
lean_ctor_set_uint8(v___x_5389_, sizeof(void*)*3 + 2, v_suppressElabErrors_5385_);
lean_ctor_set_uint8(v___x_5389_, sizeof(void*)*3 + 3, v_checkDeprecated_5386_);
lean_ctor_set_uint8(v___x_5389_, sizeof(void*)*3 + 4, v_isRecordingDeps_5387_);
lean_inc(v___x_5366_);
v___x_5390_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v___x_5366_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___x_5389_, v___y_5379_);
lean_dec_ref_known(v___x_5389_, 3);
if (lean_obj_tag(v___x_5390_) == 0)
{
lean_object* v_a_5391_; lean_object* v_ref_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
lean_inc(v_a_5391_);
lean_dec_ref_known(v___x_5390_, 1);
v_ref_5392_ = l_Lean_replaceRef(v___x_5367_, v_ref_5383_);
lean_inc(v_currRecDepth_5382_);
lean_inc_ref(v_toCold_5381_);
v___x_5393_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5393_, 0, v_toCold_5381_);
lean_ctor_set(v___x_5393_, 1, v_currRecDepth_5382_);
lean_ctor_set(v___x_5393_, 2, v_ref_5392_);
lean_ctor_set_uint16(v___x_5393_, sizeof(void*)*3, v_optionFlags_5384_);
lean_ctor_set_uint8(v___x_5393_, sizeof(void*)*3 + 2, v_suppressElabErrors_5385_);
lean_ctor_set_uint8(v___x_5393_, sizeof(void*)*3 + 3, v_checkDeprecated_5386_);
lean_ctor_set_uint8(v___x_5393_, sizeof(void*)*3 + 4, v_isRecordingDeps_5387_);
lean_inc(v___x_5367_);
v___x_5394_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v___x_5367_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___x_5393_, v___y_5379_);
lean_dec_ref_known(v___x_5393_, 3);
if (lean_obj_tag(v___x_5394_) == 0)
{
lean_object* v_a_5395_; uint8_t v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___y_5400_; lean_object* v___y_5401_; lean_object* v___y_5402_; lean_object* v___y_5403_; lean_object* v___y_5404_; lean_object* v___y_5405_; lean_object* v___x_5455_; 
v_a_5395_ = lean_ctor_get(v___x_5394_, 0);
lean_inc_n(v_a_5395_, 2);
lean_dec_ref_known(v___x_5394_, 1);
v___x_5396_ = 0;
lean_inc(v_a_5391_);
lean_inc_ref(v_val_5369_);
v___x_5397_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_5397_, 0, v_stx_5368_);
lean_ctor_set(v___x_5397_, 1, v_val_5369_);
lean_ctor_set(v___x_5397_, 2, v_a_5391_);
lean_ctor_set(v___x_5397_, 3, v_a_5395_);
lean_ctor_set_uint8(v___x_5397_, sizeof(void*)*4, v___x_5396_);
v___x_5398_ = lean_box(0);
lean_inc_ref(v___x_5397_);
v___x_5455_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v___x_5397_, v___x_5398_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_object* v_options_5456_; lean_object* v_a_5457_; lean_object* v_inheritedTraceOptions_5458_; uint8_t v_hasTrace_5459_; lean_object* v___x_5460_; uint8_t v___y_5462_; lean_object* v_maxType_5463_; lean_object* v___y_5464_; lean_object* v___y_5465_; lean_object* v___y_5466_; lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v___y_5469_; lean_object* v___y_5509_; lean_object* v___y_5510_; lean_object* v___y_5511_; lean_object* v___y_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___y_5534_; lean_object* v___y_5535_; 
v_options_5456_ = lean_ctor_get(v_toCold_5381_, 2);
v_a_5457_ = lean_ctor_get(v___x_5455_, 0);
lean_inc(v_a_5457_);
lean_dec_ref_known(v___x_5455_, 1);
v_inheritedTraceOptions_5458_ = lean_ctor_get(v_toCold_5381_, 11);
v_hasTrace_5459_ = lean_ctor_get_uint8(v_options_5456_, sizeof(void*)*1);
v___x_5460_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
if (v_hasTrace_5459_ == 0)
{
v___y_5509_ = v___y_5374_;
v___y_5510_ = v___y_5375_;
v___y_5511_ = v___y_5376_;
v___y_5512_ = v___y_5377_;
v___y_5513_ = v___y_5378_;
v___y_5514_ = v___y_5379_;
goto v___jp_5508_;
}
else
{
lean_object* v___x_5546_; uint8_t v___x_5547_; 
v___x_5546_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2, &l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2_once, _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2);
v___x_5547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5458_, v_options_5456_, v___x_5546_);
if (v___x_5547_ == 0)
{
v___y_5509_ = v___y_5374_;
v___y_5510_ = v___y_5375_;
v___y_5511_ = v___y_5376_;
v___y_5512_ = v___y_5377_;
v___y_5513_ = v___y_5378_;
v___y_5514_ = v___y_5379_;
goto v___jp_5508_;
}
else
{
lean_object* v_max_x3f_5548_; uint8_t v_hasUncomparable_5549_; uint8_t v_hasUnknown_5550_; lean_object* v___y_5552_; lean_object* v___y_5553_; lean_object* v___x_5562_; lean_object* v___y_5564_; 
v_max_x3f_5548_ = lean_ctor_get(v_a_5457_, 0);
v_hasUncomparable_5549_ = lean_ctor_get_uint8(v_a_5457_, sizeof(void*)*1);
v_hasUnknown_5550_ = lean_ctor_get_uint8(v_a_5457_, sizeof(void*)*1 + 1);
v___x_5562_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8);
if (v_hasUncomparable_5549_ == 0)
{
lean_object* v___x_5572_; 
v___x_5572_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_5564_ = v___x_5572_;
goto v___jp_5563_;
}
else
{
lean_object* v___x_5573_; 
v___x_5573_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_5564_ = v___x_5573_;
goto v___jp_5563_;
}
v___jp_5551_:
{
lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; 
lean_inc_ref(v___y_5553_);
v___x_5554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5554_, 0, v___y_5553_);
v___x_5555_ = l_Lean_MessageData_ofFormat(v___x_5554_);
v___x_5556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5556_, 0, v___y_5552_);
lean_ctor_set(v___x_5556_, 1, v___x_5555_);
v___x_5557_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3);
v___x_5558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5558_, 0, v___x_5556_);
lean_ctor_set(v___x_5558_, 1, v___x_5557_);
if (lean_obj_tag(v_max_x3f_5548_) == 0)
{
lean_object* v___x_5559_; 
v___x_5559_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6);
v___y_5534_ = v___x_5558_;
v___y_5535_ = v___x_5559_;
goto v___jp_5533_;
}
else
{
lean_object* v_val_5560_; lean_object* v___x_5561_; 
v_val_5560_ = lean_ctor_get(v_max_x3f_5548_, 0);
lean_inc(v_val_5560_);
v___x_5561_ = l_Lean_MessageData_ofExpr(v_val_5560_);
v___y_5534_ = v___x_5558_;
v___y_5535_ = v___x_5561_;
goto v___jp_5533_;
}
}
v___jp_5563_:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; 
lean_inc_ref(v___y_5564_);
v___x_5565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5565_, 0, v___y_5564_);
v___x_5566_ = l_Lean_MessageData_ofFormat(v___x_5565_);
v___x_5567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5562_);
lean_ctor_set(v___x_5567_, 1, v___x_5566_);
v___x_5568_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10);
v___x_5569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5569_, 0, v___x_5567_);
lean_ctor_set(v___x_5569_, 1, v___x_5568_);
if (v_hasUnknown_5550_ == 0)
{
lean_object* v___x_5570_; 
v___x_5570_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_5552_ = v___x_5569_;
v___y_5553_ = v___x_5570_;
goto v___jp_5551_;
}
else
{
lean_object* v___x_5571_; 
v___x_5571_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_5552_ = v___x_5569_;
v___y_5553_ = v___x_5571_;
goto v___jp_5551_;
}
}
}
}
v___jp_5461_:
{
lean_object* v___x_5470_; 
v___x_5470_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v___x_5397_, v_maxType_5463_, v___y_5462_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
if (lean_obj_tag(v___x_5470_) == 0)
{
lean_object* v_a_5471_; lean_object* v___x_5472_; 
v_a_5471_ = lean_ctor_get(v___x_5470_, 0);
lean_inc(v_a_5471_);
lean_dec_ref_known(v___x_5470_, 1);
v___x_5472_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5471_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
if (lean_obj_tag(v___x_5472_) == 0)
{
lean_object* v_toCold_5473_; lean_object* v_options_5474_; uint8_t v_hasTrace_5475_; 
v_toCold_5473_ = lean_ctor_get(v___y_5468_, 0);
v_options_5474_ = lean_ctor_get(v_toCold_5473_, 2);
v_hasTrace_5475_ = lean_ctor_get_uint8(v_options_5474_, sizeof(void*)*1);
if (v_hasTrace_5475_ == 0)
{
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
return v___x_5472_;
}
else
{
lean_object* v_a_5476_; lean_object* v_inheritedTraceOptions_5477_; lean_object* v___x_5478_; uint8_t v___x_5479_; 
v_a_5476_ = lean_ctor_get(v___x_5472_, 0);
v_inheritedTraceOptions_5477_ = lean_ctor_get(v_toCold_5473_, 11);
v___x_5478_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2, &l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2_once, _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2);
v___x_5479_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5477_, v_options_5474_, v___x_5478_);
if (v___x_5479_ == 0)
{
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
return v___x_5472_;
}
else
{
lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
lean_inc_n(v_a_5476_, 2);
lean_dec_ref_known(v___x_5472_, 1);
v___x_5480_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1);
v___x_5481_ = l_Lean_MessageData_ofExpr(v_a_5476_);
v___x_5482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5480_);
lean_ctor_set(v___x_5482_, 1, v___x_5481_);
v___x_5483_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_5460_, v___x_5482_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
if (lean_obj_tag(v___x_5483_) == 0)
{
lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5490_; 
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5490_ == 0)
{
lean_object* v_unused_5491_; 
v_unused_5491_ = lean_ctor_get(v___x_5483_, 0);
lean_dec(v_unused_5491_);
v___x_5485_ = v___x_5483_;
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
else
{
lean_dec(v___x_5483_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5488_; 
if (v_isShared_5486_ == 0)
{
lean_ctor_set(v___x_5485_, 0, v_a_5476_);
v___x_5488_ = v___x_5485_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5476_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
else
{
lean_object* v_a_5492_; lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5499_; 
lean_dec(v_a_5476_);
v_a_5492_ = lean_ctor_get(v___x_5483_, 0);
v_isSharedCheck_5499_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5499_ == 0)
{
v___x_5494_ = v___x_5483_;
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
else
{
lean_inc(v_a_5492_);
lean_dec(v___x_5483_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v___x_5497_; 
if (v_isShared_5495_ == 0)
{
v___x_5497_ = v___x_5494_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_a_5492_);
v___x_5497_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
return v___x_5497_;
}
}
}
}
}
}
else
{
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
return v___x_5472_;
}
}
else
{
lean_object* v_a_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5507_; 
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
v_a_5500_ = lean_ctor_get(v___x_5470_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5502_ = v___x_5470_;
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_a_5500_);
lean_dec(v___x_5470_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5505_; 
if (v_isShared_5503_ == 0)
{
v___x_5505_ = v___x_5502_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_a_5500_);
v___x_5505_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
return v___x_5505_;
}
}
}
}
v___jp_5508_:
{
uint8_t v_hasUncomparable_5515_; 
v_hasUncomparable_5515_ = lean_ctor_get_uint8(v_a_5457_, sizeof(void*)*1);
if (v_hasUncomparable_5515_ == 0)
{
lean_object* v_max_x3f_5516_; 
v_max_x3f_5516_ = lean_ctor_get(v_a_5457_, 0);
lean_inc(v_max_x3f_5516_);
lean_dec(v_a_5457_);
if (lean_obj_tag(v_max_x3f_5516_) == 0)
{
lean_dec_ref_known(v___x_5397_, 4);
v___y_5400_ = v___y_5514_;
v___y_5401_ = v___y_5510_;
v___y_5402_ = v___y_5509_;
v___y_5403_ = v___y_5512_;
v___y_5404_ = v___y_5511_;
v___y_5405_ = v___y_5513_;
goto v___jp_5399_;
}
else
{
lean_object* v_val_5517_; uint8_t v___x_5518_; 
lean_dec(v_a_5395_);
lean_dec(v_a_5391_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
lean_dec(v___x_5367_);
lean_dec(v___x_5366_);
v_val_5517_ = lean_ctor_get(v_max_x3f_5516_, 0);
lean_inc(v_val_5517_);
lean_dec_ref_known(v_max_x3f_5516_, 1);
v___x_5518_ = 1;
if (v_noProp_5370_ == 0)
{
v___y_5462_ = v___x_5518_;
v_maxType_5463_ = v_val_5517_;
v___y_5464_ = v___y_5509_;
v___y_5465_ = v___y_5510_;
v___y_5466_ = v___y_5511_;
v___y_5467_ = v___y_5512_;
v___y_5468_ = v___y_5513_;
v___y_5469_ = v___y_5514_;
goto v___jp_5461_;
}
else
{
lean_object* v___x_5519_; lean_object* v___f_5520_; lean_object* v___x_5521_; 
v___x_5519_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0);
lean_inc(v_val_5517_);
v___f_5520_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5520_, 0, v_val_5517_);
lean_closure_set(v___f_5520_, 1, v___x_5519_);
v___x_5521_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v___f_5520_, v___x_5373_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_);
if (lean_obj_tag(v___x_5521_) == 0)
{
lean_object* v_a_5522_; uint8_t v___x_5523_; 
v_a_5522_ = lean_ctor_get(v___x_5521_, 0);
lean_inc(v_a_5522_);
lean_dec_ref_known(v___x_5521_, 1);
v___x_5523_ = lean_unbox(v_a_5522_);
lean_dec(v_a_5522_);
if (v___x_5523_ == 0)
{
v___y_5462_ = v___x_5518_;
v_maxType_5463_ = v_val_5517_;
v___y_5464_ = v___y_5509_;
v___y_5465_ = v___y_5510_;
v___y_5466_ = v___y_5511_;
v___y_5467_ = v___y_5512_;
v___y_5468_ = v___y_5513_;
v___y_5469_ = v___y_5514_;
goto v___jp_5461_;
}
else
{
lean_object* v___x_5524_; 
lean_dec(v_val_5517_);
v___x_5524_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3);
v___y_5462_ = v___x_5518_;
v_maxType_5463_ = v___x_5524_;
v___y_5464_ = v___y_5509_;
v___y_5465_ = v___y_5510_;
v___y_5466_ = v___y_5511_;
v___y_5467_ = v___y_5512_;
v___y_5468_ = v___y_5513_;
v___y_5469_ = v___y_5514_;
goto v___jp_5461_;
}
}
else
{
lean_object* v_a_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5532_; 
lean_dec(v_val_5517_);
lean_dec(v___y_5514_);
lean_dec_ref(v___y_5513_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5511_);
lean_dec_ref_known(v___x_5397_, 4);
v_a_5525_ = lean_ctor_get(v___x_5521_, 0);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___x_5521_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5527_ = v___x_5521_;
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_a_5525_);
lean_dec(v___x_5521_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5530_; 
if (v_isShared_5528_ == 0)
{
v___x_5530_ = v___x_5527_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_a_5525_);
v___x_5530_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
return v___x_5530_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5457_);
lean_dec_ref_known(v___x_5397_, 4);
v___y_5400_ = v___y_5514_;
v___y_5401_ = v___y_5510_;
v___y_5402_ = v___y_5509_;
v___y_5403_ = v___y_5512_;
v___y_5404_ = v___y_5511_;
v___y_5405_ = v___y_5513_;
goto v___jp_5399_;
}
}
v___jp_5533_:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5536_, 0, v___y_5534_);
lean_ctor_set(v___x_5536_, 1, v___y_5535_);
v___x_5537_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_5460_, v___x_5536_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5537_) == 0)
{
lean_dec_ref_known(v___x_5537_, 1);
v___y_5509_ = v___y_5374_;
v___y_5510_ = v___y_5375_;
v___y_5511_ = v___y_5376_;
v___y_5512_ = v___y_5377_;
v___y_5513_ = v___y_5378_;
v___y_5514_ = v___y_5379_;
goto v___jp_5508_;
}
else
{
lean_object* v_a_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5545_; 
lean_dec(v_a_5457_);
lean_dec_ref_known(v___x_5397_, 4);
lean_dec(v_a_5395_);
lean_dec(v_a_5391_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
lean_dec(v___x_5367_);
lean_dec(v___x_5366_);
v_a_5538_ = lean_ctor_get(v___x_5537_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5537_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5540_ = v___x_5537_;
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_a_5538_);
lean_dec(v___x_5537_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5543_; 
if (v_isShared_5541_ == 0)
{
v___x_5543_ = v___x_5540_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_a_5538_);
v___x_5543_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
return v___x_5543_;
}
}
}
}
}
else
{
lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5581_; 
lean_dec_ref_known(v___x_5397_, 4);
lean_dec(v_a_5395_);
lean_dec(v_a_5391_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
lean_dec(v___x_5367_);
lean_dec(v___x_5366_);
v_a_5574_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5576_ = v___x_5455_;
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_dec(v___x_5455_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5579_; 
if (v_isShared_5577_ == 0)
{
v___x_5579_ = v___x_5576_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
v___jp_5399_:
{
lean_object* v___x_5406_; 
v___x_5406_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5391_, v___y_5402_, v___y_5401_, v___y_5404_, v___y_5403_, v___y_5405_, v___y_5400_);
if (lean_obj_tag(v___x_5406_) == 0)
{
lean_object* v_a_5407_; lean_object* v___x_5408_; 
v_a_5407_ = lean_ctor_get(v___x_5406_, 0);
lean_inc(v_a_5407_);
lean_dec_ref_known(v___x_5406_, 1);
v___x_5408_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5395_, v___y_5402_, v___y_5401_, v___y_5404_, v___y_5403_, v___y_5405_, v___y_5400_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v_a_5409_; lean_object* v_toCold_5410_; lean_object* v_currRecDepth_5411_; lean_object* v_ref_5412_; uint16_t v_optionFlags_5413_; uint8_t v_suppressElabErrors_5414_; uint8_t v_checkDeprecated_5415_; uint8_t v_isRecordingDeps_5416_; lean_object* v_ref_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v_a_5409_ = lean_ctor_get(v___x_5408_, 0);
lean_inc(v_a_5409_);
lean_dec_ref_known(v___x_5408_, 1);
v_toCold_5410_ = lean_ctor_get(v___y_5405_, 0);
v_currRecDepth_5411_ = lean_ctor_get(v___y_5405_, 1);
v_ref_5412_ = lean_ctor_get(v___y_5405_, 2);
v_optionFlags_5413_ = lean_ctor_get_uint16(v___y_5405_, sizeof(void*)*3);
v_suppressElabErrors_5414_ = lean_ctor_get_uint8(v___y_5405_, sizeof(void*)*3 + 2);
v_checkDeprecated_5415_ = lean_ctor_get_uint8(v___y_5405_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5416_ = lean_ctor_get_uint8(v___y_5405_, sizeof(void*)*3 + 4);
v_ref_5417_ = l_Lean_replaceRef(v___x_5366_, v_ref_5412_);
lean_dec(v___x_5366_);
lean_inc(v_currRecDepth_5411_);
lean_inc_ref(v_toCold_5410_);
v___x_5418_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5418_, 0, v_toCold_5410_);
lean_ctor_set(v___x_5418_, 1, v_currRecDepth_5411_);
lean_ctor_set(v___x_5418_, 2, v_ref_5417_);
lean_ctor_set_uint16(v___x_5418_, sizeof(void*)*3, v_optionFlags_5413_);
lean_ctor_set_uint8(v___x_5418_, sizeof(void*)*3 + 2, v_suppressElabErrors_5414_);
lean_ctor_set_uint8(v___x_5418_, sizeof(void*)*3 + 3, v_checkDeprecated_5415_);
lean_ctor_set_uint8(v___x_5418_, sizeof(void*)*3 + 4, v_isRecordingDeps_5416_);
v___x_5419_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_5370_, v_a_5407_, v___y_5402_, v___y_5401_, v___y_5404_, v___y_5403_, v___x_5418_, v___y_5400_);
lean_dec_ref_known(v___x_5418_, 3);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; lean_object* v_ref_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
lean_inc(v_a_5420_);
lean_dec_ref_known(v___x_5419_, 1);
v_ref_5421_ = l_Lean_replaceRef(v___x_5367_, v_ref_5412_);
lean_dec(v___x_5367_);
lean_inc(v_currRecDepth_5411_);
lean_inc_ref(v_toCold_5410_);
v___x_5422_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5422_, 0, v_toCold_5410_);
lean_ctor_set(v___x_5422_, 1, v_currRecDepth_5411_);
lean_ctor_set(v___x_5422_, 2, v_ref_5421_);
lean_ctor_set_uint16(v___x_5422_, sizeof(void*)*3, v_optionFlags_5413_);
lean_ctor_set_uint8(v___x_5422_, sizeof(void*)*3 + 2, v_suppressElabErrors_5414_);
lean_ctor_set_uint8(v___x_5422_, sizeof(void*)*3 + 3, v_checkDeprecated_5415_);
lean_ctor_set_uint8(v___x_5422_, sizeof(void*)*3 + 4, v_isRecordingDeps_5416_);
v___x_5423_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_5370_, v_a_5409_, v___y_5402_, v___y_5401_, v___y_5404_, v___y_5403_, v___x_5422_, v___y_5400_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5454_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5426_ = v___x_5423_;
v_isShared_5427_ = v_isSharedCheck_5454_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5454_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5428_; 
lean_inc(v___y_5400_);
lean_inc_ref(v___y_5405_);
lean_inc(v___y_5403_);
lean_inc_ref(v___y_5404_);
lean_inc(v_a_5420_);
v___x_5428_ = lean_infer_type(v_a_5420_, v___y_5404_, v___y_5403_, v___y_5405_, v___y_5400_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5453_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5431_ = v___x_5428_;
v_isShared_5432_ = v_isSharedCheck_5453_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5428_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5453_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
lean_ctor_set_tag(v___x_5431_, 1);
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
lean_object* v___x_5435_; 
v___x_5435_ = l_Lean_Elab_Term_ensureHasType(v___x_5434_, v_a_5424_, v___x_5398_, v___x_5398_, v___y_5402_, v___y_5401_, v___y_5404_, v___y_5403_, v___x_5422_, v___y_5400_);
lean_dec_ref_known(v___x_5422_, 3);
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5451_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
v_isSharedCheck_5451_ = !lean_is_exclusive(v___x_5435_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5438_ = v___x_5435_;
v_isShared_5439_ = v_isSharedCheck_5451_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_a_5436_);
lean_dec(v___x_5435_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5451_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5440_; lean_object* v___x_5442_; 
v___x_5440_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
if (v_isShared_5439_ == 0)
{
lean_ctor_set_tag(v___x_5438_, 1);
lean_ctor_set(v___x_5438_, 0, v_a_5420_);
v___x_5442_ = v___x_5438_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_a_5420_);
v___x_5442_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
lean_object* v___x_5444_; 
if (v_isShared_5427_ == 0)
{
lean_ctor_set_tag(v___x_5426_, 1);
lean_ctor_set(v___x_5426_, 0, v_a_5436_);
v___x_5444_ = v___x_5426_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_a_5436_);
v___x_5444_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5445_ = lean_mk_empty_array_with_capacity(v___x_5371_);
v___x_5446_ = lean_array_push(v___x_5445_, v___x_5442_);
v___x_5447_ = lean_array_push(v___x_5446_, v___x_5444_);
v___x_5448_ = l_Lean_Elab_Term_elabAppArgs(v_val_5369_, v___x_5440_, v___x_5447_, v_expectedType_x3f_5372_, v___x_5373_, v___x_5373_, v___x_5373_, v___y_5402_, v___y_5401_, v___y_5404_, v___y_5403_, v___y_5405_, v___y_5400_);
lean_dec(v___y_5400_);
lean_dec_ref(v___y_5405_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5404_);
return v___x_5448_;
}
}
}
}
else
{
lean_del_object(v___x_5426_);
lean_dec(v_a_5420_);
lean_dec_ref(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec(v___y_5400_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
return v___x_5435_;
}
}
}
}
else
{
lean_del_object(v___x_5426_);
lean_dec(v_a_5424_);
lean_dec_ref_known(v___x_5422_, 3);
lean_dec(v_a_5420_);
lean_dec_ref(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec(v___y_5400_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
return v___x_5428_;
}
}
}
else
{
lean_dec_ref_known(v___x_5422_, 3);
lean_dec(v_a_5420_);
lean_dec_ref(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec(v___y_5400_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
return v___x_5423_;
}
}
else
{
lean_dec(v_a_5409_);
lean_dec_ref(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec(v___y_5400_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
lean_dec(v___x_5367_);
return v___x_5419_;
}
}
else
{
lean_dec(v_a_5407_);
lean_dec_ref(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec(v___y_5400_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
lean_dec(v___x_5367_);
lean_dec(v___x_5366_);
return v___x_5408_;
}
}
else
{
lean_dec_ref(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec(v___y_5400_);
lean_dec(v_a_5395_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
lean_dec(v___x_5367_);
lean_dec(v___x_5366_);
return v___x_5406_;
}
}
}
else
{
lean_object* v_a_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5589_; 
lean_dec(v_a_5391_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
lean_dec(v_stx_5368_);
lean_dec(v___x_5367_);
lean_dec(v___x_5366_);
v_a_5582_ = lean_ctor_get(v___x_5394_, 0);
v_isSharedCheck_5589_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5589_ == 0)
{
v___x_5584_ = v___x_5394_;
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_a_5582_);
lean_dec(v___x_5394_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5587_; 
if (v_isShared_5585_ == 0)
{
v___x_5587_ = v___x_5584_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_a_5582_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
return v___x_5587_;
}
}
}
}
else
{
lean_object* v_a_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5597_; 
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec(v_expectedType_x3f_5372_);
lean_dec_ref(v_val_5369_);
lean_dec(v_stx_5368_);
lean_dec(v___x_5367_);
lean_dec(v___x_5366_);
v_a_5590_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5597_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5597_ == 0)
{
v___x_5592_ = v___x_5390_;
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_a_5590_);
lean_dec(v___x_5390_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v___x_5595_; 
if (v_isShared_5593_ == 0)
{
v___x_5595_ = v___x_5592_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_a_5590_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___boxed(lean_object* v___x_5598_, lean_object* v___x_5599_, lean_object* v_stx_5600_, lean_object* v_val_5601_, lean_object* v_noProp_5602_, lean_object* v___x_5603_, lean_object* v_expectedType_x3f_5604_, lean_object* v___x_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_){
_start:
{
uint8_t v_noProp_boxed_5613_; uint8_t v___x_11471__boxed_5614_; lean_object* v_res_5615_; 
v_noProp_boxed_5613_ = lean_unbox(v_noProp_5602_);
v___x_11471__boxed_5614_ = lean_unbox(v___x_5605_);
v_res_5615_ = l_Lean_Elab_Term_Op_elabBinRelCore___lam__1(v___x_5598_, v___x_5599_, v_stx_5600_, v_val_5601_, v_noProp_boxed_5613_, v___x_5603_, v_expectedType_x3f_5604_, v___x_11471__boxed_5614_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_);
lean_dec(v___y_5607_);
lean_dec_ref(v___y_5606_);
lean_dec(v___x_5603_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore(uint8_t v_noProp_5616_, lean_object* v_stx_5617_, lean_object* v_expectedType_x3f_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_){
_start:
{
lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; uint8_t v___x_5629_; lean_object* v___x_5630_; 
v___x_5626_ = lean_unsigned_to_nat(1u);
v___x_5627_ = l_Lean_Syntax_getArg(v_stx_5617_, v___x_5626_);
v___x_5628_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_5629_ = 0;
lean_inc(v___x_5627_);
v___x_5630_ = l_Lean_Elab_Term_resolveId_x3f(v___x_5627_, v___x_5628_, v___x_5629_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_);
if (lean_obj_tag(v___x_5630_) == 0)
{
lean_object* v_a_5631_; 
v_a_5631_ = lean_ctor_get(v___x_5630_, 0);
lean_inc(v_a_5631_);
lean_dec_ref_known(v___x_5630_, 1);
if (lean_obj_tag(v_a_5631_) == 0)
{
lean_object* v___x_5632_; lean_object* v___x_5633_; 
lean_dec(v_expectedType_x3f_5618_);
lean_dec(v_stx_5617_);
v___x_5632_ = l_Lean_Syntax_getId(v___x_5627_);
v___x_5633_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v___x_5627_, v___x_5632_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_);
lean_dec(v___x_5627_);
return v___x_5633_;
}
else
{
lean_object* v_val_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___f_5641_; lean_object* v___x_5642_; 
lean_dec(v___x_5627_);
v_val_5634_ = lean_ctor_get(v_a_5631_, 0);
lean_inc(v_val_5634_);
lean_dec_ref_known(v_a_5631_, 1);
v___x_5635_ = lean_unsigned_to_nat(2u);
v___x_5636_ = l_Lean_Syntax_getArg(v_stx_5617_, v___x_5635_);
v___x_5637_ = lean_unsigned_to_nat(3u);
v___x_5638_ = l_Lean_Syntax_getArg(v_stx_5617_, v___x_5637_);
v___x_5639_ = lean_box(v_noProp_5616_);
v___x_5640_ = lean_box(v___x_5629_);
v___f_5641_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___boxed), 15, 8);
lean_closure_set(v___f_5641_, 0, v___x_5636_);
lean_closure_set(v___f_5641_, 1, v___x_5638_);
lean_closure_set(v___f_5641_, 2, v_stx_5617_);
lean_closure_set(v___f_5641_, 3, v_val_5634_);
lean_closure_set(v___f_5641_, 4, v___x_5639_);
lean_closure_set(v___f_5641_, 5, v___x_5635_);
lean_closure_set(v___f_5641_, 6, v_expectedType_x3f_5618_);
lean_closure_set(v___f_5641_, 7, v___x_5640_);
v___x_5642_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_box(0), v___f_5641_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_);
return v___x_5642_;
}
}
else
{
lean_object* v_a_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5650_; 
lean_dec(v___x_5627_);
lean_dec(v_expectedType_x3f_5618_);
lean_dec(v_stx_5617_);
v_a_5643_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5645_ = v___x_5630_;
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_a_5643_);
lean_dec(v___x_5630_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5648_; 
if (v_isShared_5646_ == 0)
{
v___x_5648_ = v___x_5645_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_a_5643_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___boxed(lean_object* v_noProp_5651_, lean_object* v_stx_5652_, lean_object* v_expectedType_x3f_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_){
_start:
{
uint8_t v_noProp_boxed_5661_; lean_object* v_res_5662_; 
v_noProp_boxed_5661_ = lean_unbox(v_noProp_5651_);
v_res_5662_ = l_Lean_Elab_Term_Op_elabBinRelCore(v_noProp_boxed_5661_, v_stx_5652_, v_expectedType_x3f_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_);
lean_dec(v_a_5659_);
lean_dec_ref(v_a_5658_);
lean_dec(v_a_5657_);
lean_dec_ref(v_a_5656_);
lean_dec(v_a_5655_);
lean_dec_ref(v_a_5654_);
return v_res_5662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel(lean_object* v_stx_5663_, lean_object* v_expectedType_x3f_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_){
_start:
{
uint8_t v___x_5672_; lean_object* v___x_5673_; 
v___x_5672_ = 0;
v___x_5673_ = l_Lean_Elab_Term_Op_elabBinRelCore(v___x_5672_, v_stx_5663_, v_expectedType_x3f_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_, v_a_5669_, v_a_5670_);
return v___x_5673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel___boxed(lean_object* v_stx_5674_, lean_object* v_expectedType_x3f_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_){
_start:
{
lean_object* v_res_5683_; 
v_res_5683_ = l_Lean_Elab_Term_Op_elabBinRel(v_stx_5674_, v_expectedType_x3f_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
lean_dec(v_a_5679_);
lean_dec_ref(v_a_5678_);
lean_dec(v_a_5677_);
lean_dec_ref(v_a_5676_);
return v_res_5683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1(){
_start:
{
lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; 
v___x_5697_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5698_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0));
v___x_5699_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2));
v___x_5700_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRel___boxed), 9, 0);
v___x_5701_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5697_, v___x_5698_, v___x_5699_, v___x_5700_);
return v___x_5701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___boxed(lean_object* v_a_5702_){
_start:
{
lean_object* v_res_5703_; 
v_res_5703_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1();
return v_res_5703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3(){
_start:
{
lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; 
v___x_5730_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2));
v___x_5731_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__6));
v___x_5732_ = l_Lean_addBuiltinDeclarationRanges(v___x_5730_, v___x_5731_);
return v___x_5732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___boxed(lean_object* v_a_5733_){
_start:
{
lean_object* v_res_5734_; 
v_res_5734_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3();
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp(lean_object* v_stx_5735_, lean_object* v_expectedType_x3f_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_){
_start:
{
uint8_t v___x_5744_; lean_object* v___x_5745_; 
v___x_5744_ = 1;
v___x_5745_ = l_Lean_Elab_Term_Op_elabBinRelCore(v___x_5744_, v_stx_5735_, v_expectedType_x3f_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp___boxed(lean_object* v_stx_5746_, lean_object* v_expectedType_x3f_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_){
_start:
{
lean_object* v_res_5755_; 
v_res_5755_ = l_Lean_Elab_Term_Op_elabBinRelNoProp(v_stx_5746_, v_expectedType_x3f_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_);
lean_dec(v_a_5753_);
lean_dec_ref(v_a_5752_);
lean_dec(v_a_5751_);
lean_dec_ref(v_a_5750_);
lean_dec(v_a_5749_);
lean_dec_ref(v_a_5748_);
return v_res_5755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1(){
_start:
{
lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; 
v___x_5770_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5771_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1));
v___x_5772_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3));
v___x_5773_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelNoProp___boxed), 9, 0);
v___x_5774_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5770_, v___x_5771_, v___x_5772_, v___x_5773_);
return v___x_5774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___boxed(lean_object* v_a_5775_){
_start:
{
lean_object* v_res_5776_; 
v_res_5776_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1();
return v_res_5776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3(){
_start:
{
lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; 
v___x_5803_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3));
v___x_5804_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__6));
v___x_5805_ = l_Lean_addBuiltinDeclarationRanges(v___x_5803_, v___x_5804_);
return v___x_5805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___boxed(lean_object* v_a_5806_){
_start:
{
lean_object* v_res_5807_; 
v_res_5807_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3();
return v_res_5807_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1(void){
_start:
{
lean_object* v___x_5809_; lean_object* v___x_5810_; 
v___x_5809_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__0));
v___x_5810_ = l_Lean_stringToMessageData(v___x_5809_);
return v___x_5810_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3(void){
_start:
{
lean_object* v___x_5812_; lean_object* v___x_5813_; 
v___x_5812_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__2));
v___x_5813_ = l_Lean_stringToMessageData(v___x_5812_);
return v___x_5813_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7(void){
_start:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; 
v___x_5818_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__6));
v___x_5819_ = l_Lean_stringToMessageData(v___x_5818_);
return v___x_5819_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11(void){
_start:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5824_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__10));
v___x_5825_ = l_Lean_stringToMessageData(v___x_5824_);
return v___x_5825_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13(void){
_start:
{
lean_object* v___x_5827_; lean_object* v___x_5828_; 
v___x_5827_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__12));
v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
return v___x_5828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty(lean_object* v_stx_5829_, lean_object* v_expectedType_x3f_5830_, lean_object* v_a_5831_, lean_object* v_a_5832_, lean_object* v_a_5833_, lean_object* v_a_5834_, lean_object* v_a_5835_, lean_object* v_a_5836_){
_start:
{
lean_object* v___x_5838_; 
lean_inc(v_expectedType_x3f_5830_);
v___x_5838_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_5830_, v_a_5831_, v_a_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_);
if (lean_obj_tag(v___x_5838_) == 0)
{
lean_dec_ref_known(v___x_5838_, 1);
if (lean_obj_tag(v_expectedType_x3f_5830_) == 0)
{
lean_object* v___x_5839_; lean_object* v___x_5840_; 
v___x_5839_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1);
v___x_5840_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_5839_, v_a_5831_, v_a_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_);
return v___x_5840_;
}
else
{
lean_object* v_val_5841_; lean_object* v___x_5842_; 
v_val_5841_ = lean_ctor_get(v_expectedType_x3f_5830_, 0);
lean_inc_n(v_val_5841_, 2);
lean_dec_ref_known(v_expectedType_x3f_5830_, 1);
v___x_5842_ = l_Lean_Meta_mkDefault(v_val_5841_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_);
if (lean_obj_tag(v___x_5842_) == 0)
{
lean_dec(v_val_5841_);
return v___x_5842_;
}
else
{
lean_object* v_a_5843_; uint8_t v___x_5844_; 
v_a_5843_ = lean_ctor_get(v___x_5842_, 0);
v___x_5844_ = l_Lean_Exception_isInterrupt(v_a_5843_);
if (v___x_5844_ == 0)
{
uint8_t v___x_5845_; 
lean_inc(v_a_5843_);
v___x_5845_ = l_Lean_Exception_isRuntime(v_a_5843_);
if (v___x_5845_ == 0)
{
lean_object* v___x_5846_; 
lean_dec_ref_known(v___x_5842_, 1);
lean_inc(v_val_5841_);
v___x_5846_ = l_Lean_Meta_mkOfNonempty(v_val_5841_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_);
if (lean_obj_tag(v___x_5846_) == 0)
{
lean_dec(v_val_5841_);
return v___x_5846_;
}
else
{
lean_object* v_a_5847_; uint8_t v___x_5848_; 
v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
v___x_5848_ = l_Lean_Exception_isInterrupt(v_a_5847_);
if (v___x_5848_ == 0)
{
uint8_t v___x_5849_; 
lean_inc(v_a_5847_);
v___x_5849_ = l_Lean_Exception_isRuntime(v_a_5847_);
if (v___x_5849_ == 0)
{
lean_object* v___x_5850_; lean_object* v___x_5851_; uint8_t v___x_5852_; 
lean_dec_ref_known(v___x_5846_, 1);
v___x_5850_ = lean_unsigned_to_nat(1u);
v___x_5851_ = l_Lean_Syntax_getArg(v_stx_5829_, v___x_5850_);
v___x_5852_ = l_Lean_Syntax_isNone(v___x_5851_);
lean_dec(v___x_5851_);
if (v___x_5852_ == 0)
{
uint8_t v___x_5853_; lean_object* v___x_5854_; 
v___x_5853_ = 1;
v___x_5854_ = l_Lean_Meta_mkLabeledSorry(v_val_5841_, v___x_5852_, v___x_5853_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_);
return v___x_5854_;
}
else
{
lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5855_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3);
v___x_5856_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__5));
v___x_5857_ = l_Lean_MessageData_ofConstName(v___x_5856_, v___x_5849_);
v___x_5858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5855_);
lean_ctor_set(v___x_5858_, 1, v___x_5857_);
v___x_5859_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7);
v___x_5860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5860_, 0, v___x_5858_);
lean_ctor_set(v___x_5860_, 1, v___x_5859_);
v___x_5861_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__9));
v___x_5862_ = l_Lean_MessageData_ofConstName(v___x_5861_, v___x_5849_);
v___x_5863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5863_, 0, v___x_5860_);
lean_ctor_set(v___x_5863_, 1, v___x_5862_);
v___x_5864_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11);
v___x_5865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5863_);
lean_ctor_set(v___x_5865_, 1, v___x_5864_);
v___x_5866_ = l_Lean_indentExpr(v_val_5841_);
v___x_5867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5867_, 0, v___x_5865_);
lean_ctor_set(v___x_5867_, 1, v___x_5866_);
v___x_5868_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13);
v___x_5869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5869_, 0, v___x_5867_);
lean_ctor_set(v___x_5869_, 1, v___x_5868_);
v___x_5870_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_5869_, v_a_5831_, v_a_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_);
return v___x_5870_;
}
}
else
{
lean_dec(v_val_5841_);
return v___x_5846_;
}
}
else
{
lean_dec(v_val_5841_);
return v___x_5846_;
}
}
}
else
{
lean_dec(v_val_5841_);
return v___x_5842_;
}
}
else
{
lean_dec(v_val_5841_);
return v___x_5842_;
}
}
}
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
lean_dec(v_expectedType_x3f_5830_);
v_a_5871_ = lean_ctor_get(v___x_5838_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5838_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5838_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5838_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___boxed(lean_object* v_stx_5879_, lean_object* v_expectedType_x3f_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_){
_start:
{
lean_object* v_res_5888_; 
v_res_5888_ = l_Lean_Elab_Term_Op_elabDefaultOrNonempty(v_stx_5879_, v_expectedType_x3f_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
lean_dec(v_a_5886_);
lean_dec_ref(v_a_5885_);
lean_dec(v_a_5884_);
lean_dec_ref(v_a_5883_);
lean_dec(v_a_5882_);
lean_dec_ref(v_a_5881_);
lean_dec(v_stx_5879_);
return v_res_5888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1(){
_start:
{
lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; 
v___x_5903_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5904_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1));
v___x_5905_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3));
v___x_5906_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___boxed), 9, 0);
v___x_5907_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5903_, v___x_5904_, v___x_5905_, v___x_5906_);
return v___x_5907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___boxed(lean_object* v_a_5908_){
_start:
{
lean_object* v_res_5909_; 
v_res_5909_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1();
return v_res_5909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3(){
_start:
{
lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; 
v___x_5936_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3));
v___x_5937_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__6));
v___x_5938_ = l_Lean_addBuiltinDeclarationRanges(v___x_5936_, v___x_5937_);
return v___x_5938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___boxed(lean_object* v_a_5939_){
_start:
{
lean_object* v_res_5940_; 
v_res_5940_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3();
return v_res_5940_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5987_ = lean_unsigned_to_nat(2859506122u);
v___x_5988_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__17_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_5989_ = l_Lean_Name_num___override(v___x_5988_, v___x_5987_);
return v___x_5989_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; 
v___x_5991_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__19_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_5992_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5993_ = l_Lean_Name_str___override(v___x_5992_, v___x_5991_);
return v___x_5993_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5995_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__21_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_5996_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_5997_ = l_Lean_Name_str___override(v___x_5996_, v___x_5995_);
return v___x_5997_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; 
v___x_5998_ = lean_unsigned_to_nat(2u);
v___x_5999_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_6000_ = l_Lean_Name_num___override(v___x_5999_, v___x_5998_);
return v___x_6000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6002_; uint8_t v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; 
v___x_6002_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_6003_ = 0;
v___x_6004_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_6005_ = l_Lean_registerTraceClass(v___x_6002_, v___x_6003_, v___x_6004_);
if (lean_obj_tag(v___x_6005_) == 0)
{
lean_object* v___x_6006_; lean_object* v___x_6007_; 
lean_dec_ref_known(v___x_6005_, 1);
v___x_6006_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
v___x_6007_ = l_Lean_registerTraceClass(v___x_6006_, v___x_6003_, v___x_6004_);
return v___x_6007_;
}
else
{
return v___x_6005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2____boxed(lean_object* v_a_6008_){
_start:
{
lean_object* v_res_6009_; 
v_res_6009_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_();
return v_res_6009_;
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
res = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux___regBuiltin_Lean_Elab_Term_elabListLitAux__1();
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
