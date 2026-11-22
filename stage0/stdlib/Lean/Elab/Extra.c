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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__27;
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
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
lean_ctor_set(v___x_1523_, 2, v___x_1522_);
lean_ctor_set(v___x_1523_, 3, v___x_1522_);
lean_ctor_set(v___x_1523_, 4, v___x_1521_);
lean_ctor_set(v___x_1523_, 5, v___x_1521_);
lean_ctor_set(v___x_1523_, 6, v___x_1521_);
lean_ctor_set(v___x_1523_, 7, v___x_1521_);
lean_ctor_set(v___x_1523_, 8, v___x_1521_);
lean_ctor_set(v___x_1523_, 9, v___x_1521_);
lean_ctor_set(v___x_1523_, 10, v___x_1521_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = lean_unsigned_to_nat(32u);
v___x_1525_ = lean_mk_empty_array_with_capacity(v___x_1524_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1527_ = ((size_t)5ULL);
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = lean_unsigned_to_nat(32u);
v___x_1530_ = lean_mk_empty_array_with_capacity(v___x_1529_);
v___x_1531_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__3);
v___x_1532_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___x_1530_);
lean_ctor_set(v___x_1532_, 2, v___x_1528_);
lean_ctor_set(v___x_1532_, 3, v___x_1528_);
lean_ctor_set_usize(v___x_1532_, 4, v___x_1527_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1533_ = lean_box(1);
v___x_1534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__4);
v___x_1535_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_1536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___x_1534_);
lean_ctor_set(v___x_1536_, 2, v___x_1533_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__6));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__8));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__10));
v___x_1545_ = l_Lean_stringToMessageData(v___x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__12));
v___x_1548_ = l_Lean_stringToMessageData(v___x_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__14));
v___x_1551_ = l_Lean_stringToMessageData(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__16));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__18));
v___x_1557_ = l_Lean_stringToMessageData(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__21(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__20));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__23(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__22));
v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__25(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__24));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__27(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__26));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(lean_object* v_msg_1570_, lean_object* v_declHint_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v_env_1576_; uint8_t v___x_1577_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_st_ref_get(v___y_1572_);
v_env_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc_ref(v_env_1576_);
lean_dec(v___x_1575_);
v___x_1577_ = l_Lean_Name_isAnonymous(v_declHint_1571_);
if (v___x_1577_ == 0)
{
uint8_t v_isExporting_1578_; 
v_isExporting_1578_ = lean_ctor_get_uint8(v_env_1576_, sizeof(void*)*13);
if (v_isExporting_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref(v_env_1576_);
lean_dec(v_declHint_1571_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v_msg_1570_);
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; uint8_t v___x_1581_; 
lean_inc_ref(v_env_1576_);
v___x_1580_ = l_Lean_Environment_setExporting(v_env_1576_, v___x_1577_);
lean_inc(v_declHint_1571_);
lean_inc_ref(v___x_1580_);
v___x_1581_ = l_Lean_Environment_contains(v___x_1580_, v_declHint_1571_, v_isExporting_1578_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref(v___x_1580_);
lean_dec_ref(v_env_1576_);
lean_dec(v_declHint_1571_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_msg_1570_);
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_c_1588_; lean_object* v___x_1589_; 
v___x_1583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_1584_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5);
v___x_1585_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1580_);
v___x_1586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1580_);
lean_ctor_set(v___x_1586_, 1, v___x_1583_);
lean_ctor_set(v___x_1586_, 2, v___x_1584_);
lean_ctor_set(v___x_1586_, 3, v___x_1585_);
lean_inc(v_declHint_1571_);
v___x_1587_ = l_Lean_MessageData_ofConstName(v_declHint_1571_, v___x_1577_);
v_c_1588_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1588_, 0, v___x_1586_);
lean_ctor_set(v_c_1588_, 1, v___x_1587_);
v___x_1589_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1580_, v_declHint_1571_);
lean_dec_ref(v___x_1580_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref(v_env_1576_);
lean_dec(v_declHint_1571_);
v___x_1590_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v_c_1588_);
v___x_1592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_MessageData_note(v___x_1593_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_msg_1570_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1650_; 
v_val_1597_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1599_ = v___x_1589_;
v_isShared_1600_ = v_isSharedCheck_1650_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_val_1597_);
lean_dec(v___x_1589_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1650_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v_modules_1602_; lean_object* v_moduleNames_1603_; lean_object* v_mod_1604_; uint8_t v___x_1619_; 
v___x_1601_ = l_Lean_Environment_header(v_env_1576_);
lean_dec_ref(v_env_1576_);
v_modules_1602_ = lean_ctor_get(v___x_1601_, 3);
lean_inc_ref(v_modules_1602_);
v_moduleNames_1603_ = lean_ctor_get(v___x_1601_, 4);
lean_inc_ref(v_moduleNames_1603_);
lean_dec_ref(v___x_1601_);
v_mod_1604_ = lean_array_get(v___x_1574_, v_moduleNames_1603_, v_val_1597_);
lean_dec_ref(v_moduleNames_1603_);
v___x_1619_ = l_Lean_isPrivateName(v_declHint_1571_);
lean_dec(v_declHint_1571_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = lean_array_get_size(v_modules_1602_);
v___x_1621_ = lean_nat_dec_lt(v_val_1597_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_dec_ref(v_modules_1602_);
lean_dec(v_val_1597_);
goto v___jp_1605_;
}
else
{
lean_object* v___x_1622_; lean_object* v_toImport_1623_; uint8_t v_isExported_1624_; 
v___x_1622_ = lean_array_fget(v_modules_1602_, v_val_1597_);
lean_dec(v_val_1597_);
lean_dec_ref(v_modules_1602_);
v_toImport_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc_ref(v_toImport_1623_);
lean_dec(v___x_1622_);
v_isExported_1624_ = lean_ctor_get_uint8(v_toImport_1623_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1623_);
if (v_isExported_1624_ == 0)
{
goto v___jp_1605_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_del_object(v___x_1599_);
v___x_1625_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v_c_1588_);
v___x_1627_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = l_Lean_MessageData_ofName(v_mod_1604_);
lean_inc_ref(v___x_1629_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__21);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v___x_1629_);
v___x_1634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__23);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_MessageData_note(v___x_1635_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_msg_1570_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec_ref(v_modules_1602_);
lean_del_object(v___x_1599_);
lean_dec(v_val_1597_);
v___x_1639_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_c_1588_);
v___x_1641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__25);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = l_Lean_MessageData_ofName(v_mod_1604_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__27);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = l_Lean_MessageData_note(v___x_1646_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_msg_1570_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
v___jp_1605_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1606_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v_c_1588_);
v___x_1608_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_MessageData_ofName(v_mod_1604_);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = l_Lean_MessageData_note(v___x_1613_);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v_msg_1570_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1615_);
v___x_1617_ = v___x_1599_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1651_; 
lean_dec_ref(v_env_1576_);
lean_dec(v_declHint_1571_);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v_msg_1570_);
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1652_, lean_object* v_declHint_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1652_, v_declHint_1653_, v___y_1654_);
lean_dec(v___y_1654_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(lean_object* v_msg_1657_, lean_object* v_declHint_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1676_; 
v___x_1666_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_1657_, v_declHint_1658_, v___y_1664_);
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1671_ = l_Lean_unknownIdentifierMessageTag;
v___x_1672_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v_a_1667_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1672_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4___boxed(lean_object* v_msg_1677_, lean_object* v_declHint_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(v_msg_1677_, v_declHint_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_1687_, lean_object* v_msg_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_toCold_1696_; lean_object* v_currRecDepth_1697_; lean_object* v_ref_1698_; uint16_t v_optionFlags_1699_; uint8_t v_suppressElabErrors_1700_; uint8_t v_checkDeprecated_1701_; uint8_t v_isRecordingDeps_1702_; lean_object* v_ref_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_toCold_1696_ = lean_ctor_get(v___y_1693_, 0);
v_currRecDepth_1697_ = lean_ctor_get(v___y_1693_, 1);
v_ref_1698_ = lean_ctor_get(v___y_1693_, 2);
v_optionFlags_1699_ = lean_ctor_get_uint16(v___y_1693_, sizeof(void*)*3);
v_suppressElabErrors_1700_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*3 + 2);
v_checkDeprecated_1701_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1702_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*3 + 4);
v_ref_1703_ = l_Lean_replaceRef(v_ref_1687_, v_ref_1698_);
lean_inc(v_currRecDepth_1697_);
lean_inc_ref(v_toCold_1696_);
v___x_1704_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1704_, 0, v_toCold_1696_);
lean_ctor_set(v___x_1704_, 1, v_currRecDepth_1697_);
lean_ctor_set(v___x_1704_, 2, v_ref_1703_);
lean_ctor_set_uint16(v___x_1704_, sizeof(void*)*3, v_optionFlags_1699_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*3 + 2, v_suppressElabErrors_1700_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*3 + 3, v_checkDeprecated_1701_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*3 + 4, v_isRecordingDeps_1702_);
v___x_1705_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v_msg_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___x_1704_, v___y_1694_);
lean_dec_ref_known(v___x_1704_, 3);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1706_, lean_object* v_msg_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_1706_, v_msg_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v_ref_1706_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(lean_object* v_ref_1716_, lean_object* v_msg_1717_, lean_object* v_declHint_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; lean_object* v_a_1727_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4(v_msg_1717_, v_declHint_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_1716_, v_a_1727_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg___boxed(lean_object* v_ref_1729_, lean_object* v_msg_1730_, lean_object* v_declHint_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_1729_, v_msg_1730_, v_declHint_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v_ref_1729_);
return v_res_1739_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__0));
v___x_1742_ = l_Lean_stringToMessageData(v___x_1741_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__2));
v___x_1745_ = l_Lean_stringToMessageData(v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(lean_object* v_ref_1746_, lean_object* v_constName_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1755_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1);
v___x_1756_ = 0;
lean_inc(v_constName_1747_);
v___x_1757_ = l_Lean_MessageData_ofConstName(v_constName_1747_, v___x_1756_);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1755_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_1746_, v___x_1760_, v_constName_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___boxed(lean_object* v_ref_1762_, lean_object* v_constName_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_ref_1762_, v_constName_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v_ref_1762_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed(lean_object* v_s_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_s_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(lean_object* v_ref_1827_, uint8_t v_kind_1828_, lean_object* v_f_1829_, lean_object* v_lhs_1830_, lean_object* v_rhs_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_1840_ = 0;
lean_inc(v_f_1829_);
v___x_1841_ = l_Lean_Elab_Term_resolveId_x3f(v_f_1829_, v___x_1839_, v___x_1840_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1876_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1876_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1876_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
if (lean_obj_tag(v_a_1842_) == 1)
{
lean_object* v_val_1846_; lean_object* v___y_1848_; lean_object* v_rhs_1849_; lean_object* v_lhs_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; uint8_t v___x_1868_; uint8_t v___x_1869_; 
lean_dec(v_f_1829_);
v_val_1846_ = lean_ctor_get(v_a_1842_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v_a_1842_, 1);
v___x_1868_ = 2;
v___x_1869_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_1828_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_lhs_1830_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v_lhs_1855_ = v_a_1871_;
v___y_1856_ = v_a_1832_;
v___y_1857_ = v_a_1833_;
v___y_1858_ = v_a_1834_;
v___y_1859_ = v_a_1835_;
v___y_1860_ = v_a_1836_;
v___y_1861_ = v_a_1837_;
goto v___jp_1854_;
}
else
{
lean_dec(v_val_1846_);
lean_del_object(v___x_1844_);
lean_dec(v_rhs_1831_);
lean_dec(v_ref_1827_);
return v___x_1870_;
}
}
else
{
lean_object* v___x_1872_; 
v___x_1872_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_lhs_1830_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v_lhs_1855_ = v_a_1873_;
v___y_1856_ = v_a_1832_;
v___y_1857_ = v_a_1833_;
v___y_1858_ = v_a_1834_;
v___y_1859_ = v_a_1835_;
v___y_1860_ = v_a_1836_;
v___y_1861_ = v_a_1837_;
goto v___jp_1854_;
}
else
{
lean_dec(v_val_1846_);
lean_del_object(v___x_1844_);
lean_dec(v_rhs_1831_);
lean_dec(v_ref_1827_);
return v___x_1872_;
}
}
v___jp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1850_, 0, v_ref_1827_);
lean_ctor_set(v___x_1850_, 1, v_val_1846_);
lean_ctor_set(v___x_1850_, 2, v___y_1848_);
lean_ctor_set(v___x_1850_, 3, v_rhs_1849_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*4, v_kind_1828_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1850_);
v___x_1852_ = v___x_1844_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
v___jp_1854_:
{
uint8_t v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = 3;
v___x_1863_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_1828_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
v___x_1864_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_rhs_1831_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___y_1848_ = v_lhs_1855_;
v_rhs_1849_ = v_a_1865_;
goto v___jp_1847_;
}
else
{
lean_dec_ref(v_lhs_1855_);
lean_dec(v_val_1846_);
lean_del_object(v___x_1844_);
lean_dec(v_ref_1827_);
return v___x_1864_;
}
}
else
{
lean_object* v___x_1866_; 
v___x_1866_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_rhs_1831_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___y_1848_ = v_lhs_1855_;
v_rhs_1849_ = v_a_1867_;
goto v___jp_1847_;
}
else
{
lean_dec_ref(v_lhs_1855_);
lean_dec(v_val_1846_);
lean_del_object(v___x_1844_);
lean_dec(v_ref_1827_);
return v___x_1866_;
}
}
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_del_object(v___x_1844_);
lean_dec(v_a_1842_);
lean_dec(v_rhs_1831_);
lean_dec(v_lhs_1830_);
lean_dec(v_ref_1827_);
v___x_1874_ = l_Lean_Syntax_getId(v_f_1829_);
v___x_1875_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_f_1829_, v___x_1874_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_f_1829_);
return v___x_1875_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_rhs_1831_);
lean_dec(v_lhs_1830_);
lean_dec(v_f_1829_);
lean_dec(v_ref_1827_);
v_a_1877_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1841_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1841_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(lean_object* v_s_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1));
lean_inc(v_s_1885_);
v___x_1894_ = l_Lean_Syntax_isOfKind(v_s_1885_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3));
lean_inc(v_s_1885_);
v___x_1896_ = l_Lean_Syntax_isOfKind(v_s_1885_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5));
lean_inc(v_s_1885_);
v___x_1898_ = l_Lean_Syntax_isOfKind(v_s_1885_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7));
lean_inc(v_s_1885_);
v___x_1900_ = l_Lean_Syntax_isOfKind(v_s_1885_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9));
lean_inc(v_s_1885_);
v___x_1902_ = l_Lean_Syntax_isOfKind(v_s_1885_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__11));
lean_inc(v_s_1885_);
v___x_1904_ = l_Lean_Syntax_isOfKind(v_s_1885_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v_toCold_1905_; lean_object* v_currRecDepth_1906_; lean_object* v_ref_1907_; uint16_t v_optionFlags_1908_; uint8_t v_suppressElabErrors_1909_; uint8_t v_checkDeprecated_1910_; uint8_t v_isRecordingDeps_1911_; lean_object* v_ref_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_toCold_1905_ = lean_ctor_get(v_a_1890_, 0);
v_currRecDepth_1906_ = lean_ctor_get(v_a_1890_, 1);
v_ref_1907_ = lean_ctor_get(v_a_1890_, 2);
v_optionFlags_1908_ = lean_ctor_get_uint16(v_a_1890_, sizeof(void*)*3);
v_suppressElabErrors_1909_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*3 + 2);
v_checkDeprecated_1910_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1911_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*3 + 4);
v_ref_1912_ = l_Lean_replaceRef(v_s_1885_, v_ref_1907_);
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
lean_inc(v_s_1885_);
v___x_1914_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v___x_1913_, v_a_1891_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
if (lean_obj_tag(v_a_1915_) == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v___x_1913_, v_a_1891_);
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
lean_inc(v_s_1885_);
v___f_1921_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1921_, 0, v_s_1885_);
lean_closure_set(v___f_1921_, 1, v___x_1920_);
lean_closure_set(v___f_1921_, 2, v_fst_1918_);
lean_closure_set(v___f_1921_, 3, v_snd_1919_);
v___x_1922_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1885_, v_snd_1919_, v___f_1921_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v___x_1913_, v_a_1891_);
lean_dec_ref_known(v___x_1913_, 3);
return v___x_1922_;
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref_known(v___x_1913_, 3);
lean_dec(v_s_1885_);
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
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_1931_);
v___x_1933_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__13));
lean_inc(v___x_1932_);
v___x_1934_ = l_Lean_Syntax_isOfKind(v___x_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v_toCold_1935_; lean_object* v_currRecDepth_1936_; lean_object* v_ref_1937_; uint16_t v_optionFlags_1938_; uint8_t v_suppressElabErrors_1939_; uint8_t v_checkDeprecated_1940_; uint8_t v_isRecordingDeps_1941_; lean_object* v_ref_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v___x_1932_);
v_toCold_1935_ = lean_ctor_get(v_a_1890_, 0);
v_currRecDepth_1936_ = lean_ctor_get(v_a_1890_, 1);
v_ref_1937_ = lean_ctor_get(v_a_1890_, 2);
v_optionFlags_1938_ = lean_ctor_get_uint16(v_a_1890_, sizeof(void*)*3);
v_suppressElabErrors_1939_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*3 + 2);
v_checkDeprecated_1940_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1941_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*3 + 4);
v_ref_1942_ = l_Lean_replaceRef(v_s_1885_, v_ref_1937_);
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
lean_inc(v_s_1885_);
v___x_1944_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v___x_1943_, v_a_1891_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
if (lean_obj_tag(v_a_1945_) == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v___x_1943_, v_a_1891_);
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
lean_inc(v_s_1885_);
v___f_1951_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1951_, 0, v_s_1885_);
lean_closure_set(v___f_1951_, 1, v___x_1950_);
lean_closure_set(v___f_1951_, 2, v_fst_1948_);
lean_closure_set(v___f_1951_, 3, v_snd_1949_);
v___x_1952_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1885_, v_snd_1949_, v___f_1951_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v___x_1943_, v_a_1891_);
lean_dec_ref_known(v___x_1943_, 3);
return v___x_1952_;
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref_known(v___x_1943_, 3);
lean_dec(v_s_1885_);
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
lean_object* v___x_1961_; lean_object* v_h_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1961_ = lean_unsigned_to_nat(1u);
v_h_1962_ = l_Lean_Syntax_getArg(v___x_1932_, v___x_1961_);
lean_dec(v___x_1932_);
v___x_1963_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__15));
lean_inc(v_h_1962_);
v___x_1964_ = l_Lean_Syntax_isOfKind(v_h_1962_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v_toCold_1965_; lean_object* v_currRecDepth_1966_; lean_object* v_ref_1967_; uint16_t v_optionFlags_1968_; uint8_t v_suppressElabErrors_1969_; uint8_t v_checkDeprecated_1970_; uint8_t v_isRecordingDeps_1971_; lean_object* v_ref_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec(v_h_1962_);
v_toCold_1965_ = lean_ctor_get(v_a_1890_, 0);
v_currRecDepth_1966_ = lean_ctor_get(v_a_1890_, 1);
v_ref_1967_ = lean_ctor_get(v_a_1890_, 2);
v_optionFlags_1968_ = lean_ctor_get_uint16(v_a_1890_, sizeof(void*)*3);
v_suppressElabErrors_1969_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*3 + 2);
v_checkDeprecated_1970_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1971_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*3 + 4);
v_ref_1972_ = l_Lean_replaceRef(v_s_1885_, v_ref_1967_);
lean_inc(v_currRecDepth_1966_);
lean_inc_ref(v_toCold_1965_);
v___x_1973_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1973_, 0, v_toCold_1965_);
lean_ctor_set(v___x_1973_, 1, v_currRecDepth_1966_);
lean_ctor_set(v___x_1973_, 2, v_ref_1972_);
lean_ctor_set_uint16(v___x_1973_, sizeof(void*)*3, v_optionFlags_1968_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*3 + 2, v_suppressElabErrors_1969_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*3 + 3, v_checkDeprecated_1970_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*3 + 4, v_isRecordingDeps_1971_);
lean_inc(v_s_1885_);
v___x_1974_ = l_Lean_Elab_Term_expandMacroReportingDeprecated_x3f(v_s_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v___x_1973_, v_a_1891_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
if (lean_obj_tag(v_a_1975_) == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v___x_1973_, v_a_1891_);
lean_dec_ref_known(v___x_1973_, 3);
return v___x_1976_;
}
else
{
lean_object* v_val_1977_; lean_object* v_fst_1978_; lean_object* v_snd_1979_; lean_object* v___x_1980_; lean_object* v___f_1981_; lean_object* v___x_1982_; 
v_val_1977_ = lean_ctor_get(v_a_1975_, 0);
lean_inc(v_val_1977_);
lean_dec_ref_known(v_a_1975_, 1);
v_fst_1978_ = lean_ctor_get(v_val_1977_, 0);
lean_inc(v_fst_1978_);
v_snd_1979_ = lean_ctor_get(v_val_1977_, 1);
lean_inc_n(v_snd_1979_, 3);
lean_dec(v_val_1977_);
v___x_1980_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___boxed), 8, 1);
lean_closure_set(v___x_1980_, 0, v_snd_1979_);
lean_inc(v_s_1885_);
v___f_1981_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1981_, 0, v_s_1885_);
lean_closure_set(v___f_1981_, 1, v___x_1980_);
lean_closure_set(v___f_1981_, 2, v_fst_1978_);
lean_closure_set(v___f_1981_, 3, v_snd_1979_);
v___x_1982_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_s_1885_, v_snd_1979_, v___f_1981_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v___x_1973_, v_a_1891_);
lean_dec_ref_known(v___x_1973_, 3);
return v___x_1982_;
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec_ref_known(v___x_1973_, 3);
lean_dec(v_s_1885_);
v_a_1983_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1974_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1974_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1991_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_1961_);
v___x_1992_ = l_Lean_TSyntax_getHygieneInfo(v_h_1962_);
lean_dec(v_h_1962_);
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_inc(v___x_1991_);
v___x_1994_ = l_Lean_Elab_Term_hasCDot(v___x_1991_, v___x_1993_);
lean_dec_ref_known(v___x_1993_, 1);
if (v___x_1994_ == 0)
{
lean_dec(v_s_1885_);
v_s_1885_ = v___x_1991_;
goto _start;
}
else
{
lean_object* v___x_1996_; 
lean_dec(v___x_1991_);
v___x_1996_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf(v_s_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_1996_;
}
}
}
}
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; 
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_1997_);
v___x_1999_ = lean_unsigned_to_nat(2u);
v___x_2000_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_1999_);
v___x_2001_ = lean_unsigned_to_nat(3u);
v___x_2002_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2001_);
v___x_2003_ = 3;
v___x_2004_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1885_, v___x_2003_, v___x_1998_, v___x_2000_, v___x_2002_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_2004_;
}
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2005_);
v___x_2007_ = lean_unsigned_to_nat(2u);
v___x_2008_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2007_);
v___x_2009_ = lean_unsigned_to_nat(3u);
v___x_2010_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2009_);
v___x_2011_ = 2;
v___x_2012_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1885_, v___x_2011_, v___x_2006_, v___x_2008_, v___x_2010_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_2012_;
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2013_ = lean_unsigned_to_nat(1u);
v___x_2014_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2013_);
v___x_2015_ = lean_unsigned_to_nat(2u);
v___x_2016_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2015_);
v___x_2017_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(v_s_1885_, v___x_2014_, v___x_2016_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_2017_;
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; lean_object* v___x_2025_; 
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2018_);
v___x_2020_ = lean_unsigned_to_nat(2u);
v___x_2021_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2020_);
v___x_2022_ = lean_unsigned_to_nat(3u);
v___x_2023_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2022_);
v___x_2024_ = 1;
v___x_2025_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1885_, v___x_2024_, v___x_2019_, v___x_2021_, v___x_2023_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_2025_;
}
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2026_);
v___x_2028_ = lean_unsigned_to_nat(2u);
v___x_2029_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2028_);
v___x_2030_ = lean_unsigned_to_nat(3u);
v___x_2031_ = l_Lean_Syntax_getArg(v_s_1885_, v___x_2030_);
v___x_2032_ = 0;
v___x_2033_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_s_1885_, v___x_2032_, v___x_2027_, v___x_2029_, v___x_2031_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_2033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(lean_object* v_ref_2034_, lean_object* v_f_2035_, lean_object* v_arg_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_2045_ = 0;
lean_inc(v_f_2035_);
v___x_2046_ = l_Lean_Elab_Term_resolveId_x3f(v_f_2035_, v___x_2044_, v___x_2045_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
if (lean_obj_tag(v_a_2047_) == 1)
{
lean_object* v_val_2048_; lean_object* v___x_2049_; 
lean_dec(v_f_2035_);
v_val_2048_ = lean_ctor_get(v_a_2047_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v_a_2047_, 1);
v___x_2049_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_arg_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2058_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2058_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2058_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2054_, 0, v_ref_2034_);
lean_ctor_set(v___x_2054_, 1, v_val_2048_);
lean_ctor_set(v___x_2054_, 2, v_a_2050_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2054_);
v___x_2056_ = v___x_2052_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
lean_dec(v_val_2048_);
lean_dec(v_ref_2034_);
return v___x_2049_;
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_dec(v_a_2047_);
lean_dec(v_arg_2036_);
lean_dec(v_ref_2034_);
v___x_2059_ = l_Lean_Syntax_getId(v_f_2035_);
v___x_2060_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_f_2035_, v___x_2059_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_f_2035_);
return v___x_2060_;
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_arg_2036_);
lean_dec(v_f_2035_);
lean_dec(v_ref_2034_);
v_a_2061_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2046_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2046_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___boxed(lean_object* v_ref_2069_, lean_object* v_f_2070_, lean_object* v_arg_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp(v_ref_2069_, v_f_2070_, v_arg_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp___boxed(lean_object* v_ref_2080_, lean_object* v_kind_2081_, lean_object* v_f_2082_, lean_object* v_lhs_2083_, lean_object* v_rhs_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
uint8_t v_kind_boxed_2092_; lean_object* v_res_2093_; 
v_kind_boxed_2092_ = lean_unbox(v_kind_2081_);
v_res_2093_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processBinOp(v_ref_2080_, v_kind_boxed_2092_, v_f_2082_, v_lhs_2083_, v_rhs_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2(lean_object* v_00_u03b1_2094_, lean_object* v_ref_2095_, lean_object* v_constName_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v_ref_2095_, v_constName_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___boxed(lean_object* v_00_u03b1_2105_, lean_object* v_ref_2106_, lean_object* v_constName_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2(v_00_u03b1_2105_, v_ref_2106_, v_constName_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v_ref_2106_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2(lean_object* v_00_u03b1_2116_, lean_object* v_ref_2117_, lean_object* v_msg_2118_, lean_object* v_declHint_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___redArg(v_ref_2117_, v_msg_2118_, v_declHint_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_ref_2129_, lean_object* v_msg_2130_, lean_object* v_declHint_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2(v_00_u03b1_2128_, v_ref_2129_, v_msg_2130_, v_declHint_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v_ref_2129_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5(lean_object* v_msg_2140_, lean_object* v_declHint_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg(v_msg_2140_, v_declHint_2141_, v___y_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_2150_, lean_object* v_declHint_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5(v_msg_2150_, v_declHint_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_2160_, lean_object* v_ref_2161_, lean_object* v_msg_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___redArg(v_ref_2161_, v_msg_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2171_, lean_object* v_ref_2172_, lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__5(v_00_u03b1_2171_, v_ref_2172_, v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v_ref_2172_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(lean_object* v_s_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go(v_s_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; uint8_t v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2192_ = 0;
v___x_2193_ = 0;
v___x_2194_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_2192_, v___x_2193_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; 
v_unused_2202_ = lean_ctor_get(v___x_2194_, 0);
lean_dec(v_unused_2202_);
v___x_2196_ = v___x_2194_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_dec(v___x_2194_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v_a_2191_);
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2191_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v_a_2191_);
v_a_2203_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2194_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2194_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree___boxed(lean_object* v_s_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v_s_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0(lean_object* v_toType_2220_, uint8_t v___x_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Meta_coerceSimple_x3f(v_x_2222_, v_toType_2220_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2244_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2244_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2244_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
if (lean_obj_tag(v_a_2231_) == 1)
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
lean_dec_ref_known(v_a_2231_, 1);
v___x_2235_ = lean_box(v___x_2221_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2235_);
v___x_2237_ = v___x_2233_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
else
{
uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
lean_dec(v_a_2231_);
v___x_2239_ = 0;
v___x_2240_ = lean_box(v___x_2239_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2240_);
v___x_2242_ = v___x_2233_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
v_a_2245_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2230_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2230_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0___boxed(lean_object* v_toType_2253_, lean_object* v___x_2254_, lean_object* v_x_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
uint8_t v___x_1729__boxed_2263_; lean_object* v_res_2264_; 
v___x_1729__boxed_2263_ = lean_unbox(v___x_2254_);
v_res_2264_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0(v_toType_2253_, v___x_1729__boxed_2263_, v_x_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v_b_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc(v___y_2267_);
lean_inc_ref(v___y_2266_);
v___x_2274_ = lean_apply_8(v_k_2265_, v_b_2268_, v___y_2266_, v___y_2267_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, lean_box(0));
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v_b_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0(v_k_2275_, v___y_2276_, v___y_2277_, v_b_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(lean_object* v_name_2285_, uint8_t v_bi_2286_, lean_object* v_type_2287_, lean_object* v_k_2288_, uint8_t v_kind_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___f_2297_; lean_object* v___x_2298_; 
lean_inc(v___y_2291_);
lean_inc_ref(v___y_2290_);
v___f_2297_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2297_, 0, v_k_2288_);
lean_closure_set(v___f_2297_, 1, v___y_2290_);
lean_closure_set(v___f_2297_, 2, v___y_2291_);
v___x_2298_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2285_, v_bi_2286_, v_type_2287_, v___f_2297_, v_kind_2289_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2298_) == 0)
{
return v___x_2298_;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg___boxed(lean_object* v_name_2307_, lean_object* v_bi_2308_, lean_object* v_type_2309_, lean_object* v_k_2310_, lean_object* v_kind_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
uint8_t v_bi_boxed_2319_; uint8_t v_kind_boxed_2320_; lean_object* v_res_2321_; 
v_bi_boxed_2319_ = lean_unbox(v_bi_2308_);
v_kind_boxed_2320_ = lean_unbox(v_kind_2311_);
v_res_2321_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_2307_, v_bi_boxed_2319_, v_type_2309_, v_k_2310_, v_kind_boxed_2320_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(lean_object* v_name_2322_, lean_object* v_type_2323_, lean_object* v_k_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = 0;
v___x_2333_ = 0;
v___x_2334_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_2322_, v___x_2332_, v_type_2323_, v_k_2324_, v___x_2333_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg___boxed(lean_object* v_name_2335_, lean_object* v_type_2336_, lean_object* v_k_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v_name_2335_, v_type_2336_, v_k_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(lean_object* v_fromType_2349_, lean_object* v_toType_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v_env_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; uint8_t v___x_2362_; 
v___x_2358_ = lean_st_ref_get(v_a_2356_);
v_env_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc_ref(v_env_2359_);
lean_dec(v___x_2358_);
v___x_2360_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___closed__1));
v___x_2361_ = 1;
v___x_2362_ = l_Lean_Environment_contains(v_env_2359_, v___x_2360_, v___x_2361_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v_toType_2350_);
lean_dec_ref(v_fromType_2349_);
v___x_2363_ = lean_box(v___x_2362_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___f_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2365_ = lean_box(v___x_2361_);
v___f_2366_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2366_, 0, v_toType_2350_);
lean_closure_set(v___f_2366_, 1, v___x_2365_);
v___x_2367_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_mkTree___closed__1));
v___x_2368_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v___x_2367_, v_fromType_2349_, v___f_2366_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe___boxed(lean_object* v_fromType_2369_, lean_object* v_toType_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v_fromType_2369_, v_toType_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0(lean_object* v_00_u03b1_2379_, lean_object* v_name_2380_, uint8_t v_bi_2381_, lean_object* v_type_2382_, lean_object* v_k_2383_, uint8_t v_kind_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___redArg(v_name_2380_, v_bi_2381_, v_type_2382_, v_k_2383_, v_kind_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2393_, lean_object* v_name_2394_, lean_object* v_bi_2395_, lean_object* v_type_2396_, lean_object* v_k_2397_, lean_object* v_kind_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
uint8_t v_bi_boxed_2406_; uint8_t v_kind_boxed_2407_; lean_object* v_res_2408_; 
v_bi_boxed_2406_ = lean_unbox(v_bi_2395_);
v_kind_boxed_2407_ = lean_unbox(v_kind_2398_);
v_res_2408_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0_spec__0(v_00_u03b1_2393_, v_name_2394_, v_bi_boxed_2406_, v_type_2396_, v_k_2397_, v_kind_boxed_2407_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0(lean_object* v_00_u03b1_2409_, lean_object* v_name_2410_, lean_object* v_type_2411_, lean_object* v_k_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___redArg(v_name_2410_, v_type_2411_, v_k_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0___boxed(lean_object* v_00_u03b1_2421_, lean_object* v_name_2422_, lean_object* v_type_2423_, lean_object* v_k_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe_spec__0(v_00_u03b1_2421_, v_name_2422_, v_type_2423_, v_k_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2432_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(lean_object* v_x_2433_){
_start:
{
switch(lean_obj_tag(v_x_2433_))
{
case 2:
{
uint8_t v___x_2434_; 
v___x_2434_ = 1;
return v___x_2434_;
}
case 5:
{
lean_object* v_fn_2435_; 
v_fn_2435_ = lean_ctor_get(v_x_2433_, 0);
v_x_2433_ = v_fn_2435_;
goto _start;
}
case 8:
{
lean_object* v_body_2437_; 
v_body_2437_ = lean_ctor_get(v_x_2433_, 3);
v_x_2433_ = v_body_2437_;
goto _start;
}
case 10:
{
lean_object* v_expr_2439_; 
v_expr_2439_ = lean_ctor_get(v_x_2433_, 1);
v_x_2433_ = v_expr_2439_;
goto _start;
}
default: 
{
uint8_t v___x_2441_; 
v___x_2441_ = 0;
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown___boxed(lean_object* v_x_2442_){
_start:
{
uint8_t v_res_2443_; lean_object* v_r_2444_; 
v_res_2443_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v_x_2442_);
lean_dec_ref(v_x_2442_);
v_r_2444_ = lean_box(v_res_2443_);
return v_r_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(lean_object* v_e_2445_, lean_object* v___y_2446_){
_start:
{
uint8_t v___x_2448_; 
v___x_2448_ = l_Lean_Expr_hasMVar(v_e_2445_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v_e_2445_);
return v___x_2449_;
}
else
{
lean_object* v___x_2450_; lean_object* v_mctx_2451_; lean_object* v___x_2452_; lean_object* v_fst_2453_; lean_object* v_snd_2454_; lean_object* v___x_2455_; lean_object* v_cache_2456_; lean_object* v_zetaDeltaFVarIds_2457_; lean_object* v_postponed_2458_; lean_object* v_diag_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2468_; 
v___x_2450_ = lean_st_ref_get(v___y_2446_);
v_mctx_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc_ref(v_mctx_2451_);
lean_dec(v___x_2450_);
v___x_2452_ = l_Lean_instantiateMVarsCore(v_mctx_2451_, v_e_2445_);
v_fst_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_fst_2453_);
v_snd_2454_ = lean_ctor_get(v___x_2452_, 1);
lean_inc(v_snd_2454_);
lean_dec_ref(v___x_2452_);
v___x_2455_ = lean_st_ref_take(v___y_2446_);
v_cache_2456_ = lean_ctor_get(v___x_2455_, 1);
v_zetaDeltaFVarIds_2457_ = lean_ctor_get(v___x_2455_, 2);
v_postponed_2458_ = lean_ctor_get(v___x_2455_, 3);
v_diag_2459_ = lean_ctor_get(v___x_2455_, 4);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2455_, 0);
lean_dec(v_unused_2469_);
v___x_2461_ = v___x_2455_;
v_isShared_2462_ = v_isSharedCheck_2468_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_diag_2459_);
lean_inc(v_postponed_2458_);
lean_inc(v_zetaDeltaFVarIds_2457_);
lean_inc(v_cache_2456_);
lean_dec(v___x_2455_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2468_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v_snd_2454_);
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_snd_2454_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_cache_2456_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_zetaDeltaFVarIds_2457_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_postponed_2458_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_diag_2459_);
v___x_2464_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_st_ref_put(v___y_2446_, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v_fst_2453_);
return v___x_2466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg___boxed(lean_object* v_e_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_e_2470_, v___y_2471_);
lean_dec(v___y_2471_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0(lean_object* v_e_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_e_2474_, v___y_2479_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___boxed(lean_object* v_e_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0(v_e_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0(lean_object* v_k_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___x_2503_; 
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
lean_inc(v___y_2495_);
v___x_2503_ = lean_apply_8(v_k_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, lean_box(0));
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0(v_k_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(lean_object* v_k_2514_, uint8_t v_allowLevelAssignments_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___f_2524_; lean_object* v___x_2525_; 
lean_inc(v___y_2518_);
lean_inc_ref(v___y_2517_);
lean_inc(v___y_2516_);
v___f_2524_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2524_, 0, v_k_2514_);
lean_closure_set(v___f_2524_, 1, v___y_2516_);
lean_closure_set(v___f_2524_, 2, v___y_2517_);
lean_closure_set(v___f_2524_, 3, v___y_2518_);
v___x_2525_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2515_, v___f_2524_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
if (lean_obj_tag(v___x_2525_) == 0)
{
return v___x_2525_;
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg___boxed(lean_object* v_k_2534_, lean_object* v_allowLevelAssignments_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2544_; lean_object* v_res_2545_; 
v_allowLevelAssignments_boxed_2544_ = lean_unbox(v_allowLevelAssignments_2535_);
v_res_2545_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v_k_2534_, v_allowLevelAssignments_boxed_2544_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1(lean_object* v_00_u03b1_2546_, lean_object* v_k_2547_, uint8_t v_allowLevelAssignments_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v_k_2547_, v_allowLevelAssignments_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___boxed(lean_object* v_00_u03b1_2558_, lean_object* v_k_2559_, lean_object* v_allowLevelAssignments_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2569_; lean_object* v_res_2570_; 
v_allowLevelAssignments_boxed_2569_ = lean_unbox(v_allowLevelAssignments_2560_);
v_res_2570_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1(v_00_u03b1_2558_, v_k_2559_, v_allowLevelAssignments_boxed_2569_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0(uint8_t v___x_2571_, lean_object* v_val_2572_, lean_object* v___x_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; uint8_t v_foApprox_2583_; uint8_t v_ctxApprox_2584_; uint8_t v_quasiPatternApprox_2585_; uint8_t v_constApprox_2586_; uint8_t v_unificationHints_2587_; uint8_t v_proofIrrelevance_2588_; uint8_t v_assignSyntheticOpaque_2589_; uint8_t v_offsetCnstrs_2590_; uint8_t v_transparency_2591_; uint8_t v_etaStruct_2592_; uint8_t v_univApprox_2593_; uint8_t v_iota_2594_; uint8_t v_beta_2595_; uint8_t v_proj_2596_; uint8_t v_zeta_2597_; uint8_t v_zetaDelta_2598_; uint8_t v_zetaUnused_2599_; uint8_t v_zetaHave_2600_; uint8_t v_canUnfoldPredicateConfig_2601_; uint8_t v_stringLitToCtor_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2623_; 
v___x_2582_ = l_Lean_Meta_Context_config(v___y_2577_);
v_foApprox_2583_ = lean_ctor_get_uint8(v___x_2582_, 0);
v_ctxApprox_2584_ = lean_ctor_get_uint8(v___x_2582_, 1);
v_quasiPatternApprox_2585_ = lean_ctor_get_uint8(v___x_2582_, 2);
v_constApprox_2586_ = lean_ctor_get_uint8(v___x_2582_, 3);
v_unificationHints_2587_ = lean_ctor_get_uint8(v___x_2582_, 5);
v_proofIrrelevance_2588_ = lean_ctor_get_uint8(v___x_2582_, 6);
v_assignSyntheticOpaque_2589_ = lean_ctor_get_uint8(v___x_2582_, 7);
v_offsetCnstrs_2590_ = lean_ctor_get_uint8(v___x_2582_, 8);
v_transparency_2591_ = lean_ctor_get_uint8(v___x_2582_, 9);
v_etaStruct_2592_ = lean_ctor_get_uint8(v___x_2582_, 10);
v_univApprox_2593_ = lean_ctor_get_uint8(v___x_2582_, 11);
v_iota_2594_ = lean_ctor_get_uint8(v___x_2582_, 12);
v_beta_2595_ = lean_ctor_get_uint8(v___x_2582_, 13);
v_proj_2596_ = lean_ctor_get_uint8(v___x_2582_, 14);
v_zeta_2597_ = lean_ctor_get_uint8(v___x_2582_, 15);
v_zetaDelta_2598_ = lean_ctor_get_uint8(v___x_2582_, 16);
v_zetaUnused_2599_ = lean_ctor_get_uint8(v___x_2582_, 17);
v_zetaHave_2600_ = lean_ctor_get_uint8(v___x_2582_, 18);
v_canUnfoldPredicateConfig_2601_ = lean_ctor_get_uint8(v___x_2582_, 19);
v_stringLitToCtor_2602_ = lean_ctor_get_uint8(v___x_2582_, 20);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2604_ = v___x_2582_;
v_isShared_2605_ = v_isSharedCheck_2623_;
goto v_resetjp_2603_;
}
else
{
lean_dec(v___x_2582_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2623_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
uint8_t v_trackZetaDelta_2606_; lean_object* v_zetaDeltaSet_2607_; lean_object* v_lctx_2608_; lean_object* v_localInstances_2609_; lean_object* v_defEqCtx_x3f_2610_; lean_object* v_synthPendingDepth_2611_; lean_object* v_customCanUnfoldPredicate_x3f_2612_; uint8_t v_univApprox_2613_; uint8_t v_inTypeClassResolution_2614_; uint8_t v_cacheInferType_2615_; lean_object* v___x_2617_; 
v_trackZetaDelta_2606_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*7);
v_zetaDeltaSet_2607_ = lean_ctor_get(v___y_2577_, 1);
v_lctx_2608_ = lean_ctor_get(v___y_2577_, 2);
v_localInstances_2609_ = lean_ctor_get(v___y_2577_, 3);
v_defEqCtx_x3f_2610_ = lean_ctor_get(v___y_2577_, 4);
v_synthPendingDepth_2611_ = lean_ctor_get(v___y_2577_, 5);
v_customCanUnfoldPredicate_x3f_2612_ = lean_ctor_get(v___y_2577_, 6);
v_univApprox_2613_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2614_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*7 + 2);
v_cacheInferType_2615_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*7 + 3);
if (v_isShared_2605_ == 0)
{
v___x_2617_ = v___x_2604_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 0, v_foApprox_2583_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 1, v_ctxApprox_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 2, v_quasiPatternApprox_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 3, v_constApprox_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 5, v_unificationHints_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 6, v_proofIrrelevance_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 7, v_assignSyntheticOpaque_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 8, v_offsetCnstrs_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 9, v_transparency_2591_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 10, v_etaStruct_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 11, v_univApprox_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 12, v_iota_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 13, v_beta_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 14, v_proj_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 15, v_zeta_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 16, v_zetaDelta_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 17, v_zetaUnused_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 18, v_zetaHave_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 19, v_canUnfoldPredicateConfig_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, 20, v_stringLitToCtor_2602_);
v___x_2617_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
uint64_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_ctor_set_uint8(v___x_2617_, 4, v___x_2571_);
v___x_2618_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2617_);
v___x_2619_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set_uint64(v___x_2619_, sizeof(void*)*1, v___x_2618_);
lean_inc(v_customCanUnfoldPredicate_x3f_2612_);
lean_inc(v_synthPendingDepth_2611_);
lean_inc(v_defEqCtx_x3f_2610_);
lean_inc_ref(v_localInstances_2609_);
lean_inc_ref(v_lctx_2608_);
lean_inc(v_zetaDeltaSet_2607_);
v___x_2620_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v_zetaDeltaSet_2607_);
lean_ctor_set(v___x_2620_, 2, v_lctx_2608_);
lean_ctor_set(v___x_2620_, 3, v_localInstances_2609_);
lean_ctor_set(v___x_2620_, 4, v_defEqCtx_x3f_2610_);
lean_ctor_set(v___x_2620_, 5, v_synthPendingDepth_2611_);
lean_ctor_set(v___x_2620_, 6, v_customCanUnfoldPredicate_x3f_2612_);
lean_ctor_set_uint8(v___x_2620_, sizeof(void*)*7, v_trackZetaDelta_2606_);
lean_ctor_set_uint8(v___x_2620_, sizeof(void*)*7 + 1, v_univApprox_2613_);
lean_ctor_set_uint8(v___x_2620_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2614_);
lean_ctor_set_uint8(v___x_2620_, sizeof(void*)*7 + 3, v_cacheInferType_2615_);
v___x_2621_ = l_Lean_Meta_isExprDefEqGuarded(v_val_2572_, v___x_2573_, v___x_2620_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec_ref_known(v___x_2620_, 7);
return v___x_2621_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0___boxed(lean_object* v___x_2624_, lean_object* v_val_2625_, lean_object* v___x_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
uint8_t v___x_14806__boxed_2635_; lean_object* v_res_2636_; 
v___x_14806__boxed_2635_ = lean_unbox(v___x_2624_);
v_res_2636_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0(v___x_14806__boxed_2635_, v_val_2625_, v___x_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
return v_res_2636_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2637_; double v___x_2638_; 
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_float_of_nat(v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(lean_object* v_cls_2642_, lean_object* v_msg_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_ref_2649_; lean_object* v___x_2650_; lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2696_; 
v_ref_2649_ = lean_ctor_get(v___y_2646_, 2);
v___x_2650_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2696_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2696_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v_traceState_2656_; lean_object* v_env_2657_; lean_object* v_nextMacroScope_2658_; lean_object* v_ngen_2659_; lean_object* v_auxDeclNGen_2660_; lean_object* v_cache_2661_; lean_object* v_recordedDeps_2662_; lean_object* v_messages_2663_; lean_object* v_infoState_2664_; lean_object* v_snapshotTasks_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2695_; 
v___x_2655_ = lean_st_ref_take(v___y_2647_);
v_traceState_2656_ = lean_ctor_get(v___x_2655_, 4);
v_env_2657_ = lean_ctor_get(v___x_2655_, 0);
v_nextMacroScope_2658_ = lean_ctor_get(v___x_2655_, 1);
v_ngen_2659_ = lean_ctor_get(v___x_2655_, 2);
v_auxDeclNGen_2660_ = lean_ctor_get(v___x_2655_, 3);
v_cache_2661_ = lean_ctor_get(v___x_2655_, 5);
v_recordedDeps_2662_ = lean_ctor_get(v___x_2655_, 6);
v_messages_2663_ = lean_ctor_get(v___x_2655_, 7);
v_infoState_2664_ = lean_ctor_get(v___x_2655_, 8);
v_snapshotTasks_2665_ = lean_ctor_get(v___x_2655_, 9);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2667_ = v___x_2655_;
v_isShared_2668_ = v_isSharedCheck_2695_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_snapshotTasks_2665_);
lean_inc(v_infoState_2664_);
lean_inc(v_messages_2663_);
lean_inc(v_recordedDeps_2662_);
lean_inc(v_cache_2661_);
lean_inc(v_traceState_2656_);
lean_inc(v_auxDeclNGen_2660_);
lean_inc(v_ngen_2659_);
lean_inc(v_nextMacroScope_2658_);
lean_inc(v_env_2657_);
lean_dec(v___x_2655_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2695_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint64_t v_tid_2669_; lean_object* v_traces_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2694_; 
v_tid_2669_ = lean_ctor_get_uint64(v_traceState_2656_, sizeof(void*)*1);
v_traces_2670_ = lean_ctor_get(v_traceState_2656_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_traceState_2656_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2672_ = v_traceState_2656_;
v_isShared_2673_ = v_isSharedCheck_2694_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_traces_2670_);
lean_dec(v_traceState_2656_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2694_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; double v___x_2676_; uint8_t v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0);
v___x_2677_ = 0;
v___x_2678_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1));
v___x_2679_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2679_, 0, v_cls_2642_);
lean_ctor_set(v___x_2679_, 1, v___x_2675_);
lean_ctor_set(v___x_2679_, 2, v___x_2678_);
lean_ctor_set_float(v___x_2679_, sizeof(void*)*3, v___x_2676_);
lean_ctor_set_float(v___x_2679_, sizeof(void*)*3 + 8, v___x_2676_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*3 + 16, v___x_2677_);
v___x_2680_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2));
v___x_2681_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v_a_2651_);
lean_ctor_set(v___x_2681_, 2, v___x_2680_);
lean_inc(v_ref_2649_);
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v_ref_2649_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = l_Lean_PersistentArray_push___redArg(v_traces_2670_, v___x_2682_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2683_);
v___x_2685_ = v___x_2672_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2683_);
lean_ctor_set_uint64(v_reuseFailAlloc_2693_, sizeof(void*)*1, v_tid_2669_);
v___x_2685_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2687_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 4, v___x_2685_);
v___x_2687_ = v___x_2667_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_env_2657_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_nextMacroScope_2658_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v_ngen_2659_);
lean_ctor_set(v_reuseFailAlloc_2692_, 3, v_auxDeclNGen_2660_);
lean_ctor_set(v_reuseFailAlloc_2692_, 4, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2692_, 5, v_cache_2661_);
lean_ctor_set(v_reuseFailAlloc_2692_, 6, v_recordedDeps_2662_);
lean_ctor_set(v_reuseFailAlloc_2692_, 7, v_messages_2663_);
lean_ctor_set(v_reuseFailAlloc_2692_, 8, v_infoState_2664_);
lean_ctor_set(v_reuseFailAlloc_2692_, 9, v_snapshotTasks_2665_);
v___x_2687_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2688_ = lean_st_ref_put(v___y_2647_, v___x_2687_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v___x_2674_);
v___x_2690_ = v___x_2653_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2674_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___boxed(lean_object* v_cls_2697_, lean_object* v_msg_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v_cls_2697_, v_msg_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
return v_res_2704_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_2712_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2));
v___x_2713_ = l_Lean_Name_append(v___x_2712_, v___x_2711_);
return v___x_2713_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__4));
v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
return v___x_2716_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__6));
v___x_2719_ = l_Lean_stringToMessageData(v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(lean_object* v_t_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v___x_2729_; uint8_t v_hasUncomparable_2730_; 
v___x_2729_ = lean_st_ref_get(v_a_2721_);
v_hasUncomparable_2730_ = lean_ctor_get_uint8(v___x_2729_, sizeof(void*)*1);
lean_dec(v___x_2729_);
if (v_hasUncomparable_2730_ == 0)
{
switch(lean_obj_tag(v_t_2720_))
{
case 0:
{
lean_object* v_val_2731_; uint8_t v___x_2732_; lean_object* v___y_2734_; lean_object* v___x_2748_; 
v_val_2731_ = lean_ctor_get(v_t_2720_, 2);
lean_inc_ref(v_val_2731_);
lean_dec_ref_known(v_t_2720_, 3);
v___x_2732_ = 1;
lean_inc(v_a_2727_);
lean_inc_ref(v_a_2726_);
lean_inc(v_a_2725_);
lean_inc_ref(v_a_2724_);
v___x_2748_ = lean_infer_type(v_val_2731_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2885_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__0___redArg(v_a_2749_, v_a_2725_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2885_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2885_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2755_ = l_Lean_Expr_cleanupAnnotations(v_a_2751_);
lean_dec(v_a_2751_);
v___x_2756_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v_max_x3f_2758_; 
v___x_2757_ = lean_st_ref_get(v_a_2721_);
v_max_x3f_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_max_x3f_2758_);
lean_dec(v___x_2757_);
if (lean_obj_tag(v_max_x3f_2758_) == 0)
{
lean_object* v___x_2759_; uint8_t v_hasUncomparable_2760_; uint8_t v_hasUnknown_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2774_; 
v___x_2759_ = lean_st_ref_take(v_a_2721_);
v_hasUncomparable_2760_ = lean_ctor_get_uint8(v___x_2759_, sizeof(void*)*1);
v_hasUnknown_2761_ = lean_ctor_get_uint8(v___x_2759_, sizeof(void*)*1 + 1);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; 
v_unused_2775_ = lean_ctor_get(v___x_2759_, 0);
lean_dec(v_unused_2775_);
v___x_2763_ = v___x_2759_;
v_isShared_2764_ = v_isSharedCheck_2774_;
goto v_resetjp_2762_;
}
else
{
lean_dec(v___x_2759_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2774_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2755_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2766_);
v___x_2768_ = v___x_2763_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2766_);
lean_ctor_set_uint8(v_reuseFailAlloc_2773_, sizeof(void*)*1, v_hasUncomparable_2760_);
lean_ctor_set_uint8(v_reuseFailAlloc_2773_, sizeof(void*)*1 + 1, v_hasUnknown_2761_);
v___x_2768_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2769_ = lean_st_ref_put(v_a_2721_, v___x_2768_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2765_);
v___x_2771_ = v___x_2753_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2765_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_val_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2869_; 
lean_del_object(v___x_2753_);
v_val_2776_ = lean_ctor_get(v_max_x3f_2758_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_max_x3f_2758_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2778_ = v_max_x3f_2758_;
v_isShared_2779_ = v_isSharedCheck_2869_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_val_2776_);
lean_dec(v_max_x3f_2758_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2869_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___f_2781_; lean_object* v___x_2782_; 
v___x_2780_ = lean_box(v___x_2732_);
lean_inc_ref(v___x_2755_);
lean_inc(v_val_2776_);
v___f_2781_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2781_, 0, v___x_2780_);
lean_closure_set(v___f_2781_, 1, v_val_2776_);
lean_closure_set(v___f_2781_, 2, v___x_2755_);
v___x_2782_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__1___redArg(v___f_2781_, v___x_2756_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2860_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2860_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2860_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
uint8_t v___x_2787_; 
v___x_2787_ = lean_unbox(v_a_2783_);
lean_dec(v_a_2783_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; 
lean_del_object(v___x_2785_);
lean_inc(v_val_2776_);
lean_inc_ref(v___x_2755_);
v___x_2788_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v___x_2755_, v_val_2776_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2847_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2847_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2847_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
uint8_t v___x_2793_; 
v___x_2793_ = lean_unbox(v_a_2789_);
lean_dec(v_a_2789_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; 
lean_del_object(v___x_2791_);
lean_inc_ref(v___x_2755_);
lean_inc(v_val_2776_);
v___x_2794_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasCoe(v_val_2776_, v___x_2755_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2834_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2834_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2834_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_unbox(v_a_2795_);
lean_dec(v_a_2795_);
if (v___x_2799_ == 0)
{
lean_object* v_toCold_2800_; lean_object* v_options_2801_; uint8_t v_hasTrace_2802_; 
lean_del_object(v___x_2797_);
lean_del_object(v___x_2778_);
v_toCold_2800_ = lean_ctor_get(v_a_2726_, 0);
v_options_2801_ = lean_ctor_get(v_toCold_2800_, 2);
v_hasTrace_2802_ = lean_ctor_get_uint8(v_options_2801_, sizeof(void*)*1);
if (v_hasTrace_2802_ == 0)
{
lean_dec(v_val_2776_);
lean_dec_ref(v___x_2755_);
v___y_2734_ = v_a_2721_;
goto v___jp_2733_;
}
else
{
lean_object* v_inheritedTraceOptions_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v_inheritedTraceOptions_2803_ = lean_ctor_get(v_toCold_2800_, 11);
v___x_2804_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_2805_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_2806_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2803_, v_options_2801_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_dec(v_val_2776_);
lean_dec_ref(v___x_2755_);
v___y_2734_ = v_a_2721_;
goto v___jp_2733_;
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2807_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__5);
v___x_2808_ = l_Lean_MessageData_ofExpr(v_val_2776_);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2807_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__7);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = l_Lean_MessageData_ofExpr(v___x_2755_);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v___x_2804_, v___x_2813_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_dec_ref_known(v___x_2814_, 1);
v___y_2734_ = v_a_2721_;
goto v___jp_2733_;
}
else
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v___x_2815_; uint8_t v_hasUncomparable_2816_; uint8_t v_hasUnknown_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_val_2776_);
v___x_2815_ = lean_st_ref_take(v_a_2721_);
v_hasUncomparable_2816_ = lean_ctor_get_uint8(v___x_2815_, sizeof(void*)*1);
v_hasUnknown_2817_ = lean_ctor_get_uint8(v___x_2815_, sizeof(void*)*1 + 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v___x_2815_, 0);
lean_dec(v_unused_2833_);
v___x_2819_ = v___x_2815_;
v_isShared_2820_ = v_isSharedCheck_2832_;
goto v_resetjp_2818_;
}
else
{
lean_dec(v___x_2815_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2832_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2821_ = lean_box(0);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2755_);
v___x_2823_ = v___x_2778_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2755_);
v___x_2823_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2823_);
v___x_2825_ = v___x_2819_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2823_);
lean_ctor_set_uint8(v_reuseFailAlloc_2830_, sizeof(void*)*1, v_hasUncomparable_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2830_, sizeof(void*)*1 + 1, v_hasUnknown_2817_);
v___x_2825_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2826_ = lean_st_ref_put(v_a_2721_, v___x_2825_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v___x_2821_);
v___x_2828_ = v___x_2797_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2821_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_del_object(v___x_2778_);
lean_dec(v_val_2776_);
lean_dec_ref(v___x_2755_);
v_a_2835_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2794_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2794_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
lean_del_object(v___x_2778_);
lean_dec(v_val_2776_);
lean_dec_ref(v___x_2755_);
v___x_2843_ = lean_box(0);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2843_);
v___x_2845_ = v___x_2791_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_del_object(v___x_2778_);
lean_dec(v_val_2776_);
lean_dec_ref(v___x_2755_);
v_a_2848_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2788_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2788_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2858_; 
lean_del_object(v___x_2778_);
lean_dec(v_val_2776_);
lean_dec_ref(v___x_2755_);
v___x_2856_ = lean_box(0);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2856_);
v___x_2858_ = v___x_2785_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_del_object(v___x_2778_);
lean_dec(v_val_2776_);
lean_dec_ref(v___x_2755_);
v_a_2861_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2782_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2782_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
}
else
{
lean_object* v___x_2870_; lean_object* v_max_x3f_2871_; uint8_t v_hasUncomparable_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2884_; 
lean_dec_ref(v___x_2755_);
v___x_2870_ = lean_st_ref_take(v_a_2721_);
v_max_x3f_2871_ = lean_ctor_get(v___x_2870_, 0);
v_hasUncomparable_2872_ = lean_ctor_get_uint8(v___x_2870_, sizeof(void*)*1);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2874_ = v___x_2870_;
v_isShared_2875_ = v_isSharedCheck_2884_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_max_x3f_2871_);
lean_dec(v___x_2870_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2884_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = lean_box(0);
if (v_isShared_2875_ == 0)
{
v___x_2878_ = v___x_2874_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_max_x3f_2871_);
lean_ctor_set_uint8(v_reuseFailAlloc_2883_, sizeof(void*)*1, v_hasUncomparable_2872_);
v___x_2878_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_ctor_set_uint8(v___x_2878_, sizeof(void*)*1 + 1, v___x_2732_);
v___x_2879_ = lean_st_ref_put(v_a_2721_, v___x_2878_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2876_);
v___x_2881_ = v___x_2753_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_a_2886_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2748_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2748_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
v___jp_2733_:
{
lean_object* v___x_2735_; lean_object* v_max_x3f_2736_; uint8_t v_hasUnknown_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2747_; 
v___x_2735_ = lean_st_ref_take(v___y_2734_);
v_max_x3f_2736_ = lean_ctor_get(v___x_2735_, 0);
v_hasUnknown_2737_ = lean_ctor_get_uint8(v___x_2735_, sizeof(void*)*1 + 1);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2739_ = v___x_2735_;
v_isShared_2740_ = v_isSharedCheck_2747_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_max_x3f_2736_);
lean_dec(v___x_2735_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2747_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = lean_box(0);
if (v_isShared_2740_ == 0)
{
v___x_2743_ = v___x_2739_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_max_x3f_2736_);
lean_ctor_set_uint8(v_reuseFailAlloc_2746_, sizeof(void*)*1 + 1, v_hasUnknown_2737_);
v___x_2743_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*1, v___x_2732_);
v___x_2744_ = lean_st_ref_put(v___y_2734_, v___x_2743_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2741_);
return v___x_2745_;
}
}
}
}
case 1:
{
uint8_t v_kind_2894_; 
v_kind_2894_ = lean_ctor_get_uint8(v_t_2720_, sizeof(void*)*4);
switch(v_kind_2894_)
{
case 2:
{
lean_object* v_rhs_2895_; 
v_rhs_2895_ = lean_ctor_get(v_t_2720_, 3);
lean_inc_ref(v_rhs_2895_);
lean_dec_ref_known(v_t_2720_, 4);
v_t_2720_ = v_rhs_2895_;
goto _start;
}
case 3:
{
lean_object* v_lhs_2897_; 
v_lhs_2897_ = lean_ctor_get(v_t_2720_, 2);
lean_inc_ref(v_lhs_2897_);
lean_dec_ref_known(v_t_2720_, 4);
v_t_2720_ = v_lhs_2897_;
goto _start;
}
default: 
{
lean_object* v_lhs_2899_; lean_object* v_rhs_2900_; lean_object* v___x_2901_; 
v_lhs_2899_ = lean_ctor_get(v_t_2720_, 2);
lean_inc_ref(v_lhs_2899_);
v_rhs_2900_ = lean_ctor_get(v_t_2720_, 3);
lean_inc_ref(v_rhs_2900_);
lean_dec_ref_known(v_t_2720_, 4);
v___x_2901_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_lhs_2899_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_dec_ref_known(v___x_2901_, 1);
v_t_2720_ = v_rhs_2900_;
goto _start;
}
else
{
lean_dec_ref(v_rhs_2900_);
return v___x_2901_;
}
}
}
}
case 2:
{
lean_object* v_arg_2903_; 
v_arg_2903_ = lean_ctor_get(v_t_2720_, 2);
lean_inc_ref(v_arg_2903_);
lean_dec_ref_known(v_t_2720_, 3);
v_t_2720_ = v_arg_2903_;
goto _start;
}
default: 
{
lean_object* v_nested_2905_; 
v_nested_2905_ = lean_ctor_get(v_t_2720_, 3);
lean_inc_ref(v_nested_2905_);
lean_dec_ref_known(v_t_2720_, 4);
v_t_2720_ = v_nested_2905_;
goto _start;
}
}
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec_ref(v_t_2720_);
v___x_2907_ = lean_box(0);
v___x_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
return v___x_2908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___boxed(lean_object* v_t_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_t_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2(lean_object* v_cls_2919_, lean_object* v_msg_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg(v_cls_2919_, v_msg_2920_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___boxed(lean_object* v_cls_2930_, lean_object* v_msg_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2(v_cls_2930_, v_msg_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(lean_object* v_t_2941_, lean_object* v_expectedType_x3f_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_max_x3f_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; 
if (lean_obj_tag(v_expectedType_x3f_2942_) == 0)
{
v_max_x3f_2951_ = v_expectedType_x3f_2942_;
v___y_2952_ = v_a_2943_;
v___y_2953_ = v_a_2944_;
v___y_2954_ = v_a_2945_;
v___y_2955_ = v_a_2946_;
v___y_2956_ = v_a_2947_;
v___y_2957_ = v_a_2948_;
goto v___jp_2950_;
}
else
{
lean_object* v_val_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2992_; 
v_val_2980_ = lean_ctor_get(v_expectedType_x3f_2942_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_expectedType_x3f_2942_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2982_ = v_expectedType_x3f_2942_;
v_isShared_2983_ = v_isSharedCheck_2992_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_val_2980_);
lean_dec(v_expectedType_x3f_2942_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2992_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v_a_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2984_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(v_val_2980_, v_a_2946_);
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref(v___x_2984_);
v___x_2986_ = l_Lean_Expr_cleanupAnnotations(v_a_2985_);
lean_dec(v_a_2985_);
v___x_2987_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2989_; 
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_2986_);
v___x_2989_ = v___x_2982_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2986_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
v_max_x3f_2951_ = v___x_2989_;
v___y_2952_ = v_a_2943_;
v___y_2953_ = v_a_2944_;
v___y_2954_ = v_a_2945_;
v___y_2955_ = v_a_2946_;
v___y_2956_ = v_a_2947_;
v___y_2957_ = v_a_2948_;
goto v___jp_2950_;
}
}
else
{
lean_object* v___x_2991_; 
lean_dec_ref(v___x_2986_);
lean_del_object(v___x_2982_);
v___x_2991_ = lean_box(0);
v_max_x3f_2951_ = v___x_2991_;
v___y_2952_ = v_a_2943_;
v___y_2953_ = v_a_2944_;
v___y_2954_ = v_a_2945_;
v___y_2955_ = v_a_2946_;
v___y_2956_ = v_a_2947_;
v___y_2957_ = v_a_2948_;
goto v___jp_2950_;
}
}
}
v___jp_2950_:
{
uint8_t v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2958_ = 0;
v___x_2959_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2959_, 0, v_max_x3f_2951_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*1, v___x_2958_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*1 + 1, v___x_2958_);
v___x_2960_ = lean_st_mk_ref(v___x_2959_);
v___x_2961_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go(v_t_2941_, v___x_2960_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2970_; 
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2970_ == 0)
{
lean_object* v_unused_2971_; 
v_unused_2971_ = lean_ctor_get(v___x_2961_, 0);
lean_dec(v_unused_2971_);
v___x_2963_ = v___x_2961_;
v_isShared_2964_ = v_isSharedCheck_2970_;
goto v_resetjp_2962_;
}
else
{
lean_dec(v___x_2961_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2970_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2965_ = lean_st_ref_get(v___x_2960_);
v___x_2966_ = lean_st_ref_get(v___x_2960_);
lean_dec(v___x_2960_);
lean_dec(v___x_2966_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2965_);
v___x_2968_ = v___x_2963_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2965_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v___x_2960_);
v_a_2972_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2961_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2961_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze___boxed(lean_object* v_t_2993_, lean_object* v_expectedType_x3f_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v_t_2993_, v_expectedType_x3f_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(uint8_t v_lazy_3005_, lean_object* v_f_3006_, lean_object* v_lhs_3007_, lean_object* v_rhs_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v_rhs_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; 
if (v_lazy_3005_ == 0)
{
v_rhs_3017_ = v_rhs_3008_;
v___y_3018_ = v_a_3009_;
v___y_3019_ = v_a_3010_;
v___y_3020_ = v_a_3011_;
v___y_3021_ = v_a_3012_;
v___y_3022_ = v_a_3013_;
v___y_3023_ = v_a_3014_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_Meta_mkFunUnit___redArg(v_rhs_3008_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
v_rhs_3017_ = v_a_3035_;
v___y_3018_ = v_a_3009_;
v___y_3019_ = v_a_3010_;
v___y_3020_ = v_a_3011_;
v___y_3021_ = v_a_3012_;
v___y_3022_ = v_a_3013_;
v___y_3023_ = v_a_3014_;
goto v___jp_3016_;
}
else
{
lean_dec_ref(v_lhs_3007_);
lean_dec_ref(v_f_3006_);
return v___x_3034_;
}
}
v___jp_3016_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; 
v___x_3024_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
v___x_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_lhs_3007_);
v___x_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_rhs_3017_);
v___x_3027_ = lean_unsigned_to_nat(2u);
v___x_3028_ = lean_mk_empty_array_with_capacity(v___x_3027_);
v___x_3029_ = lean_array_push(v___x_3028_, v___x_3025_);
v___x_3030_ = lean_array_push(v___x_3029_, v___x_3026_);
v___x_3031_ = lean_box(0);
v___x_3032_ = 0;
v___x_3033_ = l_Lean_Elab_Term_elabAppArgs(v_f_3006_, v___x_3024_, v___x_3030_, v___x_3031_, v___x_3032_, v___x_3032_, v___x_3032_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
return v___x_3033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___boxed(lean_object* v_lazy_3036_, lean_object* v_f_3037_, lean_object* v_lhs_3038_, lean_object* v_rhs_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
uint8_t v_lazy_boxed_3047_; lean_object* v_res_3048_; 
v_lazy_boxed_3047_ = lean_unbox(v_lazy_3036_);
v_res_3048_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v_lazy_boxed_3047_, v_f_3037_, v_lhs_3038_, v_rhs_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(lean_object* v_f_3049_, lean_object* v_arg_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; 
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
v___x_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_arg_3050_);
v___x_3060_ = lean_unsigned_to_nat(1u);
v___x_3061_ = lean_mk_empty_array_with_capacity(v___x_3060_);
v___x_3062_ = lean_array_push(v___x_3061_, v___x_3059_);
v___x_3063_ = lean_box(0);
v___x_3064_ = 0;
v___x_3065_ = l_Lean_Elab_Term_elabAppArgs(v_f_3049_, v___x_3058_, v___x_3062_, v___x_3063_, v___x_3064_, v___x_3064_, v___x_3064_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp___boxed(lean_object* v_f_3066_, lean_object* v_arg_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(v_f_3066_, v_arg_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___y_3076_, lean_object* v_mkInfoTree_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v_a_3083_, lean_object* v_a_x3f_3084_){
_start:
{
lean_object* v___x_3086_; lean_object* v_infoState_3087_; lean_object* v_trees_3088_; lean_object* v___x_3089_; 
v___x_3086_ = lean_st_ref_get(v___y_3076_);
v_infoState_3087_ = lean_ctor_get(v___x_3086_, 8);
lean_inc_ref(v_infoState_3087_);
lean_dec(v___x_3086_);
v_trees_3088_ = lean_ctor_get(v_infoState_3087_, 2);
lean_inc_ref(v_trees_3088_);
lean_dec_ref(v_infoState_3087_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3082_);
lean_inc(v___y_3081_);
lean_inc_ref(v___y_3080_);
lean_inc(v___y_3079_);
lean_inc_ref(v___y_3078_);
v___x_3089_ = lean_apply_8(v_mkInfoTree_3077_, v_trees_3088_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3076_, lean_box(0));
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3129_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3129_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3129_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v_infoState_3095_; lean_object* v_env_3096_; lean_object* v_nextMacroScope_3097_; lean_object* v_ngen_3098_; lean_object* v_auxDeclNGen_3099_; lean_object* v_traceState_3100_; lean_object* v_cache_3101_; lean_object* v_recordedDeps_3102_; lean_object* v_messages_3103_; lean_object* v_snapshotTasks_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3128_; 
v___x_3094_ = lean_st_ref_take(v___y_3076_);
v_infoState_3095_ = lean_ctor_get(v___x_3094_, 8);
v_env_3096_ = lean_ctor_get(v___x_3094_, 0);
v_nextMacroScope_3097_ = lean_ctor_get(v___x_3094_, 1);
v_ngen_3098_ = lean_ctor_get(v___x_3094_, 2);
v_auxDeclNGen_3099_ = lean_ctor_get(v___x_3094_, 3);
v_traceState_3100_ = lean_ctor_get(v___x_3094_, 4);
v_cache_3101_ = lean_ctor_get(v___x_3094_, 5);
v_recordedDeps_3102_ = lean_ctor_get(v___x_3094_, 6);
v_messages_3103_ = lean_ctor_get(v___x_3094_, 7);
v_snapshotTasks_3104_ = lean_ctor_get(v___x_3094_, 9);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3106_ = v___x_3094_;
v_isShared_3107_ = v_isSharedCheck_3128_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_snapshotTasks_3104_);
lean_inc(v_infoState_3095_);
lean_inc(v_messages_3103_);
lean_inc(v_recordedDeps_3102_);
lean_inc(v_cache_3101_);
lean_inc(v_traceState_3100_);
lean_inc(v_auxDeclNGen_3099_);
lean_inc(v_ngen_3098_);
lean_inc(v_nextMacroScope_3097_);
lean_inc(v_env_3096_);
lean_dec(v___x_3094_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3128_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
uint8_t v_enabled_3108_; lean_object* v_assignment_3109_; lean_object* v_lazyAssignment_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3126_; 
v_enabled_3108_ = lean_ctor_get_uint8(v_infoState_3095_, sizeof(void*)*3);
v_assignment_3109_ = lean_ctor_get(v_infoState_3095_, 0);
v_lazyAssignment_3110_ = lean_ctor_get(v_infoState_3095_, 1);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_infoState_3095_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v_infoState_3095_, 2);
lean_dec(v_unused_3127_);
v___x_3112_ = v_infoState_3095_;
v_isShared_3113_ = v_isSharedCheck_3126_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_lazyAssignment_3110_);
lean_inc(v_assignment_3109_);
lean_dec(v_infoState_3095_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3126_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3114_ = lean_box(0);
v___x_3115_ = l_Lean_PersistentArray_push___redArg(v_a_3083_, v_a_3090_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 2, v___x_3115_);
v___x_3117_ = v___x_3112_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_assignment_3109_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_lazyAssignment_3110_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v___x_3115_);
lean_ctor_set_uint8(v_reuseFailAlloc_3125_, sizeof(void*)*3, v_enabled_3108_);
v___x_3117_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3119_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 8, v___x_3117_);
v___x_3119_ = v___x_3106_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_env_3096_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_nextMacroScope_3097_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_ngen_3098_);
lean_ctor_set(v_reuseFailAlloc_3124_, 3, v_auxDeclNGen_3099_);
lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_traceState_3100_);
lean_ctor_set(v_reuseFailAlloc_3124_, 5, v_cache_3101_);
lean_ctor_set(v_reuseFailAlloc_3124_, 6, v_recordedDeps_3102_);
lean_ctor_set(v_reuseFailAlloc_3124_, 7, v_messages_3103_);
lean_ctor_set(v_reuseFailAlloc_3124_, 8, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3124_, 9, v_snapshotTasks_3104_);
v___x_3119_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3120_ = lean_st_ref_put(v___y_3076_, v___x_3119_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3114_);
v___x_3122_ = v___x_3092_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3114_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec_ref(v_a_3083_);
v_a_3130_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3089_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3089_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_3138_, lean_object* v_mkInfoTree_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v_a_3145_, lean_object* v_a_x3f_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_3138_, v_mkInfoTree_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v_a_3145_, v_a_x3f_3146_);
lean_dec(v_a_x3f_3146_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3138_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3149_, lean_object* v_mkInfoTree_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v___x_3158_; lean_object* v_infoState_3159_; uint8_t v_enabled_3160_; 
v___x_3158_ = lean_st_ref_get(v___y_3156_);
v_infoState_3159_ = lean_ctor_get(v___x_3158_, 8);
lean_inc_ref(v_infoState_3159_);
lean_dec(v___x_3158_);
v_enabled_3160_ = lean_ctor_get_uint8(v_infoState_3159_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3159_);
if (v_enabled_3160_ == 0)
{
lean_object* v___x_3161_; 
lean_dec_ref(v_mkInfoTree_3150_);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
lean_inc(v___y_3154_);
lean_inc_ref(v___y_3153_);
lean_inc(v___y_3152_);
lean_inc_ref(v___y_3151_);
v___x_3161_ = lean_apply_7(v_x_3149_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, lean_box(0));
return v___x_3161_;
}
else
{
lean_object* v___x_3162_; lean_object* v_a_3163_; lean_object* v_r_3164_; 
v___x_3162_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v___y_3156_);
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref(v___x_3162_);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
lean_inc(v___y_3154_);
lean_inc_ref(v___y_3153_);
lean_inc(v___y_3152_);
lean_inc_ref(v___y_3151_);
v_r_3164_ = lean_apply_7(v_x_3149_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, lean_box(0));
if (lean_obj_tag(v_r_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3189_; 
v_a_3165_ = lean_ctor_get(v_r_3164_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_r_3164_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3167_ = v_r_3164_;
v_isShared_3168_ = v_isSharedCheck_3189_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v_r_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3189_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
lean_inc(v_a_3165_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set_tag(v___x_3167_, 1);
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_3156_, v_mkInfoTree_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v_a_3163_, v___x_3170_);
lean_dec_ref(v___x_3170_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v___x_3171_, 0);
lean_dec(v_unused_3179_);
v___x_3173_ = v___x_3171_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_dec(v___x_3171_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v_a_3165_);
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3165_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_a_3165_);
v_a_3180_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3171_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3171_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_a_3190_ = lean_ctor_get(v_r_3164_, 0);
lean_inc(v_a_3190_);
lean_dec_ref_known(v_r_3164_, 1);
v___x_3191_ = lean_box(0);
v___x_3192_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___lam__0(v___y_3156_, v_mkInfoTree_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v_a_3163_, v___x_3191_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v___x_3192_, 0);
lean_dec(v_unused_3200_);
v___x_3194_ = v___x_3192_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_dec(v___x_3192_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
lean_ctor_set_tag(v___x_3194_, 1);
lean_ctor_set(v___x_3194_, 0, v_a_3190_);
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3190_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v_a_3190_);
v_a_3201_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3192_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3192_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3209_, lean_object* v_mkInfoTree_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_3209_, v_mkInfoTree_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0(lean_object* v_stx_3219_, lean_object* v_output_3220_, lean_object* v_trees_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v_lctx_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_lctx_3229_ = lean_ctor_get(v___y_3224_, 2);
lean_inc_ref(v_lctx_3229_);
v___x_3230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3230_, 0, v_lctx_3229_);
lean_ctor_set(v___x_3230_, 1, v_stx_3219_);
lean_ctor_set(v___x_3230_, 2, v_output_3220_);
v___x_3231_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
v___x_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v_trees_3221_);
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_stx_3234_, lean_object* v_output_3235_, lean_object* v_trees_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0(v_stx_3234_, v_output_3235_, v_trees_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(lean_object* v_stx_3245_, lean_object* v_output_3246_, lean_object* v_x_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v___f_3255_; lean_object* v___x_3256_; 
v___f_3255_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3255_, 0, v_stx_3245_);
lean_closure_set(v___f_3255_, 1, v_output_3246_);
v___x_3256_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_3247_, v___f_3255_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg___boxed(lean_object* v_stx_3257_, lean_object* v_output_3258_, lean_object* v_x_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_stx_3257_, v_output_3258_, v_x_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(lean_object* v_beforeStx_3268_, lean_object* v_afterStx_3269_, lean_object* v_x_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_inc(v_afterStx_3269_);
lean_inc(v_beforeStx_3268_);
v___x_3278_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___boxed), 11, 4);
lean_closure_set(v___x_3278_, 0, lean_box(0));
lean_closure_set(v___x_3278_, 1, v_beforeStx_3268_);
lean_closure_set(v___x_3278_, 2, v_afterStx_3269_);
lean_closure_set(v___x_3278_, 3, v_x_3270_);
v___x_3279_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_beforeStx_3268_, v_afterStx_3269_, v___x_3278_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_a_3288_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3279_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3279_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg___boxed(lean_object* v_beforeStx_3296_, lean_object* v_afterStx_3297_, lean_object* v_x_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(v_beforeStx_3296_, v_afterStx_3297_, v_x_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0(lean_object* v_00_u03b1_3307_, lean_object* v_beforeStx_3308_, lean_object* v_afterStx_3309_, lean_object* v_x_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___redArg(v_beforeStx_3308_, v_afterStx_3309_, v_x_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___boxed(lean_object* v_00_u03b1_3319_, lean_object* v_beforeStx_3320_, lean_object* v_afterStx_3321_, lean_object* v_x_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0(v_00_u03b1_3319_, v_beforeStx_3320_, v_afterStx_3321_, v_x_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0(lean_object* v_lhs_3331_, lean_object* v_rhs_3332_, uint8_t v_kind_3333_, lean_object* v_f_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_lhs_3331_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3344_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___x_3344_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_rhs_3332_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; uint8_t v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___x_3346_ = 1;
v___x_3347_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_3333_, v___x_3346_);
v___x_3348_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v___x_3347_, v_f_3334_, v_a_3343_, v_a_3345_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
return v___x_3348_;
}
else
{
lean_dec(v_a_3343_);
lean_dec_ref(v_f_3334_);
return v___x_3344_;
}
}
else
{
lean_dec_ref(v_f_3334_);
lean_dec_ref(v_rhs_3332_);
return v___x_3342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0___boxed(lean_object* v_lhs_3349_, lean_object* v_rhs_3350_, lean_object* v_kind_3351_, lean_object* v_f_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
uint8_t v_kind_7882__boxed_3360_; lean_object* v_res_3361_; 
v_kind_7882__boxed_3360_ = lean_unbox(v_kind_3351_);
v_res_3361_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0(v_lhs_3349_, v_rhs_3350_, v_kind_7882__boxed_3360_, v_f_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1___boxed(lean_object* v_arg_3362_, lean_object* v_f_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1(v_arg_3362_, v_f_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___boxed(lean_object* v_t_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_t_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(lean_object* v_t_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_){
_start:
{
switch(lean_obj_tag(v_t_3381_))
{
case 0:
{
lean_object* v_infoTrees_3389_; lean_object* v_val_3390_; lean_object* v___x_3391_; lean_object* v_infoState_3392_; lean_object* v_env_3393_; lean_object* v_nextMacroScope_3394_; lean_object* v_ngen_3395_; lean_object* v_auxDeclNGen_3396_; lean_object* v_traceState_3397_; lean_object* v_cache_3398_; lean_object* v_recordedDeps_3399_; lean_object* v_messages_3400_; lean_object* v_snapshotTasks_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3422_; 
v_infoTrees_3389_ = lean_ctor_get(v_t_3381_, 1);
lean_inc_ref(v_infoTrees_3389_);
v_val_3390_ = lean_ctor_get(v_t_3381_, 2);
lean_inc_ref(v_val_3390_);
lean_dec_ref_known(v_t_3381_, 3);
v___x_3391_ = lean_st_ref_take(v_a_3387_);
v_infoState_3392_ = lean_ctor_get(v___x_3391_, 8);
v_env_3393_ = lean_ctor_get(v___x_3391_, 0);
v_nextMacroScope_3394_ = lean_ctor_get(v___x_3391_, 1);
v_ngen_3395_ = lean_ctor_get(v___x_3391_, 2);
v_auxDeclNGen_3396_ = lean_ctor_get(v___x_3391_, 3);
v_traceState_3397_ = lean_ctor_get(v___x_3391_, 4);
v_cache_3398_ = lean_ctor_get(v___x_3391_, 5);
v_recordedDeps_3399_ = lean_ctor_get(v___x_3391_, 6);
v_messages_3400_ = lean_ctor_get(v___x_3391_, 7);
v_snapshotTasks_3401_ = lean_ctor_get(v___x_3391_, 9);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3403_ = v___x_3391_;
v_isShared_3404_ = v_isSharedCheck_3422_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_snapshotTasks_3401_);
lean_inc(v_infoState_3392_);
lean_inc(v_messages_3400_);
lean_inc(v_recordedDeps_3399_);
lean_inc(v_cache_3398_);
lean_inc(v_traceState_3397_);
lean_inc(v_auxDeclNGen_3396_);
lean_inc(v_ngen_3395_);
lean_inc(v_nextMacroScope_3394_);
lean_inc(v_env_3393_);
lean_dec(v___x_3391_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3422_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
uint8_t v_enabled_3405_; lean_object* v_assignment_3406_; lean_object* v_lazyAssignment_3407_; lean_object* v_trees_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3421_; 
v_enabled_3405_ = lean_ctor_get_uint8(v_infoState_3392_, sizeof(void*)*3);
v_assignment_3406_ = lean_ctor_get(v_infoState_3392_, 0);
v_lazyAssignment_3407_ = lean_ctor_get(v_infoState_3392_, 1);
v_trees_3408_ = lean_ctor_get(v_infoState_3392_, 2);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_infoState_3392_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3410_ = v_infoState_3392_;
v_isShared_3411_ = v_isSharedCheck_3421_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_trees_3408_);
lean_inc(v_lazyAssignment_3407_);
lean_inc(v_assignment_3406_);
lean_dec(v_infoState_3392_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3421_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3412_ = l_Lean_PersistentArray_append___redArg(v_trees_3408_, v_infoTrees_3389_);
lean_dec_ref(v_infoTrees_3389_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 2, v___x_3412_);
v___x_3414_ = v___x_3410_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_assignment_3406_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_lazyAssignment_3407_);
lean_ctor_set(v_reuseFailAlloc_3420_, 2, v___x_3412_);
lean_ctor_set_uint8(v_reuseFailAlloc_3420_, sizeof(void*)*3, v_enabled_3405_);
v___x_3414_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3416_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 8, v___x_3414_);
v___x_3416_ = v___x_3403_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_env_3393_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_nextMacroScope_3394_);
lean_ctor_set(v_reuseFailAlloc_3419_, 2, v_ngen_3395_);
lean_ctor_set(v_reuseFailAlloc_3419_, 3, v_auxDeclNGen_3396_);
lean_ctor_set(v_reuseFailAlloc_3419_, 4, v_traceState_3397_);
lean_ctor_set(v_reuseFailAlloc_3419_, 5, v_cache_3398_);
lean_ctor_set(v_reuseFailAlloc_3419_, 6, v_recordedDeps_3399_);
lean_ctor_set(v_reuseFailAlloc_3419_, 7, v_messages_3400_);
lean_ctor_set(v_reuseFailAlloc_3419_, 8, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3419_, 9, v_snapshotTasks_3401_);
v___x_3416_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = lean_st_ref_put(v_a_3387_, v___x_3416_);
v___x_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_val_3390_);
return v___x_3418_;
}
}
}
}
}
case 1:
{
lean_object* v_ref_3423_; uint8_t v_kind_3424_; lean_object* v_f_3425_; lean_object* v_lhs_3426_; lean_object* v_rhs_3427_; lean_object* v_toCold_3428_; lean_object* v_currRecDepth_3429_; lean_object* v_ref_3430_; uint16_t v_optionFlags_3431_; uint8_t v_suppressElabErrors_3432_; uint8_t v_checkDeprecated_3433_; uint8_t v_isRecordingDeps_3434_; lean_object* v___x_3435_; lean_object* v___f_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; lean_object* v_ref_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v_ref_3423_ = lean_ctor_get(v_t_3381_, 0);
lean_inc(v_ref_3423_);
v_kind_3424_ = lean_ctor_get_uint8(v_t_3381_, sizeof(void*)*4);
v_f_3425_ = lean_ctor_get(v_t_3381_, 1);
lean_inc_ref(v_f_3425_);
v_lhs_3426_ = lean_ctor_get(v_t_3381_, 2);
lean_inc_ref(v_lhs_3426_);
v_rhs_3427_ = lean_ctor_get(v_t_3381_, 3);
lean_inc_ref(v_rhs_3427_);
lean_dec_ref_known(v_t_3381_, 4);
v_toCold_3428_ = lean_ctor_get(v_a_3386_, 0);
v_currRecDepth_3429_ = lean_ctor_get(v_a_3386_, 1);
v_ref_3430_ = lean_ctor_get(v_a_3386_, 2);
v_optionFlags_3431_ = lean_ctor_get_uint16(v_a_3386_, sizeof(void*)*3);
v_suppressElabErrors_3432_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*3 + 2);
v_checkDeprecated_3433_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3434_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*3 + 4);
v___x_3435_ = lean_box(v_kind_3424_);
v___f_3436_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3436_, 0, v_lhs_3426_);
lean_closure_set(v___f_3436_, 1, v_rhs_3427_);
lean_closure_set(v___f_3436_, 2, v___x_3435_);
lean_closure_set(v___f_3436_, 3, v_f_3425_);
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_box(0);
v___x_3439_ = 0;
v_ref_3440_ = l_Lean_replaceRef(v_ref_3423_, v_ref_3430_);
lean_inc(v_currRecDepth_3429_);
lean_inc_ref(v_toCold_3428_);
v___x_3441_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3441_, 0, v_toCold_3428_);
lean_ctor_set(v___x_3441_, 1, v_currRecDepth_3429_);
lean_ctor_set(v___x_3441_, 2, v_ref_3440_);
lean_ctor_set_uint16(v___x_3441_, sizeof(void*)*3, v_optionFlags_3431_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*3 + 2, v_suppressElabErrors_3432_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*3 + 3, v_checkDeprecated_3433_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*3 + 4, v_isRecordingDeps_3434_);
v___x_3442_ = l_Lean_Elab_Term_withTermInfoContext_x27(v___x_3437_, v_ref_3423_, v___f_3436_, v___x_3438_, v___x_3438_, v___x_3439_, v___x_3439_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v___x_3441_, v_a_3387_);
lean_dec_ref_known(v___x_3441_, 3);
return v___x_3442_;
}
case 2:
{
lean_object* v_ref_3443_; lean_object* v_f_3444_; lean_object* v_arg_3445_; lean_object* v_toCold_3446_; lean_object* v_currRecDepth_3447_; lean_object* v_ref_3448_; uint16_t v_optionFlags_3449_; uint8_t v_suppressElabErrors_3450_; uint8_t v_checkDeprecated_3451_; uint8_t v_isRecordingDeps_3452_; lean_object* v___f_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; lean_object* v_ref_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_ref_3443_ = lean_ctor_get(v_t_3381_, 0);
lean_inc(v_ref_3443_);
v_f_3444_ = lean_ctor_get(v_t_3381_, 1);
lean_inc_ref(v_f_3444_);
v_arg_3445_ = lean_ctor_get(v_t_3381_, 2);
lean_inc_ref(v_arg_3445_);
lean_dec_ref_known(v_t_3381_, 3);
v_toCold_3446_ = lean_ctor_get(v_a_3386_, 0);
v_currRecDepth_3447_ = lean_ctor_get(v_a_3386_, 1);
v_ref_3448_ = lean_ctor_get(v_a_3386_, 2);
v_optionFlags_3449_ = lean_ctor_get_uint16(v_a_3386_, sizeof(void*)*3);
v_suppressElabErrors_3450_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*3 + 2);
v_checkDeprecated_3451_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3452_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*3 + 4);
v___f_3453_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3453_, 0, v_arg_3445_);
lean_closure_set(v___f_3453_, 1, v_f_3444_);
v___x_3454_ = lean_box(0);
v___x_3455_ = lean_box(0);
v___x_3456_ = 0;
v_ref_3457_ = l_Lean_replaceRef(v_ref_3443_, v_ref_3448_);
lean_inc(v_currRecDepth_3447_);
lean_inc_ref(v_toCold_3446_);
v___x_3458_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3458_, 0, v_toCold_3446_);
lean_ctor_set(v___x_3458_, 1, v_currRecDepth_3447_);
lean_ctor_set(v___x_3458_, 2, v_ref_3457_);
lean_ctor_set_uint16(v___x_3458_, sizeof(void*)*3, v_optionFlags_3449_);
lean_ctor_set_uint8(v___x_3458_, sizeof(void*)*3 + 2, v_suppressElabErrors_3450_);
lean_ctor_set_uint8(v___x_3458_, sizeof(void*)*3 + 3, v_checkDeprecated_3451_);
lean_ctor_set_uint8(v___x_3458_, sizeof(void*)*3 + 4, v_isRecordingDeps_3452_);
v___x_3459_ = l_Lean_Elab_Term_withTermInfoContext_x27(v___x_3454_, v_ref_3443_, v___f_3453_, v___x_3455_, v___x_3455_, v___x_3456_, v___x_3456_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v___x_3458_, v_a_3387_);
lean_dec_ref_known(v___x_3458_, 3);
return v___x_3459_;
}
default: 
{
lean_object* v_macroName_3460_; lean_object* v_stx_3461_; lean_object* v_stx_x27_3462_; lean_object* v_nested_3463_; lean_object* v_toCold_3464_; lean_object* v_currRecDepth_3465_; lean_object* v_ref_3466_; uint16_t v_optionFlags_3467_; uint8_t v_suppressElabErrors_3468_; uint8_t v_checkDeprecated_3469_; uint8_t v_isRecordingDeps_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; lean_object* v_ref_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_macroName_3460_ = lean_ctor_get(v_t_3381_, 0);
lean_inc(v_macroName_3460_);
v_stx_3461_ = lean_ctor_get(v_t_3381_, 1);
lean_inc_n(v_stx_3461_, 2);
v_stx_x27_3462_ = lean_ctor_get(v_t_3381_, 2);
lean_inc(v_stx_x27_3462_);
v_nested_3463_ = lean_ctor_get(v_t_3381_, 3);
lean_inc_ref(v_nested_3463_);
lean_dec_ref_known(v_t_3381_, 4);
v_toCold_3464_ = lean_ctor_get(v_a_3386_, 0);
v_currRecDepth_3465_ = lean_ctor_get(v_a_3386_, 1);
v_ref_3466_ = lean_ctor_get(v_a_3386_, 2);
v_optionFlags_3467_ = lean_ctor_get_uint16(v_a_3386_, sizeof(void*)*3);
v_suppressElabErrors_3468_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*3 + 2);
v_checkDeprecated_3469_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3470_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*3 + 4);
v___x_3471_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___boxed), 8, 1);
lean_closure_set(v___x_3471_, 0, v_nested_3463_);
v___x_3472_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0___boxed), 11, 4);
lean_closure_set(v___x_3472_, 0, lean_box(0));
lean_closure_set(v___x_3472_, 1, v_stx_3461_);
lean_closure_set(v___x_3472_, 2, v_stx_x27_3462_);
lean_closure_set(v___x_3472_, 3, v___x_3471_);
v___x_3473_ = lean_box(0);
v___x_3474_ = 0;
v_ref_3475_ = l_Lean_replaceRef(v_stx_3461_, v_ref_3466_);
lean_inc(v_currRecDepth_3465_);
lean_inc_ref(v_toCold_3464_);
v___x_3476_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3476_, 0, v_toCold_3464_);
lean_ctor_set(v___x_3476_, 1, v_currRecDepth_3465_);
lean_ctor_set(v___x_3476_, 2, v_ref_3475_);
lean_ctor_set_uint16(v___x_3476_, sizeof(void*)*3, v_optionFlags_3467_);
lean_ctor_set_uint8(v___x_3476_, sizeof(void*)*3 + 2, v_suppressElabErrors_3468_);
lean_ctor_set_uint8(v___x_3476_, sizeof(void*)*3 + 3, v_checkDeprecated_3469_);
lean_ctor_set_uint8(v___x_3476_, sizeof(void*)*3 + 4, v_isRecordingDeps_3470_);
v___x_3477_ = l_Lean_Elab_Term_withTermInfoContext_x27(v_macroName_3460_, v_stx_3461_, v___x_3472_, v___x_3473_, v___x_3473_, v___x_3474_, v___x_3474_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v___x_3476_, v_a_3387_);
lean_dec_ref_known(v___x_3476_, 3);
return v___x_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore___lam__1(lean_object* v_arg_3478_, lean_object* v_f_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_arg_3478_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3489_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkUnOp(v_f_3479_, v_a_3488_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
return v___x_3489_;
}
else
{
lean_dec_ref(v_f_3479_);
return v___x_3487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0(lean_object* v_00_u03b1_3490_, lean_object* v_stx_3491_, lean_object* v_output_3492_, lean_object* v_x_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___redArg(v_stx_3491_, v_output_3492_, v_x_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3502_, lean_object* v_stx_3503_, lean_object* v_output_3504_, lean_object* v_x_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0(v_00_u03b1_3502_, v_stx_3503_, v_output_3504_, v_x_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3514_, lean_object* v_x_3515_, lean_object* v_mkInfoTree_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___redArg(v_x_3515_, v_mkInfoTree_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3525_, lean_object* v_x_3526_, lean_object* v_mkInfoTree_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore_spec__0_spec__0_spec__1(v_00_u03b1_3525_, v_x_3526_, v_mkInfoTree_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(lean_object* v___x_3536_, uint8_t v___x_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
if (lean_obj_tag(v_a_3538_) == 0)
{
lean_object* v___x_3540_; 
lean_dec_ref(v___x_3536_);
v___x_3540_ = l_List_reverse___redArg(v_a_3539_);
return v___x_3540_;
}
else
{
lean_object* v_head_3541_; lean_object* v_tail_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3553_; 
v_head_3541_ = lean_ctor_get(v_a_3538_, 0);
v_tail_3542_ = lean_ctor_get(v_a_3538_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_a_3538_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3544_ = v_a_3538_;
v_isShared_3545_ = v_isSharedCheck_3553_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_tail_3542_);
lean_inc(v_head_3541_);
lean_dec(v_a_3538_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3553_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v_fst_3546_; uint8_t v___x_3547_; 
v_fst_3546_ = lean_ctor_get(v_head_3541_, 0);
lean_inc(v_fst_3546_);
lean_inc_ref(v___x_3536_);
v___x_3547_ = l_Lean_Environment_contains(v___x_3536_, v_fst_3546_, v___x_3537_);
if (v___x_3547_ == 0)
{
lean_del_object(v___x_3544_);
lean_dec(v_head_3541_);
v_a_3538_ = v_tail_3542_;
goto _start;
}
else
{
lean_object* v___x_3550_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v_a_3539_);
v___x_3550_ = v___x_3544_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_head_3541_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_a_3539_);
v___x_3550_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
v_a_3538_ = v_tail_3542_;
v_a_3539_ = v___x_3550_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0___boxed(lean_object* v___x_3554_, lean_object* v___x_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
uint8_t v___x_5597__boxed_3558_; lean_object* v_res_3559_; 
v___x_5597__boxed_3558_ = lean_unbox(v___x_3555_);
v_res_3559_ = l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(v___x_3554_, v___x_5597__boxed_3558_, v_a_3556_, v_a_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(lean_object* v_className_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v_env_3565_; lean_object* v___y_3567_; lean_object* v___x_3573_; lean_object* v_toEnvExtension_3574_; lean_object* v_asyncMode_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v_defaultInstances_3578_; lean_object* v___x_3579_; 
v___x_3563_ = l_Lean_Meta_instInhabitedDefaultInstances_default;
v___x_3564_ = lean_st_ref_get(v___y_3561_);
v_env_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc_ref_n(v_env_3565_, 2);
lean_dec(v___x_3564_);
v___x_3573_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_3574_ = lean_ctor_get(v___x_3573_, 0);
v_asyncMode_3575_ = lean_ctor_get(v_toEnvExtension_3574_, 2);
v___x_3576_ = lean_box(0);
v___x_3577_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3563_, v___x_3573_, v_env_3565_, v_asyncMode_3575_, v___x_3576_);
v_defaultInstances_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_defaultInstances_3578_);
lean_dec(v___x_3577_);
v___x_3579_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_3578_, v_className_3560_);
lean_dec(v_defaultInstances_3578_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_box(0);
v___y_3567_ = v___x_3580_;
goto v___jp_3566_;
}
else
{
lean_object* v_val_3581_; 
v_val_3581_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_val_3581_);
lean_dec_ref_known(v___x_3579_, 1);
v___y_3567_ = v_val_3581_;
goto v___jp_3566_;
}
v___jp_3566_:
{
uint8_t v_isExporting_3568_; 
v_isExporting_3568_ = lean_ctor_get_uint8(v_env_3565_, sizeof(void*)*13);
if (v_isExporting_3568_ == 0)
{
lean_object* v___x_3569_; 
lean_dec_ref(v_env_3565_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___y_3567_);
return v___x_3569_;
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = lean_box(0);
v___x_3571_ = l_List_filterTR_loop___at___00Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0_spec__0(v_env_3565_, v_isExporting_3568_, v___y_3567_, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
return v___x_3572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg___boxed(lean_object* v_className_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec(v_className_3582_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3586_, lean_object* v_declHint_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v_env_3592_; uint8_t v___x_3593_; 
v___x_3590_ = lean_box(0);
v___x_3591_ = lean_st_ref_get(v___y_3588_);
v_env_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc_ref(v_env_3592_);
lean_dec(v___x_3591_);
v___x_3593_ = l_Lean_Name_isAnonymous(v_declHint_3587_);
if (v___x_3593_ == 0)
{
uint8_t v_isExporting_3594_; 
v_isExporting_3594_ = lean_ctor_get_uint8(v_env_3592_, sizeof(void*)*13);
if (v_isExporting_3594_ == 0)
{
lean_object* v___x_3595_; 
lean_dec_ref(v_env_3592_);
lean_dec(v_declHint_3587_);
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_msg_3586_);
return v___x_3595_;
}
else
{
lean_object* v___x_3596_; uint8_t v___x_3597_; 
lean_inc_ref(v_env_3592_);
v___x_3596_ = l_Lean_Environment_setExporting(v_env_3592_, v___x_3593_);
lean_inc(v_declHint_3587_);
lean_inc_ref(v___x_3596_);
v___x_3597_ = l_Lean_Environment_contains(v___x_3596_, v_declHint_3587_, v_isExporting_3594_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; 
lean_dec_ref(v___x_3596_);
lean_dec_ref(v_env_3592_);
lean_dec(v_declHint_3587_);
v___x_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3598_, 0, v_msg_3586_);
return v___x_3598_;
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v_c_3606_; lean_object* v___x_3607_; 
v___x_3599_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3600_ = lean_unsigned_to_nat(32u);
v___x_3601_ = lean_mk_empty_array_with_capacity(v___x_3600_);
lean_dec_ref(v___x_3601_);
v___x_3602_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__5);
v___x_3603_ = l_Lean_Options_empty;
lean_inc_ref(v___x_3596_);
v___x_3604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3596_);
lean_ctor_set(v___x_3604_, 1, v___x_3599_);
lean_ctor_set(v___x_3604_, 2, v___x_3602_);
lean_ctor_set(v___x_3604_, 3, v___x_3603_);
lean_inc(v_declHint_3587_);
v___x_3605_ = l_Lean_MessageData_ofConstName(v_declHint_3587_, v___x_3593_);
v_c_3606_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3606_, 0, v___x_3604_);
lean_ctor_set(v_c_3606_, 1, v___x_3605_);
v___x_3607_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3596_, v_declHint_3587_);
lean_dec_ref(v___x_3596_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
lean_dec_ref(v_env_3592_);
lean_dec(v_declHint_3587_);
v___x_3608_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
lean_ctor_set(v___x_3609_, 1, v_c_3606_);
v___x_3610_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__9);
v___x_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = l_Lean_MessageData_note(v___x_3611_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v_msg_3586_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
return v___x_3614_;
}
else
{
lean_object* v_val_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3668_; 
v_val_3615_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3617_ = v___x_3607_;
v_isShared_3618_ = v_isSharedCheck_3668_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_val_3615_);
lean_dec(v___x_3607_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3668_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; lean_object* v_modules_3620_; lean_object* v_moduleNames_3621_; lean_object* v_mod_3622_; uint8_t v___x_3637_; 
v___x_3619_ = l_Lean_Environment_header(v_env_3592_);
lean_dec_ref(v_env_3592_);
v_modules_3620_ = lean_ctor_get(v___x_3619_, 3);
lean_inc_ref(v_modules_3620_);
v_moduleNames_3621_ = lean_ctor_get(v___x_3619_, 4);
lean_inc_ref(v_moduleNames_3621_);
lean_dec_ref(v___x_3619_);
v_mod_3622_ = lean_array_get(v___x_3590_, v_moduleNames_3621_, v_val_3615_);
lean_dec_ref(v_moduleNames_3621_);
v___x_3637_ = l_Lean_isPrivateName(v_declHint_3587_);
lean_dec(v_declHint_3587_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = lean_array_get_size(v_modules_3620_);
v___x_3639_ = lean_nat_dec_lt(v_val_3615_, v___x_3638_);
if (v___x_3639_ == 0)
{
lean_dec_ref(v_modules_3620_);
lean_dec(v_val_3615_);
goto v___jp_3623_;
}
else
{
lean_object* v___x_3640_; lean_object* v_toImport_3641_; uint8_t v_isExported_3642_; 
v___x_3640_ = lean_array_fget(v_modules_3620_, v_val_3615_);
lean_dec(v_val_3615_);
lean_dec_ref(v_modules_3620_);
v_toImport_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc_ref(v_toImport_3641_);
lean_dec(v___x_3640_);
v_isExported_3642_ = lean_ctor_get_uint8(v_toImport_3641_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_3641_);
if (v_isExported_3642_ == 0)
{
goto v___jp_3623_;
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_del_object(v___x_3617_);
v___x_3643_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__17);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
lean_ctor_set(v___x_3644_, 1, v_c_3606_);
v___x_3645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__19);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3644_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = l_Lean_MessageData_ofName(v_mod_3622_);
lean_inc_ref(v___x_3647_);
v___x_3648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__21);
v___x_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3648_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
lean_ctor_set(v___x_3651_, 1, v___x_3647_);
v___x_3652_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__23);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = l_Lean_MessageData_note(v___x_3653_);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v_msg_3586_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
return v___x_3656_;
}
}
}
else
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_dec_ref(v_modules_3620_);
lean_del_object(v___x_3617_);
lean_dec(v_val_3615_);
v___x_3657_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__7);
v___x_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
lean_ctor_set(v___x_3658_, 1, v_c_3606_);
v___x_3659_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__25);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3658_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = l_Lean_MessageData_ofName(v_mod_3622_);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__27);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = l_Lean_MessageData_note(v___x_3664_);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v_msg_3586_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
return v___x_3667_;
}
v___jp_3623_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3624_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__11);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
lean_ctor_set(v___x_3625_, 1, v_c_3606_);
v___x_3626_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__13);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = l_Lean_MessageData_ofName(v_mod_3622_);
v___x_3629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3627_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2_spec__2_spec__4_spec__5___redArg___closed__15);
v___x_3631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3629_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
v___x_3632_ = l_Lean_MessageData_note(v___x_3631_);
v___x_3633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3633_, 0, v_msg_3586_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3633_);
v___x_3635_ = v___x_3617_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3669_; 
lean_dec_ref(v_env_3592_);
lean_dec(v_declHint_3587_);
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v_msg_3586_);
return v___x_3669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3670_, lean_object* v_declHint_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3670_, v_declHint_3671_, v___y_3672_);
lean_dec(v___y_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_msg_3675_, lean_object* v_declHint_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3692_; 
v___x_3682_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3675_, v_declHint_3676_, v___y_3680_);
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3692_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3692_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3687_ = l_Lean_unknownIdentifierMessageTag;
v___x_3688_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
lean_ctor_set(v___x_3688_, 1, v_a_3683_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3688_);
v___x_3690_ = v___x_3685_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3693_, lean_object* v_declHint_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_3693_, v_declHint_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v_ref_3707_; lean_object* v___x_3708_; lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3717_; 
v_ref_3707_ = lean_ctor_get(v___y_3704_, 2);
v___x_3708_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3711_ = v___x_3708_;
v_isShared_3712_ = v_isSharedCheck_3717_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3717_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
lean_inc(v_ref_3707_);
v___x_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3713_, 0, v_ref_3707_);
lean_ctor_set(v___x_3713_, 1, v_a_3709_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set_tag(v___x_3711_, 1);
lean_ctor_set(v___x_3711_, 0, v___x_3713_);
v___x_3715_ = v___x_3711_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_3725_, lean_object* v_msg_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v_toCold_3732_; lean_object* v_currRecDepth_3733_; lean_object* v_ref_3734_; uint16_t v_optionFlags_3735_; uint8_t v_suppressElabErrors_3736_; uint8_t v_checkDeprecated_3737_; uint8_t v_isRecordingDeps_3738_; lean_object* v_ref_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v_toCold_3732_ = lean_ctor_get(v___y_3729_, 0);
v_currRecDepth_3733_ = lean_ctor_get(v___y_3729_, 1);
v_ref_3734_ = lean_ctor_get(v___y_3729_, 2);
v_optionFlags_3735_ = lean_ctor_get_uint16(v___y_3729_, sizeof(void*)*3);
v_suppressElabErrors_3736_ = lean_ctor_get_uint8(v___y_3729_, sizeof(void*)*3 + 2);
v_checkDeprecated_3737_ = lean_ctor_get_uint8(v___y_3729_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3738_ = lean_ctor_get_uint8(v___y_3729_, sizeof(void*)*3 + 4);
v_ref_3739_ = l_Lean_replaceRef(v_ref_3725_, v_ref_3734_);
lean_inc(v_currRecDepth_3733_);
lean_inc_ref(v_toCold_3732_);
v___x_3740_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3740_, 0, v_toCold_3732_);
lean_ctor_set(v___x_3740_, 1, v_currRecDepth_3733_);
lean_ctor_set(v___x_3740_, 2, v_ref_3739_);
lean_ctor_set_uint16(v___x_3740_, sizeof(void*)*3, v_optionFlags_3735_);
lean_ctor_set_uint8(v___x_3740_, sizeof(void*)*3 + 2, v_suppressElabErrors_3736_);
lean_ctor_set_uint8(v___x_3740_, sizeof(void*)*3 + 3, v_checkDeprecated_3737_);
lean_ctor_set_uint8(v___x_3740_, sizeof(void*)*3 + 4, v_isRecordingDeps_3738_);
v___x_3741_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3726_, v___y_3727_, v___y_3728_, v___x_3740_, v___y_3730_);
lean_dec_ref_known(v___x_3740_, 3);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3742_, lean_object* v_msg_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3742_, v_msg_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v_ref_3742_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_3750_, lean_object* v_msg_3751_, lean_object* v_declHint_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3758_; lean_object* v_a_3759_; lean_object* v___x_3760_; 
v___x_3758_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6(v_msg_3751_, v_declHint_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref(v___x_3758_);
v___x_3760_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_3750_, v_a_3759_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3761_, lean_object* v_msg_3762_, lean_object* v_declHint_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3761_, v_msg_3762_, v_declHint_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v_ref_3761_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_3770_, lean_object* v_constName_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___x_3777_; uint8_t v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3777_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__1);
v___x_3778_ = 0;
lean_inc(v_constName_3771_);
v___x_3779_ = l_Lean_MessageData_ofConstName(v_constName_3771_, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3777_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg___closed__3);
v___x_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3770_, v___x_3782_, v_constName_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_3784_, lean_object* v_constName_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3784_, v_constName_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v_ref_3784_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(lean_object* v_constName_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_ref_3798_; lean_object* v___x_3799_; 
v_ref_3798_ = lean_ctor_get(v___y_3795_, 2);
v___x_3799_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_3798_, v_constName_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg___boxed(lean_object* v_constName_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(lean_object* v_constName_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; lean_object* v_env_3814_; uint8_t v___x_3815_; lean_object* v___x_3816_; 
v___x_3813_ = lean_st_ref_get(v___y_3811_);
v_env_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc_ref(v_env_3814_);
lean_dec(v___x_3813_);
v___x_3815_ = 0;
lean_inc(v_constName_3807_);
v___x_3816_ = l_Lean_Environment_find_x3f(v_env_3814_, v_constName_3807_, v___x_3815_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
return v___x_3817_;
}
else
{
lean_object* v_val_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_constName_3807_);
v_val_3818_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3816_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_val_3818_);
lean_dec(v___x_3816_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set_tag(v___x_3820_, 0);
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_val_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1___boxed(lean_object* v_constName_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(v_constName_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(lean_object* v_declName_3836_, uint8_t v_lhs_3837_, lean_object* v___x_3838_, lean_object* v_as_x27_3839_, lean_object* v_b_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
if (lean_obj_tag(v_as_x27_3839_) == 0)
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v_b_3840_);
return v___x_3846_;
}
else
{
lean_object* v_head_3847_; lean_object* v_tail_3848_; lean_object* v_fst_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; lean_object* v___x_3854_; 
lean_dec_ref(v_b_3840_);
v_head_3847_ = lean_ctor_get(v_as_x27_3839_, 0);
v_tail_3848_ = lean_ctor_get(v_as_x27_3839_, 1);
v_fst_3849_ = lean_ctor_get(v_head_3847_, 0);
v___x_3850_ = lean_box(0);
v___x_3851_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0));
v___x_3852_ = lean_unsigned_to_nat(1u);
v___x_3853_ = lean_nat_dec_le(v___x_3838_, v___x_3852_);
lean_inc(v_fst_3849_);
v___x_3854_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1(v_fst_3849_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3887_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3887_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3887_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = l_Lean_ConstantInfo_type(v_a_3855_);
lean_dec(v_a_3855_);
v___x_3860_ = l_Lean_Expr_getForallBody(v___x_3859_);
lean_dec_ref(v___x_3859_);
if (lean_obj_tag(v___x_3860_) == 5)
{
lean_object* v_fn_3861_; 
v_fn_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc_ref(v_fn_3861_);
lean_dec_ref_known(v___x_3860_, 2);
if (lean_obj_tag(v_fn_3861_) == 5)
{
lean_object* v_fn_3862_; 
v_fn_3862_ = lean_ctor_get(v_fn_3861_, 0);
lean_inc_ref(v_fn_3862_);
if (lean_obj_tag(v_fn_3862_) == 5)
{
lean_object* v_arg_3863_; lean_object* v_arg_3864_; uint8_t v___y_3866_; uint8_t v___y_3876_; 
v_arg_3863_ = lean_ctor_get(v_fn_3861_, 1);
lean_inc_ref(v_arg_3863_);
lean_dec_ref_known(v_fn_3861_, 2);
v_arg_3864_ = lean_ctor_get(v_fn_3862_, 1);
lean_inc_ref(v_arg_3864_);
lean_dec_ref_known(v_fn_3862_, 2);
if (v_lhs_3837_ == 0)
{
lean_dec_ref(v_arg_3863_);
v___y_3876_ = v___x_3853_;
goto v___jp_3875_;
}
else
{
uint8_t v___x_3879_; 
v___x_3879_ = l_Lean_Expr_isAppOf(v_arg_3863_, v_declName_3836_);
lean_dec_ref(v_arg_3863_);
if (v___x_3879_ == 0)
{
v___y_3876_ = v___x_3879_;
goto v___jp_3875_;
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
lean_dec_ref(v_arg_3864_);
lean_del_object(v___x_3857_);
v___x_3880_ = lean_box(v_lhs_3837_);
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v___x_3850_);
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
return v___x_3883_;
}
}
v___jp_3865_:
{
uint8_t v___x_3867_; 
v___x_3867_ = l_Lean_Expr_isAppOf(v_arg_3864_, v_declName_3836_);
lean_dec_ref(v_arg_3864_);
if (v___x_3867_ == 0)
{
lean_del_object(v___x_3857_);
v_as_x27_3839_ = v_tail_3848_;
v_b_3840_ = v___x_3851_;
goto _start;
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3869_ = lean_box(v___y_3866_);
v___x_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
v___x_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
lean_ctor_set(v___x_3871_, 1, v___x_3850_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3871_);
v___x_3873_ = v___x_3857_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
v___jp_3875_:
{
uint8_t v___x_3877_; 
v___x_3877_ = 1;
if (v_lhs_3837_ == 0)
{
v___y_3866_ = v___x_3877_;
goto v___jp_3865_;
}
else
{
if (v___y_3876_ == 0)
{
lean_dec_ref(v_arg_3864_);
lean_del_object(v___x_3857_);
v_as_x27_3839_ = v_tail_3848_;
v_b_3840_ = v___x_3851_;
goto _start;
}
else
{
v___y_3866_ = v___x_3877_;
goto v___jp_3865_;
}
}
}
}
else
{
lean_dec_ref(v_fn_3862_);
lean_dec_ref_known(v_fn_3861_, 2);
lean_del_object(v___x_3857_);
v_as_x27_3839_ = v_tail_3848_;
v_b_3840_ = v___x_3851_;
goto _start;
}
}
else
{
lean_dec_ref(v_fn_3861_);
lean_del_object(v___x_3857_);
v_as_x27_3839_ = v_tail_3848_;
v_b_3840_ = v___x_3851_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_3860_);
lean_del_object(v___x_3857_);
v_as_x27_3839_ = v_tail_3848_;
v_b_3840_ = v___x_3851_;
goto _start;
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
v_a_3888_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3854_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3854_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___boxed(lean_object* v_declName_3896_, lean_object* v_lhs_3897_, lean_object* v___x_3898_, lean_object* v_as_x27_3899_, lean_object* v_b_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
uint8_t v_lhs_boxed_3906_; lean_object* v_res_3907_; 
v_lhs_boxed_3906_ = lean_unbox(v_lhs_3897_);
v_res_3907_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3896_, v_lhs_boxed_3906_, v___x_3898_, v_as_x27_3899_, v_b_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v_as_x27_3899_);
lean_dec(v___x_3898_);
lean_dec(v_declName_3896_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(lean_object* v_f_3908_, lean_object* v_maxType_3909_, uint8_t v_lhs_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
if (lean_obj_tag(v_f_3908_) == 4)
{
lean_object* v_declName_3916_; lean_object* v___x_3917_; 
v_declName_3916_ = lean_ctor_get(v_f_3908_, 0);
v___x_3917_ = l_Lean_Expr_getAppFn(v_maxType_3909_);
if (lean_obj_tag(v___x_3917_) == 4)
{
lean_object* v_declName_3918_; lean_object* v_className_3919_; lean_object* v___x_3920_; lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3957_; 
v_declName_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_declName_3918_);
lean_dec_ref_known(v___x_3917_, 2);
v_className_3919_ = l_Lean_Name_getPrefix(v_declName_3916_);
v___x_3920_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3919_, v_a_3914_);
lean_dec(v_className_3919_);
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3923_ = v___x_3920_;
v_isShared_3924_ = v_isSharedCheck_3957_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3957_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; 
v___x_3925_ = l_List_lengthTR___redArg(v_a_3921_);
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = lean_nat_dec_le(v___x_3925_, v___x_3926_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_del_object(v___x_3923_);
v___x_3928_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg___closed__0));
v___x_3929_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3918_, v_lhs_3910_, v___x_3925_, v_a_3921_, v___x_3928_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_);
lean_dec(v_a_3921_);
lean_dec(v___x_3925_);
lean_dec(v_declName_3918_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3943_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3943_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3943_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v_fst_3934_; 
v_fst_3934_ = lean_ctor_get(v_a_3930_, 0);
lean_inc(v_fst_3934_);
lean_dec(v_a_3930_);
if (lean_obj_tag(v_fst_3934_) == 0)
{
lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3935_ = lean_box(v___x_3927_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v___x_3935_);
v___x_3937_ = v___x_3932_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
else
{
lean_object* v_val_3939_; lean_object* v___x_3941_; 
v_val_3939_ = lean_ctor_get(v_fst_3934_, 0);
lean_inc(v_val_3939_);
lean_dec_ref_known(v_fst_3934_, 1);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v_val_3939_);
v___x_3941_ = v___x_3932_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_val_3939_);
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
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
v_a_3944_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3929_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3929_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
else
{
uint8_t v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3955_; 
lean_dec(v___x_3925_);
lean_dec(v_a_3921_);
lean_dec(v_declName_3918_);
v___x_3952_ = 0;
v___x_3953_ = lean_box(v___x_3952_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3953_);
v___x_3955_ = v___x_3923_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
else
{
uint8_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_dec_ref(v___x_3917_);
v___x_3958_ = 0;
v___x_3959_ = lean_box(v___x_3958_);
v___x_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
return v___x_3960_;
}
}
else
{
uint8_t v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = 0;
v___x_3962_ = lean_box(v___x_3961_);
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances___boxed(lean_object* v_f_3964_, lean_object* v_maxType_3965_, lean_object* v_lhs_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
uint8_t v_lhs_boxed_3972_; lean_object* v_res_3973_; 
v_lhs_boxed_3972_ = lean_unbox(v_lhs_3966_);
v_res_3973_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(v_f_3964_, v_maxType_3965_, v_lhs_boxed_3972_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec_ref(v_maxType_3965_);
lean_dec_ref(v_f_3964_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0(lean_object* v_className_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___redArg(v_className_3974_, v___y_3978_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0___boxed(lean_object* v_className_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Meta_getDefaultInstances___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__0(v_className_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v_className_3981_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2(lean_object* v_declName_3988_, uint8_t v_lhs_3989_, lean_object* v___x_3990_, lean_object* v_as_3991_, lean_object* v_as_x27_3992_, lean_object* v_b_3993_, lean_object* v_a_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___redArg(v_declName_3988_, v_lhs_3989_, v___x_3990_, v_as_x27_3992_, v_b_3993_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2___boxed(lean_object* v_declName_4001_, lean_object* v_lhs_4002_, lean_object* v___x_4003_, lean_object* v_as_4004_, lean_object* v_as_x27_4005_, lean_object* v_b_4006_, lean_object* v_a_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
uint8_t v_lhs_boxed_4013_; lean_object* v_res_4014_; 
v_lhs_boxed_4013_ = lean_unbox(v_lhs_4002_);
v_res_4014_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__2(v_declName_4001_, v_lhs_boxed_4013_, v___x_4003_, v_as_4004_, v_as_x27_4005_, v_b_4006_, v_a_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v_as_x27_4005_);
lean_dec(v_as_4004_);
lean_dec(v___x_4003_);
lean_dec(v_declName_4001_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2(lean_object* v_00_u03b1_4015_, lean_object* v_constName_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___redArg(v_constName_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4023_, lean_object* v_constName_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2(v_00_u03b1_4023_, v_constName_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4031_, lean_object* v_ref_4032_, lean_object* v_constName_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___redArg(v_ref_4032_, v_constName_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4040_, lean_object* v_ref_4041_, lean_object* v_constName_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3(v_00_u03b1_4040_, v_ref_4041_, v_constName_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v_ref_4041_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_4049_, lean_object* v_ref_4050_, lean_object* v_msg_4051_, lean_object* v_declHint_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_4050_, v_msg_4051_, v_declHint_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4059_, lean_object* v_ref_4060_, lean_object* v_msg_4061_, lean_object* v_declHint_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_4059_, v_ref_4060_, v_msg_4061_, v_declHint_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v_ref_4060_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_4069_, lean_object* v_declHint_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_4069_, v_declHint_4070_, v___y_4074_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_4077_, lean_object* v_declHint_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_4077_, v_declHint_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_4085_, lean_object* v_ref_4086_, lean_object* v_msg_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_4086_, v_msg_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4094_, lean_object* v_ref_4095_, lean_object* v_msg_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_4094_, v_ref_4095_, v_msg_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v_ref_4095_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_4103_, lean_object* v_msg_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4111_, lean_object* v_msg_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances_spec__1_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_4111_, v_msg_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(lean_object* v_f_4119_, lean_object* v_maxType_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
lean_object* v_a_4127_; 
if (lean_obj_tag(v_f_4119_) == 4)
{
lean_object* v_declName_4134_; lean_object* v_className_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_declName_4134_ = lean_ctor_get(v_f_4119_, 0);
v_className_4135_ = l_Lean_Name_getPrefix(v_declName_4134_);
v___x_4136_ = lean_unsigned_to_nat(3u);
v___x_4137_ = lean_mk_empty_array_with_capacity(v___x_4136_);
lean_inc_ref_n(v_maxType_4120_, 2);
v___x_4138_ = lean_array_push(v___x_4137_, v_maxType_4120_);
v___x_4139_ = lean_array_push(v___x_4138_, v_maxType_4120_);
v___x_4140_ = lean_array_push(v___x_4139_, v_maxType_4120_);
v___x_4141_ = l_Lean_Meta_mkAppM(v_className_4135_, v___x_4140_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4143_ = lean_box(0);
v___x_4144_ = l_Lean_Meta_trySynthInstance(v_a_4142_, v___x_4143_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4159_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4147_ = v___x_4144_;
v_isShared_4148_ = v_isSharedCheck_4159_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4159_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
if (lean_obj_tag(v_a_4145_) == 1)
{
uint8_t v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4152_; 
lean_dec_ref_known(v_a_4145_, 1);
v___x_4149_ = 1;
v___x_4150_ = lean_box(v___x_4149_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4150_);
v___x_4152_ = v___x_4147_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
else
{
uint8_t v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4157_; 
lean_dec(v_a_4145_);
v___x_4154_ = 0;
v___x_4155_ = lean_box(v___x_4154_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4155_);
v___x_4157_ = v___x_4147_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
else
{
lean_object* v_a_4160_; 
v_a_4160_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4144_, 1);
v_a_4127_ = v_a_4160_;
goto v___jp_4126_;
}
}
else
{
lean_object* v_a_4161_; 
v_a_4161_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4141_, 1);
v_a_4127_ = v_a_4161_;
goto v___jp_4126_;
}
}
else
{
uint8_t v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
lean_dec_ref(v_maxType_4120_);
v___x_4162_ = 0;
v___x_4163_ = lean_box(v___x_4162_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
v___jp_4126_:
{
uint8_t v___x_4128_; 
v___x_4128_ = l_Lean_Exception_isInterrupt(v_a_4127_);
if (v___x_4128_ == 0)
{
uint8_t v___x_4129_; 
lean_inc_ref(v_a_4127_);
v___x_4129_ = l_Lean_Exception_isRuntime(v_a_4127_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
lean_dec_ref(v_a_4127_);
v___x_4130_ = lean_box(v___x_4129_);
v___x_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
return v___x_4131_;
}
else
{
lean_object* v___x_4132_; 
v___x_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4132_, 0, v_a_4127_);
return v___x_4132_;
}
}
else
{
lean_object* v___x_4133_; 
v___x_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4133_, 0, v_a_4127_);
return v___x_4133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance___boxed(lean_object* v_f_4165_, lean_object* v_maxType_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(v_f_4165_, v_maxType_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
lean_dec_ref(v_f_4165_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(lean_object* v_cls_4173_, lean_object* v_msg_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_ref_4180_; lean_object* v___x_4181_; lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4227_; 
v_ref_4180_ = lean_ctor_get(v___y_4177_, 2);
v___x_4181_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0_spec__0(v_msg_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4184_ = v___x_4181_;
v_isShared_4185_ = v_isSharedCheck_4227_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4181_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4227_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4186_; lean_object* v_traceState_4187_; lean_object* v_env_4188_; lean_object* v_nextMacroScope_4189_; lean_object* v_ngen_4190_; lean_object* v_auxDeclNGen_4191_; lean_object* v_cache_4192_; lean_object* v_recordedDeps_4193_; lean_object* v_messages_4194_; lean_object* v_infoState_4195_; lean_object* v_snapshotTasks_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4226_; 
v___x_4186_ = lean_st_ref_take(v___y_4178_);
v_traceState_4187_ = lean_ctor_get(v___x_4186_, 4);
v_env_4188_ = lean_ctor_get(v___x_4186_, 0);
v_nextMacroScope_4189_ = lean_ctor_get(v___x_4186_, 1);
v_ngen_4190_ = lean_ctor_get(v___x_4186_, 2);
v_auxDeclNGen_4191_ = lean_ctor_get(v___x_4186_, 3);
v_cache_4192_ = lean_ctor_get(v___x_4186_, 5);
v_recordedDeps_4193_ = lean_ctor_get(v___x_4186_, 6);
v_messages_4194_ = lean_ctor_get(v___x_4186_, 7);
v_infoState_4195_ = lean_ctor_get(v___x_4186_, 8);
v_snapshotTasks_4196_ = lean_ctor_get(v___x_4186_, 9);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4198_ = v___x_4186_;
v_isShared_4199_ = v_isSharedCheck_4226_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_snapshotTasks_4196_);
lean_inc(v_infoState_4195_);
lean_inc(v_messages_4194_);
lean_inc(v_recordedDeps_4193_);
lean_inc(v_cache_4192_);
lean_inc(v_traceState_4187_);
lean_inc(v_auxDeclNGen_4191_);
lean_inc(v_ngen_4190_);
lean_inc(v_nextMacroScope_4189_);
lean_inc(v_env_4188_);
lean_dec(v___x_4186_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4226_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
uint64_t v_tid_4200_; lean_object* v_traces_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4225_; 
v_tid_4200_ = lean_ctor_get_uint64(v_traceState_4187_, sizeof(void*)*1);
v_traces_4201_ = lean_ctor_get(v_traceState_4187_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_traceState_4187_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4203_ = v_traceState_4187_;
v_isShared_4204_ = v_isSharedCheck_4225_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_traces_4201_);
lean_dec(v_traceState_4187_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4225_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; double v___x_4207_; uint8_t v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4216_; 
v___x_4205_ = lean_box(0);
v___x_4206_ = lean_box(0);
v___x_4207_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__0);
v___x_4208_ = 0;
v___x_4209_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__1));
v___x_4210_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4210_, 0, v_cls_4173_);
lean_ctor_set(v___x_4210_, 1, v___x_4206_);
lean_ctor_set(v___x_4210_, 2, v___x_4209_);
lean_ctor_set_float(v___x_4210_, sizeof(void*)*3, v___x_4207_);
lean_ctor_set_float(v___x_4210_, sizeof(void*)*3 + 8, v___x_4207_);
lean_ctor_set_uint8(v___x_4210_, sizeof(void*)*3 + 16, v___x_4208_);
v___x_4211_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go_spec__2___redArg___closed__2));
v___x_4212_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4210_);
lean_ctor_set(v___x_4212_, 1, v_a_4182_);
lean_ctor_set(v___x_4212_, 2, v___x_4211_);
lean_inc(v_ref_4180_);
v___x_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4213_, 0, v_ref_4180_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = l_Lean_PersistentArray_push___redArg(v_traces_4201_, v___x_4213_);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4214_);
v___x_4216_ = v___x_4203_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4214_);
lean_ctor_set_uint64(v_reuseFailAlloc_4224_, sizeof(void*)*1, v_tid_4200_);
v___x_4216_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
lean_object* v___x_4218_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 4, v___x_4216_);
v___x_4218_ = v___x_4198_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_env_4188_);
lean_ctor_set(v_reuseFailAlloc_4223_, 1, v_nextMacroScope_4189_);
lean_ctor_set(v_reuseFailAlloc_4223_, 2, v_ngen_4190_);
lean_ctor_set(v_reuseFailAlloc_4223_, 3, v_auxDeclNGen_4191_);
lean_ctor_set(v_reuseFailAlloc_4223_, 4, v___x_4216_);
lean_ctor_set(v_reuseFailAlloc_4223_, 5, v_cache_4192_);
lean_ctor_set(v_reuseFailAlloc_4223_, 6, v_recordedDeps_4193_);
lean_ctor_set(v_reuseFailAlloc_4223_, 7, v_messages_4194_);
lean_ctor_set(v_reuseFailAlloc_4223_, 8, v_infoState_4195_);
lean_ctor_set(v_reuseFailAlloc_4223_, 9, v_snapshotTasks_4196_);
v___x_4218_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
lean_object* v___x_4219_; lean_object* v___x_4221_; 
v___x_4219_ = lean_st_ref_put(v___y_4178_, v___x_4218_);
if (v_isShared_4185_ == 0)
{
lean_ctor_set(v___x_4184_, 0, v___x_4205_);
v___x_4221_ = v___x_4184_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4205_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg___boxed(lean_object* v_cls_4228_, lean_object* v_msg_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v_cls_4228_, v_msg_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
return v_res_4235_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1(void){
_start:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__0));
v___x_4238_ = l_Lean_stringToMessageData(v___x_4237_);
return v___x_4238_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3(void){
_start:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__2));
v___x_4241_ = l_Lean_stringToMessageData(v___x_4240_);
return v___x_4241_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5(void){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__4));
v___x_4244_ = l_Lean_stringToMessageData(v___x_4243_);
return v___x_4244_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7(void){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4246_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__6));
v___x_4247_ = l_Lean_stringToMessageData(v___x_4246_);
return v___x_4247_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9(void){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__8));
v___x_4250_ = l_Lean_stringToMessageData(v___x_4249_);
return v___x_4250_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__0));
v___x_4253_ = l_Lean_stringToMessageData(v___x_4252_);
return v___x_4253_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__2));
v___x_4256_ = l_Lean_stringToMessageData(v___x_4255_);
return v___x_4256_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6(void){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__5));
v___x_4261_ = l_Lean_MessageData_ofFormat(v___x_4260_);
return v___x_4261_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8(void){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__7));
v___x_4264_ = l_Lean_stringToMessageData(v___x_4263_);
return v___x_4264_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4266_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__9));
v___x_4267_ = l_Lean_stringToMessageData(v___x_4266_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(lean_object* v_tree_4270_, lean_object* v_expectedType_x3f_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_){
_start:
{
lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___x_4300_; 
lean_inc(v_expectedType_x3f_4271_);
lean_inc_ref(v_tree_4270_);
v___x_4300_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v_tree_4270_, v_expectedType_x3f_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_toCold_4301_; lean_object* v_options_4302_; lean_object* v_a_4303_; lean_object* v_inheritedTraceOptions_4304_; uint8_t v_hasTrace_4305_; lean_object* v___x_4306_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4369_; lean_object* v___y_4370_; 
v_toCold_4301_ = lean_ctor_get(v_a_4276_, 0);
v_options_4302_ = lean_ctor_get(v_toCold_4301_, 2);
v_a_4303_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4300_, 1);
v_inheritedTraceOptions_4304_ = lean_ctor_get(v_toCold_4301_, 11);
v_hasTrace_4305_ = lean_ctor_get_uint8(v_options_4302_, sizeof(void*)*1);
v___x_4306_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
if (v_hasTrace_4305_ == 0)
{
v___y_4334_ = v_a_4272_;
v___y_4335_ = v_a_4273_;
v___y_4336_ = v_a_4274_;
v___y_4337_ = v_a_4275_;
v___y_4338_ = v_a_4276_;
v___y_4339_ = v_a_4277_;
goto v___jp_4333_;
}
else
{
lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4381_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4382_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4304_, v_options_4302_, v___x_4381_);
if (v___x_4382_ == 0)
{
v___y_4334_ = v_a_4272_;
v___y_4335_ = v_a_4273_;
v___y_4336_ = v_a_4274_;
v___y_4337_ = v_a_4275_;
v___y_4338_ = v_a_4276_;
v___y_4339_ = v_a_4277_;
goto v___jp_4333_;
}
else
{
lean_object* v_max_x3f_4383_; uint8_t v_hasUncomparable_4384_; uint8_t v_hasUnknown_4385_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___x_4397_; lean_object* v___y_4399_; 
v_max_x3f_4383_ = lean_ctor_get(v_a_4303_, 0);
v_hasUncomparable_4384_ = lean_ctor_get_uint8(v_a_4303_, sizeof(void*)*1);
v_hasUnknown_4385_ = lean_ctor_get_uint8(v_a_4303_, sizeof(void*)*1 + 1);
v___x_4397_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8);
if (v_hasUncomparable_4384_ == 0)
{
lean_object* v___x_4407_; 
v___x_4407_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_4399_ = v___x_4407_;
goto v___jp_4398_;
}
else
{
lean_object* v___x_4408_; 
v___x_4408_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_4399_ = v___x_4408_;
goto v___jp_4398_;
}
v___jp_4386_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
lean_inc_ref(v___y_4388_);
v___x_4389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4389_, 0, v___y_4388_);
v___x_4390_ = l_Lean_MessageData_ofFormat(v___x_4389_);
v___x_4391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___y_4387_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3);
v___x_4393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4391_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
if (lean_obj_tag(v_max_x3f_4383_) == 0)
{
lean_object* v___x_4394_; 
v___x_4394_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6);
v___y_4369_ = v___x_4393_;
v___y_4370_ = v___x_4394_;
goto v___jp_4368_;
}
else
{
lean_object* v_val_4395_; lean_object* v___x_4396_; 
v_val_4395_ = lean_ctor_get(v_max_x3f_4383_, 0);
lean_inc(v_val_4395_);
v___x_4396_ = l_Lean_MessageData_ofExpr(v_val_4395_);
v___y_4369_ = v___x_4393_;
v___y_4370_ = v___x_4396_;
goto v___jp_4368_;
}
}
v___jp_4398_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
lean_inc_ref(v___y_4399_);
v___x_4400_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___y_4399_);
v___x_4401_ = l_Lean_MessageData_ofFormat(v___x_4400_);
v___x_4402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4397_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10);
v___x_4404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4402_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
if (v_hasUnknown_4385_ == 0)
{
lean_object* v___x_4405_; 
v___x_4405_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_4387_ = v___x_4404_;
v___y_4388_ = v___x_4405_;
goto v___jp_4386_;
}
else
{
lean_object* v___x_4406_; 
v___x_4406_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_4387_ = v___x_4404_;
v___y_4388_ = v___x_4406_;
goto v___jp_4386_;
}
}
}
}
v___jp_4307_:
{
lean_object* v_toCold_4315_; lean_object* v_options_4316_; uint8_t v_hasTrace_4317_; 
v_toCold_4315_ = lean_ctor_get(v___y_4313_, 0);
v_options_4316_ = lean_ctor_get(v_toCold_4315_, 2);
v_hasTrace_4317_ = lean_ctor_get_uint8(v_options_4316_, sizeof(void*)*1);
if (v_hasTrace_4317_ == 0)
{
v___y_4291_ = v___y_4308_;
v___y_4292_ = v___y_4309_;
v___y_4293_ = v___y_4310_;
v___y_4294_ = v___y_4311_;
v___y_4295_ = v___y_4312_;
v___y_4296_ = v___y_4313_;
v___y_4297_ = v___y_4314_;
goto v___jp_4290_;
}
else
{
lean_object* v_inheritedTraceOptions_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; 
v_inheritedTraceOptions_4318_ = lean_ctor_get(v_toCold_4315_, 11);
v___x_4319_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4320_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4318_, v_options_4316_, v___x_4319_);
if (v___x_4320_ == 0)
{
v___y_4291_ = v___y_4308_;
v___y_4292_ = v___y_4309_;
v___y_4293_ = v___y_4310_;
v___y_4294_ = v___y_4311_;
v___y_4295_ = v___y_4312_;
v___y_4296_ = v___y_4313_;
v___y_4297_ = v___y_4314_;
goto v___jp_4290_;
}
else
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4321_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1);
lean_inc_ref(v___y_4308_);
v___x_4322_ = l_Lean_MessageData_ofExpr(v___y_4308_);
v___x_4323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4321_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
v___x_4324_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4306_, v___x_4323_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_dec_ref_known(v___x_4324_, 1);
v___y_4291_ = v___y_4308_;
v___y_4292_ = v___y_4309_;
v___y_4293_ = v___y_4310_;
v___y_4294_ = v___y_4311_;
v___y_4295_ = v___y_4312_;
v___y_4296_ = v___y_4313_;
v___y_4297_ = v___y_4314_;
goto v___jp_4290_;
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec_ref(v___y_4308_);
lean_dec(v_expectedType_x3f_4271_);
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4324_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4324_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
}
}
v___jp_4333_:
{
uint8_t v_hasUncomparable_4340_; 
v_hasUncomparable_4340_ = lean_ctor_get_uint8(v_a_4303_, sizeof(void*)*1);
if (v_hasUncomparable_4340_ == 0)
{
lean_object* v_max_x3f_4341_; 
v_max_x3f_4341_ = lean_ctor_get(v_a_4303_, 0);
lean_inc(v_max_x3f_4341_);
if (lean_obj_tag(v_max_x3f_4341_) == 0)
{
lean_dec(v_a_4303_);
v___y_4280_ = v___y_4335_;
v___y_4281_ = v___y_4334_;
v___y_4282_ = v___y_4337_;
v___y_4283_ = v___y_4339_;
v___y_4284_ = v___y_4336_;
v___y_4285_ = v___y_4338_;
goto v___jp_4279_;
}
else
{
uint8_t v_hasUnknown_4342_; lean_object* v_val_4343_; lean_object* v___x_4344_; 
v_hasUnknown_4342_ = lean_ctor_get_uint8(v_a_4303_, sizeof(void*)*1 + 1);
lean_dec(v_a_4303_);
v_val_4343_ = lean_ctor_get(v_max_x3f_4341_, 0);
lean_inc_n(v_val_4343_, 2);
lean_dec_ref_known(v_max_x3f_4341_, 1);
v___x_4344_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v_tree_4270_, v_val_4343_, v_hasUncomparable_4340_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; lean_object* v___x_4346_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4345_);
lean_dec_ref_known(v___x_4344_, 1);
v___x_4346_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_4345_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
if (lean_obj_tag(v___x_4346_) == 0)
{
if (v_hasUnknown_4342_ == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4348_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc_n(v_a_4347_, 2);
lean_dec_ref_known(v___x_4346_, 1);
lean_inc(v___y_4339_);
lean_inc_ref(v___y_4338_);
lean_inc(v___y_4337_);
lean_inc_ref(v___y_4336_);
v___x_4348_ = lean_infer_type(v_a_4347_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; lean_object* v___x_4350_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4348_, 1);
v___x_4350_ = l_Lean_Meta_isExprDefEqGuarded(v_a_4349_, v_val_4343_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_dec_ref_known(v___x_4350_, 1);
v___y_4308_ = v_a_4347_;
v___y_4309_ = v___y_4334_;
v___y_4310_ = v___y_4335_;
v___y_4311_ = v___y_4336_;
v___y_4312_ = v___y_4337_;
v___y_4313_ = v___y_4338_;
v___y_4314_ = v___y_4339_;
goto v___jp_4307_;
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec(v_a_4347_);
lean_dec(v_expectedType_x3f_4271_);
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
else
{
lean_dec(v_a_4347_);
lean_dec(v_val_4343_);
lean_dec(v_expectedType_x3f_4271_);
return v___x_4348_;
}
}
else
{
lean_object* v_a_4359_; 
lean_dec(v_val_4343_);
v_a_4359_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4346_, 1);
v___y_4308_ = v_a_4359_;
v___y_4309_ = v___y_4334_;
v___y_4310_ = v___y_4335_;
v___y_4311_ = v___y_4336_;
v___y_4312_ = v___y_4337_;
v___y_4313_ = v___y_4338_;
v___y_4314_ = v___y_4339_;
goto v___jp_4307_;
}
}
else
{
lean_dec(v_val_4343_);
lean_dec(v_expectedType_x3f_4271_);
return v___x_4346_;
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec(v_val_4343_);
lean_dec(v_expectedType_x3f_4271_);
v_a_4360_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4344_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4344_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
else
{
lean_dec(v_a_4303_);
v___y_4280_ = v___y_4335_;
v___y_4281_ = v___y_4334_;
v___y_4282_ = v___y_4337_;
v___y_4283_ = v___y_4339_;
v___y_4284_ = v___y_4336_;
v___y_4285_ = v___y_4338_;
goto v___jp_4279_;
}
}
v___jp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___y_4369_);
lean_ctor_set(v___x_4371_, 1, v___y_4370_);
v___x_4372_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4306_, v___x_4371_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_dec_ref_known(v___x_4372_, 1);
v___y_4334_ = v_a_4272_;
v___y_4335_ = v_a_4273_;
v___y_4336_ = v_a_4274_;
v___y_4337_ = v_a_4275_;
v___y_4338_ = v_a_4276_;
v___y_4339_ = v_a_4277_;
goto v___jp_4333_;
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v_a_4303_);
lean_dec(v_expectedType_x3f_4271_);
lean_dec_ref(v_tree_4270_);
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4372_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4372_);
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
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec(v_expectedType_x3f_4271_);
lean_dec_ref(v_tree_4270_);
v_a_4409_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4300_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4300_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
v___jp_4279_:
{
lean_object* v___x_4286_; 
v___x_4286_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_tree_4270_, v___y_4281_, v___y_4280_, v___y_4284_, v___y_4282_, v___y_4285_, v___y_4283_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_object* v_a_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v_a_4287_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_a_4287_);
lean_dec_ref_known(v___x_4286_, 1);
v___x_4288_ = lean_box(0);
v___x_4289_ = l_Lean_Elab_Term_ensureHasType(v_expectedType_x3f_4271_, v_a_4287_, v___x_4288_, v___x_4288_, v___y_4281_, v___y_4280_, v___y_4284_, v___y_4282_, v___y_4285_, v___y_4283_);
return v___x_4289_;
}
else
{
lean_dec(v_expectedType_x3f_4271_);
return v___x_4286_;
}
}
v___jp_4290_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = lean_box(0);
v___x_4299_ = l_Lean_Elab_Term_ensureHasType(v_expectedType_x3f_4271_, v___y_4291_, v___x_4298_, v___x_4298_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
return v___x_4299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0(lean_object* v_maxType_4417_, lean_object* v_nested_4418_, lean_object* v_f_x3f_4419_, uint8_t v_lhs_4420_, uint8_t v_isPred_4421_, lean_object* v_macroName_4422_, lean_object* v_stx_4423_, lean_object* v_stx_x27_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v___x_4432_; 
v___x_4432_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4417_, v_nested_4418_, v_f_x3f_4419_, v_lhs_4420_, v_isPred_4421_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4441_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4441_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4441_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4437_; lean_object* v___x_4439_; 
v___x_4437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4437_, 0, v_macroName_4422_);
lean_ctor_set(v___x_4437_, 1, v_stx_4423_);
lean_ctor_set(v___x_4437_, 2, v_stx_x27_4424_);
lean_ctor_set(v___x_4437_, 3, v_a_4433_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v___x_4437_);
v___x_4439_ = v___x_4435_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
else
{
lean_dec(v_stx_x27_4424_);
lean_dec(v_stx_4423_);
lean_dec(v_macroName_4422_);
return v___x_4432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0___boxed(lean_object* v_maxType_4442_, lean_object* v_nested_4443_, lean_object* v_f_x3f_4444_, lean_object* v_lhs_4445_, lean_object* v_isPred_4446_, lean_object* v_macroName_4447_, lean_object* v_stx_4448_, lean_object* v_stx_x27_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
uint8_t v_lhs_boxed_4457_; uint8_t v_isPred_boxed_4458_; lean_object* v_res_4459_; 
v_lhs_boxed_4457_ = lean_unbox(v_lhs_4445_);
v_isPred_boxed_4458_ = lean_unbox(v_isPred_4446_);
v_res_4459_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0(v_maxType_4442_, v_nested_4443_, v_f_x3f_4444_, v_lhs_boxed_4457_, v_isPred_boxed_4458_, v_macroName_4447_, v_stx_4448_, v_stx_x27_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(lean_object* v_maxType_4460_, lean_object* v_t_4461_, lean_object* v_f_x3f_4462_, uint8_t v_lhs_4463_, uint8_t v_isPred_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
switch(lean_obj_tag(v_t_4461_))
{
case 0:
{
lean_object* v_ref_4472_; lean_object* v_infoTrees_4473_; lean_object* v_val_4474_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v_toCold_4480_; lean_object* v_currRecDepth_4481_; lean_object* v_ref_4482_; uint16_t v_optionFlags_4483_; uint8_t v_suppressElabErrors_4484_; uint8_t v_checkDeprecated_4485_; uint8_t v_isRecordingDeps_4486_; lean_object* v___y_4487_; lean_object* v___x_4509_; 
v_ref_4472_ = lean_ctor_get(v_t_4461_, 0);
v_infoTrees_4473_ = lean_ctor_get(v_t_4461_, 1);
v_val_4474_ = lean_ctor_get(v_t_4461_, 2);
lean_inc(v_a_4470_);
lean_inc_ref(v_a_4469_);
lean_inc(v_a_4468_);
lean_inc_ref(v_a_4467_);
lean_inc_ref(v_val_4474_);
v___x_4509_ = lean_infer_type(v_val_4474_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_object* v_a_4510_; lean_object* v___x_4511_; 
v_a_4510_ = lean_ctor_get(v___x_4509_, 0);
lean_inc(v_a_4510_);
lean_dec_ref_known(v___x_4509_, 1);
v___x_4511_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_elabListLitAux_getListInfo_spec__1___redArg(v_a_4510_, v_a_4468_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_toCold_4512_; lean_object* v_options_4513_; lean_object* v_a_4514_; lean_object* v_inheritedTraceOptions_4515_; uint8_t v_hasTrace_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; 
v_toCold_4512_ = lean_ctor_get(v_a_4469_, 0);
v_options_4513_ = lean_ctor_get(v_toCold_4512_, 2);
v_a_4514_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4511_, 1);
v_inheritedTraceOptions_4515_ = lean_ctor_get(v_toCold_4512_, 11);
v_hasTrace_4516_ = lean_ctor_get_uint8(v_options_4513_, sizeof(void*)*1);
v___x_4517_ = l_Lean_Expr_cleanupAnnotations(v_a_4514_);
lean_dec(v_a_4514_);
v___x_4518_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
if (v_hasTrace_4516_ == 0)
{
v___y_4583_ = v_a_4465_;
v___y_4584_ = v_a_4466_;
v___y_4585_ = v_a_4467_;
v___y_4586_ = v_a_4468_;
v___y_4587_ = v_a_4469_;
v___y_4588_ = v_a_4470_;
goto v___jp_4582_;
}
else
{
lean_object* v___x_4609_; uint8_t v___x_4610_; 
v___x_4609_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4610_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4515_, v_options_4513_, v___x_4609_);
if (v___x_4610_ == 0)
{
v___y_4583_ = v_a_4465_;
v___y_4584_ = v_a_4466_;
v___y_4585_ = v_a_4467_;
v___y_4586_ = v_a_4468_;
v___y_4587_ = v_a_4469_;
v___y_4588_ = v_a_4470_;
goto v___jp_4582_;
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4611_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__7);
lean_inc_ref(v_val_4474_);
v___x_4612_ = l_Lean_MessageData_ofExpr(v_val_4474_);
v___x_4613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4611_);
lean_ctor_set(v___x_4613_, 1, v___x_4612_);
v___x_4614_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3);
v___x_4615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4613_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
lean_inc_ref(v___x_4517_);
v___x_4616_ = l_Lean_MessageData_ofExpr(v___x_4517_);
v___x_4617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4615_);
lean_ctor_set(v___x_4617_, 1, v___x_4616_);
v___x_4618_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__9);
v___x_4619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4617_);
lean_ctor_set(v___x_4619_, 1, v___x_4618_);
lean_inc_ref(v_maxType_4460_);
v___x_4620_ = l_Lean_MessageData_ofExpr(v_maxType_4460_);
v___x_4621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4619_);
lean_ctor_set(v___x_4621_, 1, v___x_4620_);
v___x_4622_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4518_, v___x_4621_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_dec_ref_known(v___x_4622_, 1);
v___y_4583_ = v_a_4465_;
v___y_4584_ = v_a_4466_;
v___y_4585_ = v_a_4467_;
v___y_4586_ = v_a_4468_;
v___y_4587_ = v_a_4469_;
v___y_4588_ = v_a_4470_;
goto v___jp_4582_;
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
lean_dec_ref(v___x_4517_);
lean_dec_ref_known(v_t_4461_, 3);
lean_dec(v_f_x3f_4462_);
lean_dec_ref(v_maxType_4460_);
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4622_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4622_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
}
v___jp_4519_:
{
lean_object* v___x_4526_; 
lean_inc_ref(v___x_4517_);
lean_inc_ref(v_maxType_4460_);
v___x_4526_ = l_Lean_Meta_isExprDefEqGuarded(v_maxType_4460_, v___x_4517_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4573_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4529_ = v___x_4526_;
v_isShared_4530_ = v_isSharedCheck_4573_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4526_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4573_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
uint8_t v___x_4531_; 
v___x_4531_ = lean_unbox(v_a_4527_);
lean_dec(v_a_4527_);
if (v___x_4531_ == 0)
{
lean_object* v_toCold_4532_; lean_object* v_options_4533_; uint8_t v_hasTrace_4534_; 
lean_inc_ref(v_val_4474_);
lean_inc_ref(v_infoTrees_4473_);
lean_inc(v_ref_4472_);
lean_del_object(v___x_4529_);
lean_dec_ref_known(v_t_4461_, 3);
v_toCold_4532_ = lean_ctor_get(v___y_4524_, 0);
v_options_4533_ = lean_ctor_get(v_toCold_4532_, 2);
v_hasTrace_4534_ = lean_ctor_get_uint8(v_options_4533_, sizeof(void*)*1);
if (v_hasTrace_4534_ == 0)
{
lean_object* v_currRecDepth_4535_; lean_object* v_ref_4536_; uint16_t v_optionFlags_4537_; uint8_t v_suppressElabErrors_4538_; uint8_t v_checkDeprecated_4539_; uint8_t v_isRecordingDeps_4540_; 
lean_dec_ref(v___x_4517_);
v_currRecDepth_4535_ = lean_ctor_get(v___y_4524_, 1);
v_ref_4536_ = lean_ctor_get(v___y_4524_, 2);
v_optionFlags_4537_ = lean_ctor_get_uint16(v___y_4524_, sizeof(void*)*3);
v_suppressElabErrors_4538_ = lean_ctor_get_uint8(v___y_4524_, sizeof(void*)*3 + 2);
v_checkDeprecated_4539_ = lean_ctor_get_uint8(v___y_4524_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4540_ = lean_ctor_get_uint8(v___y_4524_, sizeof(void*)*3 + 4);
v___y_4476_ = v___y_4520_;
v___y_4477_ = v___y_4521_;
v___y_4478_ = v___y_4522_;
v___y_4479_ = v___y_4523_;
v_toCold_4480_ = v_toCold_4532_;
v_currRecDepth_4481_ = v_currRecDepth_4535_;
v_ref_4482_ = v_ref_4536_;
v_optionFlags_4483_ = v_optionFlags_4537_;
v_suppressElabErrors_4484_ = v_suppressElabErrors_4538_;
v_checkDeprecated_4485_ = v_checkDeprecated_4539_;
v_isRecordingDeps_4486_ = v_isRecordingDeps_4540_;
v___y_4487_ = v___y_4525_;
goto v___jp_4475_;
}
else
{
lean_object* v_currRecDepth_4541_; lean_object* v_ref_4542_; uint16_t v_optionFlags_4543_; uint8_t v_suppressElabErrors_4544_; uint8_t v_checkDeprecated_4545_; uint8_t v_isRecordingDeps_4546_; lean_object* v_inheritedTraceOptions_4547_; lean_object* v___x_4548_; uint8_t v___x_4549_; 
v_currRecDepth_4541_ = lean_ctor_get(v___y_4524_, 1);
v_ref_4542_ = lean_ctor_get(v___y_4524_, 2);
v_optionFlags_4543_ = lean_ctor_get_uint16(v___y_4524_, sizeof(void*)*3);
v_suppressElabErrors_4544_ = lean_ctor_get_uint8(v___y_4524_, sizeof(void*)*3 + 2);
v_checkDeprecated_4545_ = lean_ctor_get_uint8(v___y_4524_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4546_ = lean_ctor_get_uint8(v___y_4524_, sizeof(void*)*3 + 4);
v_inheritedTraceOptions_4547_ = lean_ctor_get(v_toCold_4532_, 11);
v___x_4548_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__3);
v___x_4549_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4547_, v_options_4533_, v___x_4548_);
if (v___x_4549_ == 0)
{
lean_dec_ref(v___x_4517_);
v___y_4476_ = v___y_4520_;
v___y_4477_ = v___y_4521_;
v___y_4478_ = v___y_4522_;
v___y_4479_ = v___y_4523_;
v_toCold_4480_ = v_toCold_4532_;
v_currRecDepth_4481_ = v_currRecDepth_4541_;
v_ref_4482_ = v_ref_4542_;
v_optionFlags_4483_ = v_optionFlags_4543_;
v_suppressElabErrors_4484_ = v_suppressElabErrors_4544_;
v_checkDeprecated_4485_ = v_checkDeprecated_4545_;
v_isRecordingDeps_4486_ = v_isRecordingDeps_4546_;
v___y_4487_ = v___y_4525_;
goto v___jp_4475_;
}
else
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4550_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__1);
lean_inc_ref(v_val_4474_);
v___x_4551_ = l_Lean_MessageData_ofExpr(v_val_4474_);
v___x_4552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4550_);
lean_ctor_set(v___x_4552_, 1, v___x_4551_);
v___x_4553_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__3);
v___x_4554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4552_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = l_Lean_MessageData_ofExpr(v___x_4517_);
v___x_4556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4554_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
v___x_4557_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___closed__5);
v___x_4558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4556_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
lean_inc_ref(v_maxType_4460_);
v___x_4559_ = l_Lean_MessageData_ofExpr(v_maxType_4460_);
v___x_4560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
v___x_4561_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_4518_, v___x_4560_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_dec_ref_known(v___x_4561_, 1);
v___y_4476_ = v___y_4520_;
v___y_4477_ = v___y_4521_;
v___y_4478_ = v___y_4522_;
v___y_4479_ = v___y_4523_;
v_toCold_4480_ = v_toCold_4532_;
v_currRecDepth_4481_ = v_currRecDepth_4541_;
v_ref_4482_ = v_ref_4542_;
v_optionFlags_4483_ = v_optionFlags_4543_;
v_suppressElabErrors_4484_ = v_suppressElabErrors_4544_;
v_checkDeprecated_4485_ = v_checkDeprecated_4545_;
v_isRecordingDeps_4486_ = v_isRecordingDeps_4546_;
v___y_4487_ = v___y_4525_;
goto v___jp_4475_;
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref(v_val_4474_);
lean_dec_ref(v_infoTrees_4473_);
lean_dec(v_ref_4472_);
lean_dec_ref(v_maxType_4460_);
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4561_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4561_);
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
}
}
else
{
lean_object* v___x_4571_; 
lean_dec_ref(v___x_4517_);
lean_dec_ref(v_maxType_4460_);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v_t_4461_);
v___x_4571_ = v___x_4529_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_t_4461_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
lean_dec_ref(v___x_4517_);
lean_dec_ref_known(v_t_4461_, 3);
lean_dec_ref(v_maxType_4460_);
v_a_4574_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4526_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4526_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
v___jp_4582_:
{
uint8_t v___x_4589_; 
v___x_4589_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_isUnknown(v___x_4517_);
if (v___x_4589_ == 0)
{
lean_dec(v_f_x3f_4462_);
v___y_4520_ = v___y_4583_;
v___y_4521_ = v___y_4584_;
v___y_4522_ = v___y_4585_;
v___y_4523_ = v___y_4586_;
v___y_4524_ = v___y_4587_;
v___y_4525_ = v___y_4588_;
goto v___jp_4519_;
}
else
{
if (lean_obj_tag(v_f_x3f_4462_) == 1)
{
lean_object* v_val_4590_; lean_object* v___x_4591_; 
v_val_4590_ = lean_ctor_get(v_f_x3f_4462_, 0);
lean_inc(v_val_4590_);
lean_dec_ref_known(v_f_x3f_4462_, 1);
v___x_4591_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHeterogeneousDefaultInstances(v_val_4590_, v_maxType_4460_, v_lhs_4463_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec(v_val_4590_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4600_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4594_ = v___x_4591_;
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4591_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
uint8_t v___x_4596_; 
v___x_4596_ = lean_unbox(v_a_4592_);
lean_dec(v_a_4592_);
if (v___x_4596_ == 0)
{
lean_del_object(v___x_4594_);
v___y_4520_ = v___y_4583_;
v___y_4521_ = v___y_4584_;
v___y_4522_ = v___y_4585_;
v___y_4523_ = v___y_4586_;
v___y_4524_ = v___y_4587_;
v___y_4525_ = v___y_4588_;
goto v___jp_4519_;
}
else
{
lean_object* v___x_4598_; 
lean_dec_ref(v___x_4517_);
lean_dec_ref(v_maxType_4460_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v_t_4461_);
v___x_4598_ = v___x_4594_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_t_4461_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec_ref(v___x_4517_);
lean_dec_ref_known(v_t_4461_, 3);
lean_dec_ref(v_maxType_4460_);
v_a_4601_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4591_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4591_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
else
{
lean_dec(v_f_x3f_4462_);
v___y_4520_ = v___y_4583_;
v___y_4521_ = v___y_4584_;
v___y_4522_ = v___y_4585_;
v___y_4523_ = v___y_4586_;
v___y_4524_ = v___y_4587_;
v___y_4525_ = v___y_4588_;
goto v___jp_4519_;
}
}
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_dec_ref_known(v_t_4461_, 3);
lean_dec(v_f_x3f_4462_);
lean_dec_ref(v_maxType_4460_);
v_a_4631_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4511_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4511_);
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
lean_dec_ref_known(v_t_4461_, 3);
lean_dec(v_f_x3f_4462_);
lean_dec_ref(v_maxType_4460_);
v_a_4639_ = lean_ctor_get(v___x_4509_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4509_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4509_);
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
v___jp_4475_:
{
lean_object* v___x_4488_; lean_object* v_ref_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4488_ = lean_box(0);
v_ref_4489_ = l_Lean_replaceRef(v_ref_4472_, v_ref_4482_);
lean_inc(v_currRecDepth_4481_);
lean_inc_ref(v_toCold_4480_);
v___x_4490_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4490_, 0, v_toCold_4480_);
lean_ctor_set(v___x_4490_, 1, v_currRecDepth_4481_);
lean_ctor_set(v___x_4490_, 2, v_ref_4489_);
lean_ctor_set_uint16(v___x_4490_, sizeof(void*)*3, v_optionFlags_4483_);
lean_ctor_set_uint8(v___x_4490_, sizeof(void*)*3 + 2, v_suppressElabErrors_4484_);
lean_ctor_set_uint8(v___x_4490_, sizeof(void*)*3 + 3, v_checkDeprecated_4485_);
lean_ctor_set_uint8(v___x_4490_, sizeof(void*)*3 + 4, v_isRecordingDeps_4486_);
v___x_4491_ = l_Lean_Elab_Term_mkCoe(v_maxType_4460_, v_val_4474_, v___x_4488_, v___x_4488_, v___x_4488_, v___x_4488_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___x_4490_, v___y_4487_);
lean_dec_ref_known(v___x_4490_, 3);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4500_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4494_ = v___x_4491_;
v_isShared_4495_ = v_isSharedCheck_4500_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4491_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4500_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4496_, 0, v_ref_4472_);
lean_ctor_set(v___x_4496_, 1, v_infoTrees_4473_);
lean_ctor_set(v___x_4496_, 2, v_a_4492_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4496_);
v___x_4498_ = v___x_4494_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec_ref(v_infoTrees_4473_);
lean_dec(v_ref_4472_);
v_a_4501_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4491_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4491_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
case 1:
{
lean_object* v_ref_4647_; uint8_t v_kind_4648_; lean_object* v_f_4649_; lean_object* v_lhs_4650_; lean_object* v_rhs_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4768_; 
lean_dec(v_f_x3f_4462_);
v_ref_4647_ = lean_ctor_get(v_t_4461_, 0);
v_kind_4648_ = lean_ctor_get_uint8(v_t_4461_, sizeof(void*)*4);
v_f_4649_ = lean_ctor_get(v_t_4461_, 1);
v_lhs_4650_ = lean_ctor_get(v_t_4461_, 2);
v_rhs_4651_ = lean_ctor_get(v_t_4461_, 3);
v_isSharedCheck_4768_ = !lean_is_exclusive(v_t_4461_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4653_ = v_t_4461_;
v_isShared_4654_ = v_isSharedCheck_4768_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_rhs_4651_);
lean_inc(v_lhs_4650_);
lean_inc(v_f_4649_);
lean_inc(v_ref_4647_);
lean_dec(v_t_4461_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4768_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
switch(v_kind_4648_)
{
case 2:
{
lean_object* v___x_4673_; uint8_t v___x_4674_; lean_object* v___x_4675_; 
lean_del_object(v___x_4653_);
v___x_4673_ = lean_box(0);
v___x_4674_ = 0;
v___x_4675_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4460_, v_rhs_4651_, v___x_4673_, v___x_4674_, v___x_4674_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4684_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4684_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4684_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4680_; lean_object* v___x_4682_; 
v___x_4680_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_4680_, 0, v_ref_4647_);
lean_ctor_set(v___x_4680_, 1, v_f_4649_);
lean_ctor_set(v___x_4680_, 2, v_lhs_4650_);
lean_ctor_set(v___x_4680_, 3, v_a_4676_);
lean_ctor_set_uint8(v___x_4680_, sizeof(void*)*4, v_kind_4648_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 0, v___x_4680_);
v___x_4682_ = v___x_4678_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4680_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
else
{
lean_dec_ref(v_lhs_4650_);
lean_dec_ref(v_f_4649_);
lean_dec(v_ref_4647_);
return v___x_4675_;
}
}
case 3:
{
lean_object* v___x_4685_; uint8_t v___x_4686_; lean_object* v___x_4687_; 
lean_del_object(v___x_4653_);
v___x_4685_ = lean_box(0);
v___x_4686_ = 0;
v___x_4687_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4460_, v_lhs_4650_, v___x_4685_, v___x_4686_, v___x_4686_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4696_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4690_ = v___x_4687_;
v_isShared_4691_ = v_isSharedCheck_4696_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4687_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4696_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4692_; lean_object* v___x_4694_; 
v___x_4692_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_4692_, 0, v_ref_4647_);
lean_ctor_set(v___x_4692_, 1, v_f_4649_);
lean_ctor_set(v___x_4692_, 2, v_a_4688_);
lean_ctor_set(v___x_4692_, 3, v_rhs_4651_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*4, v_kind_4648_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 0, v___x_4692_);
v___x_4694_ = v___x_4690_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4692_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
else
{
lean_dec_ref(v_rhs_4651_);
lean_dec_ref(v_f_4649_);
lean_dec(v_ref_4647_);
return v___x_4687_;
}
}
default: 
{
if (v_isPred_4464_ == 0)
{
lean_object* v___x_4697_; 
lean_inc_ref(v_maxType_4460_);
v___x_4697_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_hasHomogeneousInstance(v_f_4649_, v_maxType_4460_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; uint8_t v___x_4699_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4698_);
lean_dec_ref_known(v___x_4697_, 1);
v___x_4699_ = lean_unbox(v_a_4698_);
lean_dec(v_a_4698_);
if (v___x_4699_ == 0)
{
lean_object* v_toCold_4700_; lean_object* v_currRecDepth_4701_; lean_object* v_ref_4702_; uint16_t v_optionFlags_4703_; uint8_t v_suppressElabErrors_4704_; uint8_t v_checkDeprecated_4705_; uint8_t v_isRecordingDeps_4706_; lean_object* v___x_4707_; lean_object* v_ref_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
lean_del_object(v___x_4653_);
lean_dec_ref(v_maxType_4460_);
v_toCold_4700_ = lean_ctor_get(v_a_4469_, 0);
v_currRecDepth_4701_ = lean_ctor_get(v_a_4469_, 1);
v_ref_4702_ = lean_ctor_get(v_a_4469_, 2);
v_optionFlags_4703_ = lean_ctor_get_uint16(v_a_4469_, sizeof(void*)*3);
v_suppressElabErrors_4704_ = lean_ctor_get_uint8(v_a_4469_, sizeof(void*)*3 + 2);
v_checkDeprecated_4705_ = lean_ctor_get_uint8(v_a_4469_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4706_ = lean_ctor_get_uint8(v_a_4469_, sizeof(void*)*3 + 4);
v___x_4707_ = lean_box(0);
v_ref_4708_ = l_Lean_replaceRef(v_ref_4647_, v_ref_4702_);
lean_inc(v_currRecDepth_4701_);
lean_inc_ref(v_toCold_4700_);
v___x_4709_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4709_, 0, v_toCold_4700_);
lean_ctor_set(v___x_4709_, 1, v_currRecDepth_4701_);
lean_ctor_set(v___x_4709_, 2, v_ref_4708_);
lean_ctor_set_uint16(v___x_4709_, sizeof(void*)*3, v_optionFlags_4703_);
lean_ctor_set_uint8(v___x_4709_, sizeof(void*)*3 + 2, v_suppressElabErrors_4704_);
lean_ctor_set_uint8(v___x_4709_, sizeof(void*)*3 + 3, v_checkDeprecated_4705_);
lean_ctor_set_uint8(v___x_4709_, sizeof(void*)*3 + 4, v_isRecordingDeps_4706_);
v___x_4710_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_lhs_4650_, v___x_4707_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v___x_4709_, v_a_4470_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v___x_4712_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4711_);
lean_dec_ref_known(v___x_4710_, 1);
v___x_4712_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_rhs_4651_, v___x_4707_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v___x_4709_, v_a_4470_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; uint8_t v___x_4714_; uint8_t v___x_4715_; lean_object* v___x_4716_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
lean_inc(v_a_4713_);
lean_dec_ref_known(v___x_4712_, 1);
v___x_4714_ = 1;
v___x_4715_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_instBEqBinOpKind_beq(v_kind_4648_, v___x_4714_);
v___x_4716_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp(v___x_4715_, v_f_4649_, v_a_4711_, v_a_4713_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v___x_4709_, v_a_4470_);
lean_dec_ref_known(v___x_4709_, 3);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; lean_object* v___x_4718_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref_known(v___x_4716_, 1);
v___x_4718_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processLeaf_spec__0___redArg(v_a_4470_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4727_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4721_ = v___x_4718_;
v_isShared_4722_ = v_isSharedCheck_4727_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4718_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4727_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4723_; lean_object* v___x_4725_; 
v___x_4723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4723_, 0, v_ref_4647_);
lean_ctor_set(v___x_4723_, 1, v_a_4719_);
lean_ctor_set(v___x_4723_, 2, v_a_4717_);
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 0, v___x_4723_);
v___x_4725_ = v___x_4721_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4723_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
lean_dec(v_a_4717_);
lean_dec(v_ref_4647_);
v_a_4728_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4730_ = v___x_4718_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4718_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4743_; 
lean_dec(v_ref_4647_);
v_a_4736_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4738_ = v___x_4716_;
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4716_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v_a_4711_);
lean_dec_ref_known(v___x_4709_, 3);
lean_dec_ref(v_f_4649_);
lean_dec(v_ref_4647_);
v_a_4744_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4712_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4712_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_dec_ref_known(v___x_4709_, 3);
lean_dec_ref(v_rhs_4651_);
lean_dec_ref(v_f_4649_);
lean_dec(v_ref_4647_);
v_a_4752_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4710_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4710_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
else
{
goto v___jp_4655_;
}
}
else
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_del_object(v___x_4653_);
lean_dec_ref(v_rhs_4651_);
lean_dec_ref(v_lhs_4650_);
lean_dec_ref(v_f_4649_);
lean_dec(v_ref_4647_);
lean_dec_ref(v_maxType_4460_);
v_a_4760_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4697_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4697_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
}
else
{
goto v___jp_4655_;
}
}
}
v___jp_4655_:
{
uint8_t v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; lean_object* v___x_4659_; 
v___x_4656_ = 1;
lean_inc_ref(v_f_4649_);
v___x_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4657_, 0, v_f_4649_);
v___x_4658_ = 0;
lean_inc_ref(v___x_4657_);
lean_inc_ref(v_maxType_4460_);
v___x_4659_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4460_, v_lhs_4650_, v___x_4657_, v___x_4656_, v___x_4658_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4661_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
lean_inc(v_a_4660_);
lean_dec_ref_known(v___x_4659_, 1);
v___x_4661_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4460_, v_rhs_4651_, v___x_4657_, v___x_4658_, v___x_4658_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
if (lean_obj_tag(v___x_4661_) == 0)
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4672_; 
v_a_4662_ = lean_ctor_get(v___x_4661_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4661_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4664_ = v___x_4661_;
v_isShared_4665_ = v_isSharedCheck_4672_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4661_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4672_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4654_ == 0)
{
lean_ctor_set(v___x_4653_, 3, v_a_4662_);
lean_ctor_set(v___x_4653_, 2, v_a_4660_);
v___x_4667_ = v___x_4653_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_ref_4647_);
lean_ctor_set(v_reuseFailAlloc_4671_, 1, v_f_4649_);
lean_ctor_set(v_reuseFailAlloc_4671_, 2, v_a_4660_);
lean_ctor_set(v_reuseFailAlloc_4671_, 3, v_a_4662_);
lean_ctor_set_uint8(v_reuseFailAlloc_4671_, sizeof(void*)*4, v_kind_4648_);
v___x_4667_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
lean_object* v___x_4669_; 
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 0, v___x_4667_);
v___x_4669_ = v___x_4664_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4667_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
else
{
lean_dec(v_a_4660_);
lean_del_object(v___x_4653_);
lean_dec_ref(v_f_4649_);
lean_dec(v_ref_4647_);
return v___x_4661_;
}
}
else
{
lean_dec_ref_known(v___x_4657_, 1);
lean_del_object(v___x_4653_);
lean_dec_ref(v_rhs_4651_);
lean_dec_ref(v_f_4649_);
lean_dec(v_ref_4647_);
lean_dec_ref(v_maxType_4460_);
return v___x_4659_;
}
}
}
}
case 2:
{
lean_object* v_ref_4769_; lean_object* v_f_4770_; lean_object* v_arg_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_f_x3f_4462_);
v_ref_4769_ = lean_ctor_get(v_t_4461_, 0);
v_f_4770_ = lean_ctor_get(v_t_4461_, 1);
v_arg_4771_ = lean_ctor_get(v_t_4461_, 2);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_t_4461_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4773_ = v_t_4461_;
v_isShared_4774_ = v_isSharedCheck_4789_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_arg_4771_);
lean_inc(v_f_4770_);
lean_inc(v_ref_4769_);
lean_dec(v_t_4461_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4789_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4775_; uint8_t v___x_4776_; lean_object* v___x_4777_; 
v___x_4775_ = lean_box(0);
v___x_4776_ = 0;
v___x_4777_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4460_, v_arg_4771_, v___x_4775_, v___x_4776_, v___x_4776_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4788_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4780_ = v___x_4777_;
v_isShared_4781_ = v_isSharedCheck_4788_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4788_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 2, v_a_4778_);
v___x_4783_ = v___x_4773_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_ref_4769_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v_f_4770_);
lean_ctor_set(v_reuseFailAlloc_4787_, 2, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
lean_object* v___x_4785_; 
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v___x_4783_);
v___x_4785_ = v___x_4780_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
else
{
lean_del_object(v___x_4773_);
lean_dec_ref(v_f_4770_);
lean_dec(v_ref_4769_);
return v___x_4777_;
}
}
}
default: 
{
lean_object* v_macroName_4790_; lean_object* v_stx_4791_; lean_object* v_stx_x27_4792_; lean_object* v_nested_4793_; lean_object* v_toCold_4794_; lean_object* v_currRecDepth_4795_; lean_object* v_ref_4796_; uint16_t v_optionFlags_4797_; uint8_t v_suppressElabErrors_4798_; uint8_t v_checkDeprecated_4799_; uint8_t v_isRecordingDeps_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___f_4803_; lean_object* v_ref_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v_macroName_4790_ = lean_ctor_get(v_t_4461_, 0);
lean_inc(v_macroName_4790_);
v_stx_4791_ = lean_ctor_get(v_t_4461_, 1);
lean_inc_n(v_stx_4791_, 2);
v_stx_x27_4792_ = lean_ctor_get(v_t_4461_, 2);
lean_inc_n(v_stx_x27_4792_, 2);
v_nested_4793_ = lean_ctor_get(v_t_4461_, 3);
lean_inc_ref(v_nested_4793_);
lean_dec_ref_known(v_t_4461_, 4);
v_toCold_4794_ = lean_ctor_get(v_a_4469_, 0);
v_currRecDepth_4795_ = lean_ctor_get(v_a_4469_, 1);
v_ref_4796_ = lean_ctor_get(v_a_4469_, 2);
v_optionFlags_4797_ = lean_ctor_get_uint16(v_a_4469_, sizeof(void*)*3);
v_suppressElabErrors_4798_ = lean_ctor_get_uint8(v_a_4469_, sizeof(void*)*3 + 2);
v_checkDeprecated_4799_ = lean_ctor_get_uint8(v_a_4469_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4800_ = lean_ctor_get_uint8(v_a_4469_, sizeof(void*)*3 + 4);
v___x_4801_ = lean_box(v_lhs_4463_);
v___x_4802_ = lean_box(v_isPred_4464_);
v___f_4803_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4803_, 0, v_maxType_4460_);
lean_closure_set(v___f_4803_, 1, v_nested_4793_);
lean_closure_set(v___f_4803_, 2, v_f_x3f_4462_);
lean_closure_set(v___f_4803_, 3, v___x_4801_);
lean_closure_set(v___f_4803_, 4, v___x_4802_);
lean_closure_set(v___f_4803_, 5, v_macroName_4790_);
lean_closure_set(v___f_4803_, 6, v_stx_4791_);
lean_closure_set(v___f_4803_, 7, v_stx_x27_4792_);
v_ref_4804_ = l_Lean_replaceRef(v_stx_4791_, v_ref_4796_);
lean_inc(v_currRecDepth_4795_);
lean_inc_ref(v_toCold_4794_);
v___x_4805_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4805_, 0, v_toCold_4794_);
lean_ctor_set(v___x_4805_, 1, v_currRecDepth_4795_);
lean_ctor_set(v___x_4805_, 2, v_ref_4804_);
lean_ctor_set_uint16(v___x_4805_, sizeof(void*)*3, v_optionFlags_4797_);
lean_ctor_set_uint8(v___x_4805_, sizeof(void*)*3 + 2, v_suppressElabErrors_4798_);
lean_ctor_set_uint8(v___x_4805_, sizeof(void*)*3 + 3, v_checkDeprecated_4799_);
lean_ctor_set_uint8(v___x_4805_, sizeof(void*)*3 + 4, v_isRecordingDeps_4800_);
v___x_4806_ = l_Lean_Elab_Term_withPushMacroExpansionStack___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go_spec__0___redArg(v_stx_4791_, v_stx_x27_4792_, v___f_4803_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v___x_4805_, v_a_4470_);
lean_dec_ref_known(v___x_4805_, 3);
return v___x_4806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(lean_object* v_t_4807_, lean_object* v_maxType_4808_, uint8_t v_isPred_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_){
_start:
{
lean_object* v___x_4817_; uint8_t v___x_4818_; lean_object* v___x_4819_; 
v___x_4817_ = lean_box(0);
v___x_4818_ = 0;
v___x_4819_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4808_, v_t_4807_, v___x_4817_, v___x_4818_, v_isPred_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe___boxed(lean_object* v_t_4820_, lean_object* v_maxType_4821_, lean_object* v_isPred_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_){
_start:
{
uint8_t v_isPred_boxed_4830_; lean_object* v_res_4831_; 
v_isPred_boxed_4830_ = lean_unbox(v_isPred_4822_);
v_res_4831_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v_t_4820_, v_maxType_4821_, v_isPred_boxed_4830_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
lean_dec(v_a_4826_);
lean_dec_ref(v_a_4825_);
lean_dec(v_a_4824_);
lean_dec_ref(v_a_4823_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___boxed(lean_object* v_tree_4832_, lean_object* v_expectedType_x3f_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_tree_4832_, v_expectedType_x3f_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
lean_dec(v_a_4835_);
lean_dec_ref(v_a_4834_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go___boxed(lean_object* v_maxType_4842_, lean_object* v_t_4843_, lean_object* v_f_x3f_4844_, lean_object* v_lhs_4845_, lean_object* v_isPred_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_){
_start:
{
uint8_t v_lhs_boxed_4854_; uint8_t v_isPred_boxed_4855_; lean_object* v_res_4856_; 
v_lhs_boxed_4854_ = lean_unbox(v_lhs_4845_);
v_isPred_boxed_4855_ = lean_unbox(v_isPred_4846_);
v_res_4856_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go(v_maxType_4842_, v_t_4843_, v_f_x3f_4844_, v_lhs_boxed_4854_, v_isPred_boxed_4855_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec_ref(v_a_4849_);
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr_spec__2(lean_object* v_msg_4857_){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4858_ = l_Lean_instInhabitedExpr;
v___x_4859_ = lean_panic_fn_borrowed(v___x_4858_, v_msg_4857_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0(lean_object* v_cls_4860_, lean_object* v_msg_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v_cls_4860_, v_msg_4861_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___boxed(lean_object* v_cls_4870_, lean_object* v_msg_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0(v_cls_4870_, v_msg_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp(lean_object* v_stx_4880_, lean_object* v_expectedType_x3f_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_){
_start:
{
lean_object* v___x_4889_; 
v___x_4889_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v_stx_4880_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4891_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4889_, 1);
v___x_4891_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr(v_a_4890_, v_expectedType_x3f_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
return v___x_4891_;
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec(v_expectedType_x3f_4881_);
v_a_4892_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4889_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4889_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabOp___boxed(lean_object* v_stx_4900_, lean_object* v_expectedType_x3f_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_Lean_Elab_Term_Op_elabOp(v_stx_4900_, v_expectedType_x3f_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
lean_dec(v_a_4903_);
lean_dec_ref(v_a_4902_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp(lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_){
_start:
{
lean_object* v___x_4919_; 
v___x_4919_ = l_Lean_Elab_Term_Op_elabOp(v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOp___boxed(lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Lean_Elab_Term_Op_elabBinOp(v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
lean_dec(v_a_4927_);
lean_dec_ref(v_a_4926_);
lean_dec(v_a_4925_);
lean_dec_ref(v_a_4924_);
lean_dec(v_a_4923_);
lean_dec_ref(v_a_4922_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1(){
_start:
{
lean_object* v___f_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___f_4939_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_4940_ = l_Lean_Elab_Term_termElabAttribute;
v___x_4941_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__1));
v___x_4942_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2));
v___x_4943_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4940_, v___x_4941_, v___x_4942_, v___f_4939_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___boxed(lean_object* v_a_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1();
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3(){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4972_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp__1___closed__2));
v___x_4973_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___closed__6));
v___x_4974_ = l_Lean_addBuiltinDeclarationRanges(v___x_4972_, v___x_4973_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3___boxed(lean_object* v_a_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOp___regBuiltin_Lean_Elab_Term_Op_elabBinOp_declRange__3();
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy(lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_){
_start:
{
lean_object* v___x_4986_; 
v___x_4986_ = l_Lean_Elab_Term_Op_elabOp(v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
return v___x_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinOpLazy___boxed(lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Lean_Elab_Term_Op_elabBinOpLazy(v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
lean_dec(v_a_4994_);
lean_dec_ref(v_a_4993_);
lean_dec(v_a_4992_);
lean_dec_ref(v_a_4991_);
lean_dec(v_a_4990_);
lean_dec_ref(v_a_4989_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1(){
_start:
{
lean_object* v___f_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___f_5005_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_5006_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5007_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__3));
v___x_5008_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1));
v___x_5009_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5006_, v___x_5007_, v___x_5008_, v___f_5005_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___boxed(lean_object* v_a_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1();
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3(){
_start:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5038_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy__1___closed__1));
v___x_5039_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___closed__6));
v___x_5040_ = l_Lean_addBuiltinDeclarationRanges(v___x_5038_, v___x_5039_);
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3___boxed(lean_object* v_a_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinOpLazy___regBuiltin_Lean_Elab_Term_Op_elabBinOpLazy_declRange__3();
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact(lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Lean_Elab_Term_Op_elabOp(v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabLeftact___boxed(lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_Elab_Term_Op_elabLeftact(v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
lean_dec(v_a_5056_);
lean_dec_ref(v_a_5055_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1(){
_start:
{
lean_object* v___f_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; 
v___f_5071_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_5072_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5073_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__7));
v___x_5074_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1));
v___x_5075_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5072_, v___x_5073_, v___x_5074_, v___f_5071_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___boxed(lean_object* v_a_5076_){
_start:
{
lean_object* v_res_5077_; 
v_res_5077_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1();
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3(){
_start:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5104_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact__1___closed__1));
v___x_5105_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___closed__6));
v___x_5106_ = l_Lean_addBuiltinDeclarationRanges(v___x_5104_, v___x_5105_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3___boxed(lean_object* v_a_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabLeftact___regBuiltin_Lean_Elab_Term_Op_elabLeftact_declRange__3();
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact(lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_){
_start:
{
lean_object* v___x_5118_; 
v___x_5118_ = l_Lean_Elab_Term_Op_elabOp(v_a_5109_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabRightact___boxed(lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l_Lean_Elab_Term_Op_elabRightact(v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_);
lean_dec(v_a_5126_);
lean_dec_ref(v_a_5125_);
lean_dec(v_a_5124_);
lean_dec_ref(v_a_5123_);
lean_dec(v_a_5122_);
lean_dec_ref(v_a_5121_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1(){
_start:
{
lean_object* v___f_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
v___f_5137_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_5138_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5139_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__9));
v___x_5140_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1));
v___x_5141_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5138_, v___x_5139_, v___x_5140_, v___f_5137_);
return v___x_5141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___boxed(lean_object* v_a_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1();
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3(){
_start:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5170_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact__1___closed__1));
v___x_5171_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___closed__6));
v___x_5172_ = l_Lean_addBuiltinDeclarationRanges(v___x_5170_, v___x_5171_);
return v___x_5172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3___boxed(lean_object* v_a_5173_){
_start:
{
lean_object* v_res_5174_; 
v_res_5174_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabRightact___regBuiltin_Lean_Elab_Term_Op_elabRightact_declRange__3();
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp(lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_){
_start:
{
lean_object* v___x_5184_; 
v___x_5184_ = l_Lean_Elab_Term_Op_elabOp(v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabUnOp___boxed(lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_Lean_Elab_Term_Op_elabUnOp(v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_);
lean_dec(v_a_5192_);
lean_dec_ref(v_a_5191_);
lean_dec(v_a_5190_);
lean_dec_ref(v_a_5189_);
lean_dec(v_a_5188_);
lean_dec_ref(v_a_5187_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1(){
_start:
{
lean_object* v___f_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
v___f_5203_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabOp___boxed), 9, 0);
v___x_5204_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5205_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_go___closed__5));
v___x_5206_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1));
v___x_5207_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5204_, v___x_5205_, v___x_5206_, v___f_5203_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___boxed(lean_object* v_a_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1();
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3(){
_start:
{
lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
v___x_5236_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp__1___closed__1));
v___x_5237_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___closed__6));
v___x_5238_ = l_Lean_addBuiltinDeclarationRanges(v___x_5236_, v___x_5237_);
return v___x_5238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3___boxed(lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabUnOp___regBuiltin_Lean_Elab_Term_Op_elabUnOp_declRange__3();
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0(lean_object* v_k_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v___x_5249_; 
lean_inc(v___y_5243_);
lean_inc_ref(v___y_5242_);
v___x_5249_ = lean_apply_7(v_k_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, lean_box(0));
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0___boxed(lean_object* v_k_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0(v_k_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(lean_object* v_k_5259_, uint8_t v_allowLevelAssignments_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
lean_object* v___f_5268_; lean_object* v___x_5269_; 
lean_inc(v___y_5262_);
lean_inc_ref(v___y_5261_);
v___f_5268_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5268_, 0, v_k_5259_);
lean_closure_set(v___f_5268_, 1, v___y_5261_);
lean_closure_set(v___f_5268_, 2, v___y_5262_);
v___x_5269_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_5260_, v___f_5268_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
if (lean_obj_tag(v___x_5269_) == 0)
{
return v___x_5269_;
}
else
{
lean_object* v_a_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5277_; 
v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5277_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5277_ == 0)
{
v___x_5272_ = v___x_5269_;
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_a_5270_);
lean_dec(v___x_5269_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5275_; 
if (v_isShared_5273_ == 0)
{
v___x_5275_ = v___x_5272_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_a_5270_);
v___x_5275_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
return v___x_5275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg___boxed(lean_object* v_k_5278_, lean_object* v_allowLevelAssignments_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5287_; lean_object* v_res_5288_; 
v_allowLevelAssignments_boxed_5287_ = lean_unbox(v_allowLevelAssignments_5279_);
v_res_5288_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v_k_5278_, v_allowLevelAssignments_boxed_5287_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0(lean_object* v_00_u03b1_5289_, lean_object* v_k_5290_, uint8_t v_allowLevelAssignments_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_){
_start:
{
lean_object* v___x_5299_; 
v___x_5299_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v_k_5290_, v_allowLevelAssignments_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___boxed(lean_object* v_00_u03b1_5300_, lean_object* v_k_5301_, lean_object* v_allowLevelAssignments_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_5310_; lean_object* v_res_5311_; 
v_allowLevelAssignments_boxed_5310_ = lean_unbox(v_allowLevelAssignments_5302_);
v_res_5311_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0(v_00_u03b1_5300_, v_k_5301_, v_allowLevelAssignments_boxed_5310_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0(lean_object* v_a_5312_, lean_object* v___x_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
lean_object* v___x_5321_; 
v___x_5321_ = l_Lean_Meta_isExprDefEq(v_a_5312_, v___x_5313_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_);
return v___x_5321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0___boxed(lean_object* v_a_5322_, lean_object* v___x_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0(v_a_5322_, v___x_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
lean_dec(v___y_5325_);
lean_dec_ref(v___y_5324_);
return v_res_5331_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0(void){
_start:
{
lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5332_ = lean_box(0);
v___x_5333_ = l_Lean_mkSort(v___x_5332_);
return v___x_5333_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3(void){
_start:
{
lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; 
v___x_5337_ = lean_box(0);
v___x_5338_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__2));
v___x_5339_ = l_Lean_mkConst(v___x_5338_, v___x_5337_);
return v___x_5339_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4(void){
_start:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; 
v___x_5340_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3);
v___x_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5340_);
return v___x_5341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(uint8_t v_noProp_5342_, lean_object* v_e_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_){
_start:
{
if (v_noProp_5342_ == 0)
{
lean_object* v___x_5351_; 
v___x_5351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5351_, 0, v_e_5343_);
return v___x_5351_;
}
else
{
lean_object* v___x_5352_; 
lean_inc(v_a_5349_);
lean_inc_ref(v_a_5348_);
lean_inc(v_a_5347_);
lean_inc_ref(v_a_5346_);
lean_inc_ref(v_e_5343_);
v___x_5352_ = lean_infer_type(v_e_5343_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_);
if (lean_obj_tag(v___x_5352_) == 0)
{
lean_object* v_a_5353_; lean_object* v___x_5354_; lean_object* v___f_5355_; uint8_t v___x_5356_; lean_object* v___x_5357_; 
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
lean_inc(v_a_5353_);
lean_dec_ref_known(v___x_5352_, 1);
v___x_5354_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0);
v___f_5355_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5355_, 0, v_a_5353_);
lean_closure_set(v___f_5355_, 1, v___x_5354_);
v___x_5356_ = 0;
v___x_5357_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v___f_5355_, v___x_5356_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_);
if (lean_obj_tag(v___x_5357_) == 0)
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5369_; 
v_a_5358_ = lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5360_ = v___x_5357_;
v_isShared_5361_ = v_isSharedCheck_5369_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5357_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5369_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
uint8_t v___x_5362_; 
v___x_5362_ = lean_unbox(v_a_5358_);
lean_dec(v_a_5358_);
if (v___x_5362_ == 0)
{
lean_object* v___x_5364_; 
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 0, v_e_5343_);
v___x_5364_ = v___x_5360_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_e_5343_);
v___x_5364_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
return v___x_5364_;
}
}
else
{
lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; 
lean_del_object(v___x_5360_);
v___x_5366_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__4);
v___x_5367_ = lean_box(0);
v___x_5368_ = l_Lean_Elab_Term_ensureHasType(v___x_5366_, v_e_5343_, v___x_5367_, v___x_5367_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_);
return v___x_5368_;
}
}
}
else
{
lean_object* v_a_5370_; lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5377_; 
lean_dec_ref(v_e_5343_);
v_a_5370_ = lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5372_ = v___x_5357_;
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_a_5370_);
lean_dec(v___x_5357_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
lean_object* v___x_5375_; 
if (v_isShared_5373_ == 0)
{
v___x_5375_ = v___x_5372_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_a_5370_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
}
}
else
{
lean_dec_ref(v_e_5343_);
return v___x_5352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___boxed(lean_object* v_noProp_5378_, lean_object* v_e_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_){
_start:
{
uint8_t v_noProp_boxed_5387_; lean_object* v_res_5388_; 
v_noProp_boxed_5387_ = lean_unbox(v_noProp_5378_);
v_res_5388_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_boxed_5387_, v_e_5379_, v_a_5380_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_, v_a_5385_);
lean_dec(v_a_5385_);
lean_dec_ref(v_a_5384_);
lean_dec(v_a_5383_);
lean_dec_ref(v_a_5382_);
lean_dec(v_a_5381_);
lean_dec_ref(v_a_5380_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0(lean_object* v_val_5389_, lean_object* v___x_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_){
_start:
{
lean_object* v___x_5398_; 
v___x_5398_ = l_Lean_Meta_isExprDefEq(v_val_5389_, v___x_5390_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_);
return v___x_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__0___boxed(lean_object* v_val_5399_, lean_object* v___x_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_){
_start:
{
lean_object* v_res_5408_; 
v_res_5408_ = l_Lean_Elab_Term_Op_elabBinRelCore___lam__0(v_val_5399_, v___x_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
lean_dec(v___y_5406_);
lean_dec_ref(v___y_5405_);
lean_dec(v___y_5404_);
lean_dec_ref(v___y_5403_);
lean_dec(v___y_5402_);
lean_dec_ref(v___y_5401_);
return v_res_5408_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2(void){
_start:
{
lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5413_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
v___x_5414_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__2));
v___x_5415_ = l_Lean_Name_append(v___x_5414_, v___x_5413_);
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1(lean_object* v___x_5416_, lean_object* v___x_5417_, lean_object* v_stx_5418_, lean_object* v_val_5419_, uint8_t v_noProp_5420_, lean_object* v___x_5421_, lean_object* v_expectedType_x3f_5422_, uint8_t v___x_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_){
_start:
{
lean_object* v_toCold_5431_; lean_object* v_currRecDepth_5432_; lean_object* v_ref_5433_; uint16_t v_optionFlags_5434_; uint8_t v_suppressElabErrors_5435_; uint8_t v_checkDeprecated_5436_; uint8_t v_isRecordingDeps_5437_; lean_object* v_ref_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; 
v_toCold_5431_ = lean_ctor_get(v___y_5428_, 0);
v_currRecDepth_5432_ = lean_ctor_get(v___y_5428_, 1);
v_ref_5433_ = lean_ctor_get(v___y_5428_, 2);
v_optionFlags_5434_ = lean_ctor_get_uint16(v___y_5428_, sizeof(void*)*3);
v_suppressElabErrors_5435_ = lean_ctor_get_uint8(v___y_5428_, sizeof(void*)*3 + 2);
v_checkDeprecated_5436_ = lean_ctor_get_uint8(v___y_5428_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5437_ = lean_ctor_get_uint8(v___y_5428_, sizeof(void*)*3 + 4);
v_ref_5438_ = l_Lean_replaceRef(v___x_5416_, v_ref_5433_);
lean_inc(v_currRecDepth_5432_);
lean_inc_ref(v_toCold_5431_);
v___x_5439_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5439_, 0, v_toCold_5431_);
lean_ctor_set(v___x_5439_, 1, v_currRecDepth_5432_);
lean_ctor_set(v___x_5439_, 2, v_ref_5438_);
lean_ctor_set_uint16(v___x_5439_, sizeof(void*)*3, v_optionFlags_5434_);
lean_ctor_set_uint8(v___x_5439_, sizeof(void*)*3 + 2, v_suppressElabErrors_5435_);
lean_ctor_set_uint8(v___x_5439_, sizeof(void*)*3 + 3, v_checkDeprecated_5436_);
lean_ctor_set_uint8(v___x_5439_, sizeof(void*)*3 + 4, v_isRecordingDeps_5437_);
lean_inc(v___x_5416_);
v___x_5440_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v___x_5416_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___x_5439_, v___y_5429_);
lean_dec_ref_known(v___x_5439_, 3);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v_a_5441_; lean_object* v_ref_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; 
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
lean_inc(v_a_5441_);
lean_dec_ref_known(v___x_5440_, 1);
v_ref_5442_ = l_Lean_replaceRef(v___x_5417_, v_ref_5433_);
lean_inc(v_currRecDepth_5432_);
lean_inc_ref(v_toCold_5431_);
v___x_5443_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5443_, 0, v_toCold_5431_);
lean_ctor_set(v___x_5443_, 1, v_currRecDepth_5432_);
lean_ctor_set(v___x_5443_, 2, v_ref_5442_);
lean_ctor_set_uint16(v___x_5443_, sizeof(void*)*3, v_optionFlags_5434_);
lean_ctor_set_uint8(v___x_5443_, sizeof(void*)*3 + 2, v_suppressElabErrors_5435_);
lean_ctor_set_uint8(v___x_5443_, sizeof(void*)*3 + 3, v_checkDeprecated_5436_);
lean_ctor_set_uint8(v___x_5443_, sizeof(void*)*3 + 4, v_isRecordingDeps_5437_);
lean_inc(v___x_5417_);
v___x_5444_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree(v___x_5417_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___x_5443_, v___y_5429_);
lean_dec_ref_known(v___x_5443_, 3);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; uint8_t v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___x_5505_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
lean_inc_n(v_a_5445_, 2);
lean_dec_ref_known(v___x_5444_, 1);
v___x_5446_ = 0;
lean_inc(v_a_5441_);
lean_inc_ref(v_val_5419_);
v___x_5447_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_5447_, 0, v_stx_5418_);
lean_ctor_set(v___x_5447_, 1, v_val_5419_);
lean_ctor_set(v___x_5447_, 2, v_a_5441_);
lean_ctor_set(v___x_5447_, 3, v_a_5445_);
lean_ctor_set_uint8(v___x_5447_, sizeof(void*)*4, v___x_5446_);
v___x_5448_ = lean_box(0);
lean_inc_ref(v___x_5447_);
v___x_5505_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze(v___x_5447_, v___x_5448_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
if (lean_obj_tag(v___x_5505_) == 0)
{
lean_object* v_options_5506_; lean_object* v_a_5507_; lean_object* v_inheritedTraceOptions_5508_; uint8_t v_hasTrace_5509_; lean_object* v___x_5510_; uint8_t v___y_5512_; lean_object* v_maxType_5513_; lean_object* v___y_5514_; lean_object* v___y_5515_; lean_object* v___y_5516_; lean_object* v___y_5517_; lean_object* v___y_5518_; lean_object* v___y_5519_; lean_object* v___y_5559_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v___y_5563_; lean_object* v___y_5564_; lean_object* v___y_5584_; lean_object* v___y_5585_; 
v_options_5506_ = lean_ctor_get(v_toCold_5431_, 2);
v_a_5507_ = lean_ctor_get(v___x_5505_, 0);
lean_inc(v_a_5507_);
lean_dec_ref_known(v___x_5505_, 1);
v_inheritedTraceOptions_5508_ = lean_ctor_get(v_toCold_5431_, 11);
v_hasTrace_5509_ = lean_ctor_get_uint8(v_options_5506_, sizeof(void*)*1);
v___x_5510_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
if (v_hasTrace_5509_ == 0)
{
v___y_5559_ = v___y_5424_;
v___y_5560_ = v___y_5425_;
v___y_5561_ = v___y_5426_;
v___y_5562_ = v___y_5427_;
v___y_5563_ = v___y_5428_;
v___y_5564_ = v___y_5429_;
goto v___jp_5558_;
}
else
{
lean_object* v___x_5596_; uint8_t v___x_5597_; 
v___x_5596_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2, &l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2_once, _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2);
v___x_5597_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5508_, v_options_5506_, v___x_5596_);
if (v___x_5597_ == 0)
{
v___y_5559_ = v___y_5424_;
v___y_5560_ = v___y_5425_;
v___y_5561_ = v___y_5426_;
v___y_5562_ = v___y_5427_;
v___y_5563_ = v___y_5428_;
v___y_5564_ = v___y_5429_;
goto v___jp_5558_;
}
else
{
lean_object* v_max_x3f_5598_; uint8_t v_hasUncomparable_5599_; uint8_t v_hasUnknown_5600_; lean_object* v___y_5602_; lean_object* v___y_5603_; lean_object* v___x_5612_; lean_object* v___y_5614_; 
v_max_x3f_5598_ = lean_ctor_get(v_a_5507_, 0);
v_hasUncomparable_5599_ = lean_ctor_get_uint8(v_a_5507_, sizeof(void*)*1);
v_hasUnknown_5600_ = lean_ctor_get_uint8(v_a_5507_, sizeof(void*)*1 + 1);
v___x_5612_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__8);
if (v_hasUncomparable_5599_ == 0)
{
lean_object* v___x_5622_; 
v___x_5622_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_5614_ = v___x_5622_;
goto v___jp_5613_;
}
else
{
lean_object* v___x_5623_; 
v___x_5623_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_5614_ = v___x_5623_;
goto v___jp_5613_;
}
v___jp_5601_:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; 
lean_inc_ref(v___y_5603_);
v___x_5604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5604_, 0, v___y_5603_);
v___x_5605_ = l_Lean_MessageData_ofFormat(v___x_5604_);
v___x_5606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5606_, 0, v___y_5602_);
lean_ctor_set(v___x_5606_, 1, v___x_5605_);
v___x_5607_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__3);
v___x_5608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5608_, 0, v___x_5606_);
lean_ctor_set(v___x_5608_, 1, v___x_5607_);
if (lean_obj_tag(v_max_x3f_5598_) == 0)
{
lean_object* v___x_5609_; 
v___x_5609_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__6);
v___y_5584_ = v___x_5608_;
v___y_5585_ = v___x_5609_;
goto v___jp_5583_;
}
else
{
lean_object* v_val_5610_; lean_object* v___x_5611_; 
v_val_5610_ = lean_ctor_get(v_max_x3f_5598_, 0);
lean_inc(v_val_5610_);
v___x_5611_ = l_Lean_MessageData_ofExpr(v_val_5610_);
v___y_5584_ = v___x_5608_;
v___y_5585_ = v___x_5611_;
goto v___jp_5583_;
}
}
v___jp_5613_:
{
lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; 
lean_inc_ref(v___y_5614_);
v___x_5615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5615_, 0, v___y_5614_);
v___x_5616_ = l_Lean_MessageData_ofFormat(v___x_5615_);
v___x_5617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5617_, 0, v___x_5612_);
lean_ctor_set(v___x_5617_, 1, v___x_5616_);
v___x_5618_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__10);
v___x_5619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5617_);
lean_ctor_set(v___x_5619_, 1, v___x_5618_);
if (v_hasUnknown_5600_ == 0)
{
lean_object* v___x_5620_; 
v___x_5620_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__11));
v___y_5602_ = v___x_5619_;
v___y_5603_ = v___x_5620_;
goto v___jp_5601_;
}
else
{
lean_object* v___x_5621_; 
v___x_5621_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__12));
v___y_5602_ = v___x_5619_;
v___y_5603_ = v___x_5621_;
goto v___jp_5601_;
}
}
}
}
v___jp_5511_:
{
lean_object* v___x_5520_; 
v___x_5520_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe(v___x_5447_, v_maxType_5513_, v___y_5512_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_);
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v_a_5521_; lean_object* v___x_5522_; 
v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
lean_inc(v_a_5521_);
lean_dec_ref_known(v___x_5520_, 1);
v___x_5522_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5521_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_);
if (lean_obj_tag(v___x_5522_) == 0)
{
lean_object* v_toCold_5523_; lean_object* v_options_5524_; uint8_t v_hasTrace_5525_; 
v_toCold_5523_ = lean_ctor_get(v___y_5518_, 0);
v_options_5524_ = lean_ctor_get(v_toCold_5523_, 2);
v_hasTrace_5525_ = lean_ctor_get_uint8(v_options_5524_, sizeof(void*)*1);
if (v_hasTrace_5525_ == 0)
{
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
return v___x_5522_;
}
else
{
lean_object* v_a_5526_; lean_object* v_inheritedTraceOptions_5527_; lean_object* v___x_5528_; uint8_t v___x_5529_; 
v_a_5526_ = lean_ctor_get(v___x_5522_, 0);
v_inheritedTraceOptions_5527_ = lean_ctor_get(v_toCold_5523_, 11);
v___x_5528_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2, &l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2_once, _init_l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__2);
v___x_5529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5527_, v_options_5524_, v___x_5528_);
if (v___x_5529_ == 0)
{
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
return v___x_5522_;
}
else
{
lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
lean_inc_n(v_a_5526_, 2);
lean_dec_ref_known(v___x_5522_, 1);
v___x_5530_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExpr___closed__1);
v___x_5531_ = l_Lean_MessageData_ofExpr(v_a_5526_);
v___x_5532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5530_);
lean_ctor_set(v___x_5532_, 1, v___x_5531_);
v___x_5533_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_5510_, v___x_5532_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
if (lean_obj_tag(v___x_5533_) == 0)
{
lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5540_; 
v_isSharedCheck_5540_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5540_ == 0)
{
lean_object* v_unused_5541_; 
v_unused_5541_ = lean_ctor_get(v___x_5533_, 0);
lean_dec(v_unused_5541_);
v___x_5535_ = v___x_5533_;
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
else
{
lean_dec(v___x_5533_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5538_; 
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 0, v_a_5526_);
v___x_5538_ = v___x_5535_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_a_5526_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
return v___x_5538_;
}
}
}
else
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5549_; 
lean_dec(v_a_5526_);
v_a_5542_ = lean_ctor_get(v___x_5533_, 0);
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5549_ == 0)
{
v___x_5544_ = v___x_5533_;
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v___x_5533_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5547_; 
if (v_isShared_5545_ == 0)
{
v___x_5547_ = v___x_5544_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_a_5542_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
}
}
else
{
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
return v___x_5522_;
}
}
else
{
lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5557_; 
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
v_a_5550_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5557_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5557_ == 0)
{
v___x_5552_ = v___x_5520_;
v_isShared_5553_ = v_isSharedCheck_5557_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_dec(v___x_5520_);
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
v___jp_5558_:
{
uint8_t v_hasUncomparable_5565_; 
v_hasUncomparable_5565_ = lean_ctor_get_uint8(v_a_5507_, sizeof(void*)*1);
if (v_hasUncomparable_5565_ == 0)
{
lean_object* v_max_x3f_5566_; 
v_max_x3f_5566_ = lean_ctor_get(v_a_5507_, 0);
lean_inc(v_max_x3f_5566_);
lean_dec(v_a_5507_);
if (lean_obj_tag(v_max_x3f_5566_) == 0)
{
lean_dec_ref_known(v___x_5447_, 4);
v___y_5450_ = v___y_5563_;
v___y_5451_ = v___y_5562_;
v___y_5452_ = v___y_5560_;
v___y_5453_ = v___y_5559_;
v___y_5454_ = v___y_5561_;
v___y_5455_ = v___y_5564_;
goto v___jp_5449_;
}
else
{
lean_object* v_val_5567_; uint8_t v___x_5568_; 
lean_dec(v_a_5445_);
lean_dec(v_a_5441_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
lean_dec(v___x_5417_);
lean_dec(v___x_5416_);
v_val_5567_ = lean_ctor_get(v_max_x3f_5566_, 0);
lean_inc(v_val_5567_);
lean_dec_ref_known(v_max_x3f_5566_, 1);
v___x_5568_ = 1;
if (v_noProp_5420_ == 0)
{
v___y_5512_ = v___x_5568_;
v_maxType_5513_ = v_val_5567_;
v___y_5514_ = v___y_5559_;
v___y_5515_ = v___y_5560_;
v___y_5516_ = v___y_5561_;
v___y_5517_ = v___y_5562_;
v___y_5518_ = v___y_5563_;
v___y_5519_ = v___y_5564_;
goto v___jp_5511_;
}
else
{
lean_object* v___x_5569_; lean_object* v___f_5570_; lean_object* v___x_5571_; 
v___x_5569_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__0);
lean_inc(v_val_5567_);
v___f_5570_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5570_, 0, v_val_5567_);
lean_closure_set(v___f_5570_, 1, v___x_5569_);
v___x_5571_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary_spec__0___redArg(v___f_5570_, v___x_5423_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
if (lean_obj_tag(v___x_5571_) == 0)
{
lean_object* v_a_5572_; uint8_t v___x_5573_; 
v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
lean_inc(v_a_5572_);
lean_dec_ref_known(v___x_5571_, 1);
v___x_5573_ = lean_unbox(v_a_5572_);
lean_dec(v_a_5572_);
if (v___x_5573_ == 0)
{
v___y_5512_ = v___x_5568_;
v_maxType_5513_ = v_val_5567_;
v___y_5514_ = v___y_5559_;
v___y_5515_ = v___y_5560_;
v___y_5516_ = v___y_5561_;
v___y_5517_ = v___y_5562_;
v___y_5518_ = v___y_5563_;
v___y_5519_ = v___y_5564_;
goto v___jp_5511_;
}
else
{
lean_object* v___x_5574_; 
lean_dec(v_val_5567_);
v___x_5574_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3_once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary___closed__3);
v___y_5512_ = v___x_5568_;
v_maxType_5513_ = v___x_5574_;
v___y_5514_ = v___y_5559_;
v___y_5515_ = v___y_5560_;
v___y_5516_ = v___y_5561_;
v___y_5517_ = v___y_5562_;
v___y_5518_ = v___y_5563_;
v___y_5519_ = v___y_5564_;
goto v___jp_5511_;
}
}
else
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
lean_dec(v_val_5567_);
lean_dec(v___y_5564_);
lean_dec_ref(v___y_5563_);
lean_dec(v___y_5562_);
lean_dec_ref(v___y_5561_);
lean_dec_ref_known(v___x_5447_, 4);
v_a_5575_ = lean_ctor_get(v___x_5571_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5571_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5577_ = v___x_5571_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5571_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5507_);
lean_dec_ref_known(v___x_5447_, 4);
v___y_5450_ = v___y_5563_;
v___y_5451_ = v___y_5562_;
v___y_5452_ = v___y_5560_;
v___y_5453_ = v___y_5559_;
v___y_5454_ = v___y_5561_;
v___y_5455_ = v___y_5564_;
goto v___jp_5449_;
}
}
v___jp_5583_:
{
lean_object* v___x_5586_; lean_object* v___x_5587_; 
v___x_5586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5586_, 0, v___y_5584_);
lean_ctor_set(v___x_5586_, 1, v___y_5585_);
v___x_5587_ = l_Lean_addTrace___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_applyCoe_go_spec__0___redArg(v___x_5510_, v___x_5586_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
if (lean_obj_tag(v___x_5587_) == 0)
{
lean_dec_ref_known(v___x_5587_, 1);
v___y_5559_ = v___y_5424_;
v___y_5560_ = v___y_5425_;
v___y_5561_ = v___y_5426_;
v___y_5562_ = v___y_5427_;
v___y_5563_ = v___y_5428_;
v___y_5564_ = v___y_5429_;
goto v___jp_5558_;
}
else
{
lean_object* v_a_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5595_; 
lean_dec(v_a_5507_);
lean_dec_ref_known(v___x_5447_, 4);
lean_dec(v_a_5445_);
lean_dec(v_a_5441_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
lean_dec(v___x_5417_);
lean_dec(v___x_5416_);
v_a_5588_ = lean_ctor_get(v___x_5587_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5587_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5590_ = v___x_5587_;
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
else
{
lean_inc(v_a_5588_);
lean_dec(v___x_5587_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5593_; 
if (v_isShared_5591_ == 0)
{
v___x_5593_ = v___x_5590_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5588_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
}
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
lean_dec_ref_known(v___x_5447_, 4);
lean_dec(v_a_5445_);
lean_dec(v_a_5441_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
lean_dec(v___x_5417_);
lean_dec(v___x_5416_);
v_a_5624_ = lean_ctor_get(v___x_5505_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5505_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5505_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5505_);
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
v___jp_5449_:
{
lean_object* v___x_5456_; 
v___x_5456_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5441_, v___y_5453_, v___y_5452_, v___y_5454_, v___y_5451_, v___y_5450_, v___y_5455_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_object* v_a_5457_; lean_object* v___x_5458_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc(v_a_5457_);
lean_dec_ref_known(v___x_5456_, 1);
v___x_5458_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toExprCore(v_a_5445_, v___y_5453_, v___y_5452_, v___y_5454_, v___y_5451_, v___y_5450_, v___y_5455_);
if (lean_obj_tag(v___x_5458_) == 0)
{
lean_object* v_a_5459_; lean_object* v_toCold_5460_; lean_object* v_currRecDepth_5461_; lean_object* v_ref_5462_; uint16_t v_optionFlags_5463_; uint8_t v_suppressElabErrors_5464_; uint8_t v_checkDeprecated_5465_; uint8_t v_isRecordingDeps_5466_; lean_object* v_ref_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v_a_5459_ = lean_ctor_get(v___x_5458_, 0);
lean_inc(v_a_5459_);
lean_dec_ref_known(v___x_5458_, 1);
v_toCold_5460_ = lean_ctor_get(v___y_5450_, 0);
v_currRecDepth_5461_ = lean_ctor_get(v___y_5450_, 1);
v_ref_5462_ = lean_ctor_get(v___y_5450_, 2);
v_optionFlags_5463_ = lean_ctor_get_uint16(v___y_5450_, sizeof(void*)*3);
v_suppressElabErrors_5464_ = lean_ctor_get_uint8(v___y_5450_, sizeof(void*)*3 + 2);
v_checkDeprecated_5465_ = lean_ctor_get_uint8(v___y_5450_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5466_ = lean_ctor_get_uint8(v___y_5450_, sizeof(void*)*3 + 4);
v_ref_5467_ = l_Lean_replaceRef(v___x_5416_, v_ref_5462_);
lean_dec(v___x_5416_);
lean_inc(v_currRecDepth_5461_);
lean_inc_ref(v_toCold_5460_);
v___x_5468_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5468_, 0, v_toCold_5460_);
lean_ctor_set(v___x_5468_, 1, v_currRecDepth_5461_);
lean_ctor_set(v___x_5468_, 2, v_ref_5467_);
lean_ctor_set_uint16(v___x_5468_, sizeof(void*)*3, v_optionFlags_5463_);
lean_ctor_set_uint8(v___x_5468_, sizeof(void*)*3 + 2, v_suppressElabErrors_5464_);
lean_ctor_set_uint8(v___x_5468_, sizeof(void*)*3 + 3, v_checkDeprecated_5465_);
lean_ctor_set_uint8(v___x_5468_, sizeof(void*)*3 + 4, v_isRecordingDeps_5466_);
v___x_5469_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_5420_, v_a_5457_, v___y_5453_, v___y_5452_, v___y_5454_, v___y_5451_, v___x_5468_, v___y_5455_);
lean_dec_ref_known(v___x_5468_, 3);
if (lean_obj_tag(v___x_5469_) == 0)
{
lean_object* v_a_5470_; lean_object* v_ref_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; 
v_a_5470_ = lean_ctor_get(v___x_5469_, 0);
lean_inc(v_a_5470_);
lean_dec_ref_known(v___x_5469_, 1);
v_ref_5471_ = l_Lean_replaceRef(v___x_5417_, v_ref_5462_);
lean_dec(v___x_5417_);
lean_inc(v_currRecDepth_5461_);
lean_inc_ref(v_toCold_5460_);
v___x_5472_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5472_, 0, v_toCold_5460_);
lean_ctor_set(v___x_5472_, 1, v_currRecDepth_5461_);
lean_ctor_set(v___x_5472_, 2, v_ref_5471_);
lean_ctor_set_uint16(v___x_5472_, sizeof(void*)*3, v_optionFlags_5463_);
lean_ctor_set_uint8(v___x_5472_, sizeof(void*)*3 + 2, v_suppressElabErrors_5464_);
lean_ctor_set_uint8(v___x_5472_, sizeof(void*)*3 + 3, v_checkDeprecated_5465_);
lean_ctor_set_uint8(v___x_5472_, sizeof(void*)*3 + 4, v_isRecordingDeps_5466_);
v___x_5473_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelCore_toBoolIfNecessary(v_noProp_5420_, v_a_5459_, v___y_5453_, v___y_5452_, v___y_5454_, v___y_5451_, v___x_5472_, v___y_5455_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5504_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5476_ = v___x_5473_;
v_isShared_5477_ = v_isSharedCheck_5504_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5473_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5504_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5478_; 
lean_inc(v___y_5455_);
lean_inc_ref(v___y_5450_);
lean_inc(v___y_5451_);
lean_inc_ref(v___y_5454_);
lean_inc(v_a_5470_);
v___x_5478_ = lean_infer_type(v_a_5470_, v___y_5454_, v___y_5451_, v___y_5450_, v___y_5455_);
if (lean_obj_tag(v___x_5478_) == 0)
{
lean_object* v_a_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5503_; 
v_a_5479_ = lean_ctor_get(v___x_5478_, 0);
v_isSharedCheck_5503_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5503_ == 0)
{
v___x_5481_ = v___x_5478_;
v_isShared_5482_ = v_isSharedCheck_5503_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_a_5479_);
lean_dec(v___x_5478_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5503_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v___x_5484_; 
if (v_isShared_5482_ == 0)
{
lean_ctor_set_tag(v___x_5481_, 1);
v___x_5484_ = v___x_5481_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v_a_5479_);
v___x_5484_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5483_;
}
v_reusejp_5483_:
{
lean_object* v___x_5485_; 
v___x_5485_ = l_Lean_Elab_Term_ensureHasType(v___x_5484_, v_a_5474_, v___x_5448_, v___x_5448_, v___y_5453_, v___y_5452_, v___y_5454_, v___y_5451_, v___x_5472_, v___y_5455_);
lean_dec_ref_known(v___x_5472_, 3);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5501_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5488_ = v___x_5485_;
v_isShared_5489_ = v_isSharedCheck_5501_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_a_5486_);
lean_dec(v___x_5485_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5501_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5490_; lean_object* v___x_5492_; 
v___x_5490_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_mkBinOp___closed__0));
if (v_isShared_5489_ == 0)
{
lean_ctor_set_tag(v___x_5488_, 1);
lean_ctor_set(v___x_5488_, 0, v_a_5470_);
v___x_5492_ = v___x_5488_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5470_);
v___x_5492_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5494_; 
if (v_isShared_5477_ == 0)
{
lean_ctor_set_tag(v___x_5476_, 1);
lean_ctor_set(v___x_5476_, 0, v_a_5486_);
v___x_5494_ = v___x_5476_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5486_);
v___x_5494_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___x_5495_ = lean_mk_empty_array_with_capacity(v___x_5421_);
v___x_5496_ = lean_array_push(v___x_5495_, v___x_5492_);
v___x_5497_ = lean_array_push(v___x_5496_, v___x_5494_);
v___x_5498_ = l_Lean_Elab_Term_elabAppArgs(v_val_5419_, v___x_5490_, v___x_5497_, v_expectedType_x3f_5422_, v___x_5423_, v___x_5423_, v___x_5423_, v___y_5453_, v___y_5452_, v___y_5454_, v___y_5451_, v___y_5450_, v___y_5455_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5450_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5454_);
return v___x_5498_;
}
}
}
}
else
{
lean_del_object(v___x_5476_);
lean_dec(v_a_5470_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
return v___x_5485_;
}
}
}
}
else
{
lean_del_object(v___x_5476_);
lean_dec(v_a_5474_);
lean_dec_ref_known(v___x_5472_, 3);
lean_dec(v_a_5470_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
return v___x_5478_;
}
}
}
else
{
lean_dec_ref_known(v___x_5472_, 3);
lean_dec(v_a_5470_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
return v___x_5473_;
}
}
else
{
lean_dec(v_a_5459_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
lean_dec(v___x_5417_);
return v___x_5469_;
}
}
else
{
lean_dec(v_a_5457_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
lean_dec(v___x_5417_);
lean_dec(v___x_5416_);
return v___x_5458_;
}
}
else
{
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v_a_5445_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
lean_dec(v___x_5417_);
lean_dec(v___x_5416_);
return v___x_5456_;
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec(v_a_5441_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
lean_dec(v_stx_5418_);
lean_dec(v___x_5417_);
lean_dec(v___x_5416_);
v_a_5632_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5444_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5444_);
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
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v_expectedType_x3f_5422_);
lean_dec_ref(v_val_5419_);
lean_dec(v_stx_5418_);
lean_dec(v___x_5417_);
lean_dec(v___x_5416_);
v_a_5640_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5642_ = v___x_5440_;
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_a_5640_);
lean_dec(v___x_5440_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___boxed(lean_object* v___x_5648_, lean_object* v___x_5649_, lean_object* v_stx_5650_, lean_object* v_val_5651_, lean_object* v_noProp_5652_, lean_object* v___x_5653_, lean_object* v_expectedType_x3f_5654_, lean_object* v___x_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_){
_start:
{
uint8_t v_noProp_boxed_5663_; uint8_t v___x_11471__boxed_5664_; lean_object* v_res_5665_; 
v_noProp_boxed_5663_ = lean_unbox(v_noProp_5652_);
v___x_11471__boxed_5664_ = lean_unbox(v___x_5655_);
v_res_5665_ = l_Lean_Elab_Term_Op_elabBinRelCore___lam__1(v___x_5648_, v___x_5649_, v_stx_5650_, v_val_5651_, v_noProp_boxed_5663_, v___x_5653_, v_expectedType_x3f_5654_, v___x_11471__boxed_5664_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
lean_dec(v___x_5653_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore(uint8_t v_noProp_5666_, lean_object* v_stx_5667_, lean_object* v_expectedType_x3f_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_){
_start:
{
lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; uint8_t v___x_5679_; lean_object* v___x_5680_; 
v___x_5676_ = lean_unsigned_to_nat(1u);
v___x_5677_ = l_Lean_Syntax_getArg(v_stx_5667_, v___x_5676_);
v___x_5678_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp___closed__0));
v___x_5679_ = 0;
lean_inc(v___x_5677_);
v___x_5680_ = l_Lean_Elab_Term_resolveId_x3f(v___x_5677_, v___x_5678_, v___x_5679_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_);
if (lean_obj_tag(v___x_5680_) == 0)
{
lean_object* v_a_5681_; 
v_a_5681_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_a_5681_);
lean_dec_ref_known(v___x_5680_, 1);
if (lean_obj_tag(v_a_5681_) == 0)
{
lean_object* v___x_5682_; lean_object* v___x_5683_; 
lean_dec(v_expectedType_x3f_5668_);
lean_dec(v_stx_5667_);
v___x_5682_ = l_Lean_Syntax_getId(v___x_5677_);
v___x_5683_ = l_Lean_throwUnknownConstantAt___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_toTree_processUnOp_spec__2___redArg(v___x_5677_, v___x_5682_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_);
lean_dec(v___x_5677_);
return v___x_5683_;
}
else
{
lean_object* v_val_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___f_5691_; lean_object* v___x_5692_; 
lean_dec(v___x_5677_);
v_val_5684_ = lean_ctor_get(v_a_5681_, 0);
lean_inc(v_val_5684_);
lean_dec_ref_known(v_a_5681_, 1);
v___x_5685_ = lean_unsigned_to_nat(2u);
v___x_5686_ = l_Lean_Syntax_getArg(v_stx_5667_, v___x_5685_);
v___x_5687_ = lean_unsigned_to_nat(3u);
v___x_5688_ = l_Lean_Syntax_getArg(v_stx_5667_, v___x_5687_);
v___x_5689_ = lean_box(v_noProp_5666_);
v___x_5690_ = lean_box(v___x_5679_);
v___f_5691_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___boxed), 15, 8);
lean_closure_set(v___f_5691_, 0, v___x_5686_);
lean_closure_set(v___f_5691_, 1, v___x_5688_);
lean_closure_set(v___f_5691_, 2, v_stx_5667_);
lean_closure_set(v___f_5691_, 3, v_val_5684_);
lean_closure_set(v___f_5691_, 4, v___x_5689_);
lean_closure_set(v___f_5691_, 5, v___x_5685_);
lean_closure_set(v___f_5691_, 6, v_expectedType_x3f_5668_);
lean_closure_set(v___f_5691_, 7, v___x_5690_);
v___x_5692_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_box(0), v___f_5691_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_);
return v___x_5692_;
}
}
else
{
lean_object* v_a_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5700_; 
lean_dec(v___x_5677_);
lean_dec(v_expectedType_x3f_5668_);
lean_dec(v_stx_5667_);
v_a_5693_ = lean_ctor_get(v___x_5680_, 0);
v_isSharedCheck_5700_ = !lean_is_exclusive(v___x_5680_);
if (v_isSharedCheck_5700_ == 0)
{
v___x_5695_ = v___x_5680_;
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
else
{
lean_inc(v_a_5693_);
lean_dec(v___x_5680_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
lean_object* v___x_5698_; 
if (v_isShared_5696_ == 0)
{
v___x_5698_ = v___x_5695_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_a_5693_);
v___x_5698_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
return v___x_5698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelCore___boxed(lean_object* v_noProp_5701_, lean_object* v_stx_5702_, lean_object* v_expectedType_x3f_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_){
_start:
{
uint8_t v_noProp_boxed_5711_; lean_object* v_res_5712_; 
v_noProp_boxed_5711_ = lean_unbox(v_noProp_5701_);
v_res_5712_ = l_Lean_Elab_Term_Op_elabBinRelCore(v_noProp_boxed_5711_, v_stx_5702_, v_expectedType_x3f_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
lean_dec(v_a_5707_);
lean_dec_ref(v_a_5706_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel(lean_object* v_stx_5713_, lean_object* v_expectedType_x3f_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_){
_start:
{
uint8_t v___x_5722_; lean_object* v___x_5723_; 
v___x_5722_ = 0;
v___x_5723_ = l_Lean_Elab_Term_Op_elabBinRelCore(v___x_5722_, v_stx_5713_, v_expectedType_x3f_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_);
return v___x_5723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRel___boxed(lean_object* v_stx_5724_, lean_object* v_expectedType_x3f_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_){
_start:
{
lean_object* v_res_5733_; 
v_res_5733_ = l_Lean_Elab_Term_Op_elabBinRel(v_stx_5724_, v_expectedType_x3f_5725_, v_a_5726_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
lean_dec(v_a_5729_);
lean_dec_ref(v_a_5728_);
lean_dec(v_a_5727_);
lean_dec_ref(v_a_5726_);
return v_res_5733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1(){
_start:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; 
v___x_5747_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5748_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__0));
v___x_5749_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2));
v___x_5750_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRel___boxed), 9, 0);
v___x_5751_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5747_, v___x_5748_, v___x_5749_, v___x_5750_);
return v___x_5751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___boxed(lean_object* v_a_5752_){
_start:
{
lean_object* v_res_5753_; 
v_res_5753_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1();
return v_res_5753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3(){
_start:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; 
v___x_5780_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel__1___closed__2));
v___x_5781_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___closed__6));
v___x_5782_ = l_Lean_addBuiltinDeclarationRanges(v___x_5780_, v___x_5781_);
return v___x_5782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3___boxed(lean_object* v_a_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRel___regBuiltin_Lean_Elab_Term_Op_elabBinRel_declRange__3();
return v_res_5784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp(lean_object* v_stx_5785_, lean_object* v_expectedType_x3f_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_){
_start:
{
uint8_t v___x_5794_; lean_object* v___x_5795_; 
v___x_5794_ = 1;
v___x_5795_ = l_Lean_Elab_Term_Op_elabBinRelCore(v___x_5794_, v_stx_5785_, v_expectedType_x3f_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_);
return v___x_5795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabBinRelNoProp___boxed(lean_object* v_stx_5796_, lean_object* v_expectedType_x3f_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_){
_start:
{
lean_object* v_res_5805_; 
v_res_5805_ = l_Lean_Elab_Term_Op_elabBinRelNoProp(v_stx_5796_, v_expectedType_x3f_5797_, v_a_5798_, v_a_5799_, v_a_5800_, v_a_5801_, v_a_5802_, v_a_5803_);
lean_dec(v_a_5803_);
lean_dec_ref(v_a_5802_);
lean_dec(v_a_5801_);
lean_dec_ref(v_a_5800_);
lean_dec(v_a_5799_);
lean_dec_ref(v_a_5798_);
return v_res_5805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1(){
_start:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; 
v___x_5820_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5821_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__1));
v___x_5822_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3));
v___x_5823_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabBinRelNoProp___boxed), 9, 0);
v___x_5824_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5820_, v___x_5821_, v___x_5822_, v___x_5823_);
return v___x_5824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___boxed(lean_object* v_a_5825_){
_start:
{
lean_object* v_res_5826_; 
v_res_5826_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1();
return v_res_5826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3(){
_start:
{
lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; 
v___x_5853_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp__1___closed__3));
v___x_5854_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___closed__6));
v___x_5855_ = l_Lean_addBuiltinDeclarationRanges(v___x_5853_, v___x_5854_);
return v___x_5855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3___boxed(lean_object* v_a_5856_){
_start:
{
lean_object* v_res_5857_; 
v_res_5857_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabBinRelNoProp___regBuiltin_Lean_Elab_Term_Op_elabBinRelNoProp_declRange__3();
return v_res_5857_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1(void){
_start:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5859_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__0));
v___x_5860_ = l_Lean_stringToMessageData(v___x_5859_);
return v___x_5860_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3(void){
_start:
{
lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5862_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__2));
v___x_5863_ = l_Lean_stringToMessageData(v___x_5862_);
return v___x_5863_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7(void){
_start:
{
lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5868_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__6));
v___x_5869_ = l_Lean_stringToMessageData(v___x_5868_);
return v___x_5869_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11(void){
_start:
{
lean_object* v___x_5874_; lean_object* v___x_5875_; 
v___x_5874_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__10));
v___x_5875_ = l_Lean_stringToMessageData(v___x_5874_);
return v___x_5875_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13(void){
_start:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; 
v___x_5877_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__12));
v___x_5878_ = l_Lean_stringToMessageData(v___x_5877_);
return v___x_5878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty(lean_object* v_stx_5879_, lean_object* v_expectedType_x3f_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_){
_start:
{
lean_object* v___x_5888_; 
lean_inc(v_expectedType_x3f_5880_);
v___x_5888_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
if (lean_obj_tag(v___x_5888_) == 0)
{
lean_dec_ref_known(v___x_5888_, 1);
if (lean_obj_tag(v_expectedType_x3f_5880_) == 0)
{
lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5889_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__1);
v___x_5890_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_5889_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
return v___x_5890_;
}
else
{
lean_object* v_val_5891_; lean_object* v___x_5892_; 
v_val_5891_ = lean_ctor_get(v_expectedType_x3f_5880_, 0);
lean_inc_n(v_val_5891_, 2);
lean_dec_ref_known(v_expectedType_x3f_5880_, 1);
v___x_5892_ = l_Lean_Meta_mkDefault(v_val_5891_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
if (lean_obj_tag(v___x_5892_) == 0)
{
lean_dec(v_val_5891_);
return v___x_5892_;
}
else
{
lean_object* v_a_5893_; uint8_t v___x_5894_; 
v_a_5893_ = lean_ctor_get(v___x_5892_, 0);
v___x_5894_ = l_Lean_Exception_isInterrupt(v_a_5893_);
if (v___x_5894_ == 0)
{
uint8_t v___x_5895_; 
lean_inc(v_a_5893_);
v___x_5895_ = l_Lean_Exception_isRuntime(v_a_5893_);
if (v___x_5895_ == 0)
{
lean_object* v___x_5896_; 
lean_dec_ref_known(v___x_5892_, 1);
lean_inc(v_val_5891_);
v___x_5896_ = l_Lean_Meta_mkOfNonempty(v_val_5891_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
if (lean_obj_tag(v___x_5896_) == 0)
{
lean_dec(v_val_5891_);
return v___x_5896_;
}
else
{
lean_object* v_a_5897_; uint8_t v___x_5898_; 
v_a_5897_ = lean_ctor_get(v___x_5896_, 0);
v___x_5898_ = l_Lean_Exception_isInterrupt(v_a_5897_);
if (v___x_5898_ == 0)
{
uint8_t v___x_5899_; 
lean_inc(v_a_5897_);
v___x_5899_ = l_Lean_Exception_isRuntime(v_a_5897_);
if (v___x_5899_ == 0)
{
lean_object* v___x_5900_; lean_object* v___x_5901_; uint8_t v___x_5902_; 
lean_dec_ref_known(v___x_5896_, 1);
v___x_5900_ = lean_unsigned_to_nat(1u);
v___x_5901_ = l_Lean_Syntax_getArg(v_stx_5879_, v___x_5900_);
v___x_5902_ = l_Lean_Syntax_isNone(v___x_5901_);
lean_dec(v___x_5901_);
if (v___x_5902_ == 0)
{
uint8_t v___x_5903_; lean_object* v___x_5904_; 
v___x_5903_ = 1;
v___x_5904_ = l_Lean_Meta_mkLabeledSorry(v_val_5891_, v___x_5902_, v___x_5903_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
return v___x_5904_;
}
else
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; 
v___x_5905_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__3);
v___x_5906_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__5));
v___x_5907_ = l_Lean_MessageData_ofConstName(v___x_5906_, v___x_5899_);
v___x_5908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5905_);
lean_ctor_set(v___x_5908_, 1, v___x_5907_);
v___x_5909_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__7);
v___x_5910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5908_);
lean_ctor_set(v___x_5910_, 1, v___x_5909_);
v___x_5911_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__9));
v___x_5912_ = l_Lean_MessageData_ofConstName(v___x_5911_, v___x_5899_);
v___x_5913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5910_);
lean_ctor_set(v___x_5913_, 1, v___x_5912_);
v___x_5914_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__11);
v___x_5915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5913_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = l_Lean_indentExpr(v_val_5891_);
v___x_5917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5915_);
lean_ctor_set(v___x_5917_, 1, v___x_5916_);
v___x_5918_ = lean_obj_once(&l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13, &l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13_once, _init_l_Lean_Elab_Term_Op_elabDefaultOrNonempty___closed__13);
v___x_5919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5917_);
lean_ctor_set(v___x_5919_, 1, v___x_5918_);
v___x_5920_ = l_Lean_throwError___at___00__private_Lean_Elab_Extra_0__Lean_Elab_Term_getMonadForIn_spec__0___redArg(v___x_5919_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
return v___x_5920_;
}
}
else
{
lean_dec(v_val_5891_);
return v___x_5896_;
}
}
else
{
lean_dec(v_val_5891_);
return v___x_5896_;
}
}
}
else
{
lean_dec(v_val_5891_);
return v___x_5892_;
}
}
else
{
lean_dec(v_val_5891_);
return v___x_5892_;
}
}
}
}
else
{
lean_object* v_a_5921_; lean_object* v___x_5923_; uint8_t v_isShared_5924_; uint8_t v_isSharedCheck_5928_; 
lean_dec(v_expectedType_x3f_5880_);
v_a_5921_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5928_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5928_ == 0)
{
v___x_5923_ = v___x_5888_;
v_isShared_5924_ = v_isSharedCheck_5928_;
goto v_resetjp_5922_;
}
else
{
lean_inc(v_a_5921_);
lean_dec(v___x_5888_);
v___x_5923_ = lean_box(0);
v_isShared_5924_ = v_isSharedCheck_5928_;
goto v_resetjp_5922_;
}
v_resetjp_5922_:
{
lean_object* v___x_5926_; 
if (v_isShared_5924_ == 0)
{
v___x_5926_ = v___x_5923_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5927_; 
v_reuseFailAlloc_5927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_a_5921_);
v___x_5926_ = v_reuseFailAlloc_5927_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
return v___x_5926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Op_elabDefaultOrNonempty___boxed(lean_object* v_stx_5929_, lean_object* v_expectedType_x3f_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_){
_start:
{
lean_object* v_res_5938_; 
v_res_5938_ = l_Lean_Elab_Term_Op_elabDefaultOrNonempty(v_stx_5929_, v_expectedType_x3f_5930_, v_a_5931_, v_a_5932_, v_a_5933_, v_a_5934_, v_a_5935_, v_a_5936_);
lean_dec(v_a_5936_);
lean_dec_ref(v_a_5935_);
lean_dec(v_a_5934_);
lean_dec_ref(v_a_5933_);
lean_dec(v_a_5932_);
lean_dec_ref(v_a_5931_);
lean_dec(v_stx_5929_);
return v_res_5938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1(){
_start:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5953_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5954_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__1));
v___x_5955_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3));
v___x_5956_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_Op_elabDefaultOrNonempty___boxed), 9, 0);
v___x_5957_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5953_, v___x_5954_, v___x_5955_, v___x_5956_);
return v___x_5957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___boxed(lean_object* v_a_5958_){
_start:
{
lean_object* v_res_5959_; 
v_res_5959_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1();
return v_res_5959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3(){
_start:
{
lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; 
v___x_5986_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty__1___closed__3));
v___x_5987_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___closed__6));
v___x_5988_ = l_Lean_addBuiltinDeclarationRanges(v___x_5986_, v___x_5987_);
return v___x_5988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3___boxed(lean_object* v_a_5989_){
_start:
{
lean_object* v_res_5990_; 
v_res_5990_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_elabDefaultOrNonempty___regBuiltin_Lean_Elab_Term_Op_elabDefaultOrNonempty_declRange__3();
return v_res_5990_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v___x_6037_ = lean_unsigned_to_nat(2859506122u);
v___x_6038_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__17_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_6039_ = l_Lean_Name_num___override(v___x_6038_, v___x_6037_);
return v___x_6039_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; 
v___x_6041_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__19_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_6042_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__18_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_6043_ = l_Lean_Name_str___override(v___x_6042_, v___x_6041_);
return v___x_6043_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v___x_6045_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__21_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_));
v___x_6046_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__20_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_6047_ = l_Lean_Name_str___override(v___x_6046_, v___x_6045_);
return v___x_6047_;
}
}
static lean_object* _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; 
v___x_6048_ = lean_unsigned_to_nat(2u);
v___x_6049_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__22_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_6050_ = l_Lean_Name_num___override(v___x_6049_, v___x_6048_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6052_; uint8_t v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; 
v___x_6052_ = ((lean_object*)(l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_analyze_go___closed__0));
v___x_6053_ = 0;
v___x_6054_ = lean_obj_once(&l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_, &l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn___closed__23_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_);
v___x_6055_ = l_Lean_registerTraceClass(v___x_6052_, v___x_6053_, v___x_6054_);
if (lean_obj_tag(v___x_6055_) == 0)
{
lean_object* v___x_6056_; lean_object* v___x_6057_; 
lean_dec_ref_known(v___x_6055_, 1);
v___x_6056_ = ((lean_object*)(l_Lean_Elab_Term_Op_elabBinRelCore___lam__1___closed__1));
v___x_6057_ = l_Lean_registerTraceClass(v___x_6056_, v___x_6053_, v___x_6054_);
return v___x_6057_;
}
else
{
return v___x_6055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2____boxed(lean_object* v_a_6058_){
_start:
{
lean_object* v_res_6059_; 
v_res_6059_ = l___private_Lean_Elab_Extra_0__Lean_Elab_Term_Op_initFn_00___x40_Lean_Elab_Extra_2859506122____hygCtx___hyg_2_();
return v_res_6059_;
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
