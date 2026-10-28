// Lean compiler output
// Module: Lean.Elab.Calc
// Imports: public import Lean.Elab.App
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_useDiagnosticMsg;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unexpected relation type"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkCalcTrans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Trans"};
static const lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcTrans___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 87, 41, 87, 171, 69, 129)}};
static const lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcTrans___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcTrans___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 87, 41, 87, 171, 69, 129)}};
static const lean_ctor_object l_Lean_Elab_Term_mkCalcTrans___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 62, 79, 217, 45, 238, 227, 16)}};
static const lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__3 = (const lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__3_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcTrans___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "invalid 'calc' step, step result is not a relation"};
static const lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__4 = (const lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Term_mkCalcTrans___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__5;
static const lean_string_object l_Lean_Elab_Term_mkCalcTrans___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "invalid 'calc' step, failed to synthesize `Trans` instance"};
static const lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__6 = (const lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Term_mkCalcTrans___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__7;
static const lean_string_object l_Lean_Elab_Term_mkCalcTrans___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Elab.Calc"};
static const lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__8 = (const lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__8_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcTrans___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Elab.Term.mkCalcTrans"};
static const lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__9 = (const lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__9_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcTrans___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__10 = (const lean_object*)&l_Lean_Elab_Term_mkCalcTrans___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Term_mkCalcTrans___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__11;
static lean_once_cell_t l_Lean_Elab_Term_mkCalcTrans___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_mkCalcTrans___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15_value),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19_value)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instInhabitedCalcStepView_default = (const lean_object*)&l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instInhabitedCalcStepView = (const lean_object*)&l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "calcFirstStep"};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 79, 246, 49, 58, 153, 94, 105)}};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__3 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__4 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__5 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__6 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__6_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__7 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__8;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__9 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__10 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__11 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "calcStep"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 3, 210, 123, 188, 211, 75, 180)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkCalcStepViews___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "calcSteps"};
static const lean_object* l_Lean_Elab_Term_mkCalcStepViews___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkCalcStepViews___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcStepViews___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_mkCalcStepViews___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcStepViews___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_mkCalcStepViews___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 10, 254, 10, 206, 238, 242, 161)}};
static const lean_object* l_Lean_Elab_Term_mkCalcStepViews___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkCalcStepViews___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "invalid 'calc' step, left-hand side is"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\nbut previous right-hand side is"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "invalid 'calc' step, relation expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_elabCalcSteps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabCalcSteps___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_elabCalcSteps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabCalcSteps___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_elabCalcSteps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__2 = (const lean_object*)&l_Lean_Elab_Term_elabCalcSteps___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_elabCalcSteps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__3 = (const lean_object*)&l_Lean_Elab_Term_elabCalcSteps___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Term_elabCalcSteps___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_elabCalcSteps___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "'calc' expression"};
static const lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "invalid 'calc' step, right-hand side is"};
static const lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\nbut is expected to be"};
static const lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7;
static const lean_string_object l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Term.throwCalcFailure"};
static const lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_elabCalc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "calc"};
static const lean_object* l_Lean_Elab_Term_elabCalc___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabCalc___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_elabCalc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 46, 171, 201, 40, 237, 174, 33)}};
static const lean_object* l_Lean_Elab_Term_elabCalc___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabCalc"};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 61, 75, 63, 20, 229, 120, 81)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Elaborator for the `calc` term mode variant."};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(116) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(121) << 1) | 1)),((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value),((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(116) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(116) << 1) | 1)),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg(lean_object* v_e_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_3_ = l_Lean_Expr_getAppNumArgs(v_e_1_);
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_dec_lt(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_6_ = l_Lean_Expr_appFn_x21(v_e_1_);
v___x_7_ = l_Lean_Expr_appFn_x21(v___x_6_);
v___x_8_ = l_Lean_Expr_appArg_x21(v___x_6_);
lean_dec_ref(v___x_6_);
v___x_9_ = l_Lean_Expr_appArg_x21(v_e_1_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_8_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_7_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
v___x_12_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
else
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_box(0);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg___boxed(lean_object* v_e_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_e_16_);
lean_dec_ref(v_e_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f(lean_object* v_e_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_e_19_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___boxed(lean_object* v_e_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_Term_getCalcRelation_x3f(v_e_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec_ref(v_e_26_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(lean_object* v_k_33_, lean_object* v_b_34_, lean_object* v_c_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
lean_inc(v___y_39_);
lean_inc_ref(v___y_38_);
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
v___x_41_ = lean_apply_7(v_k_33_, v_b_34_, v_c_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, lean_box(0));
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed(lean_object* v_k_42_, lean_object* v_b_43_, lean_object* v_c_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(v_k_42_, v_b_43_, v_c_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(lean_object* v_type_51_, lean_object* v_k_52_, uint8_t v_cleanupAnnotations_53_, uint8_t v_whnfType_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___f_60_; lean_object* v___x_61_; 
v___f_60_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_60_, 0, v_k_52_);
v___x_61_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_51_, v___f_60_, v_cleanupAnnotations_53_, v_whnfType_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
else
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_77_; 
v_a_70_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_77_ == 0)
{
v___x_72_ = v___x_61_;
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_61_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_a_70_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___boxed(lean_object* v_type_78_, lean_object* v_k_79_, lean_object* v_cleanupAnnotations_80_, lean_object* v_whnfType_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_87_; uint8_t v_whnfType_boxed_88_; lean_object* v_res_89_; 
v_cleanupAnnotations_boxed_87_ = lean_unbox(v_cleanupAnnotations_80_);
v_whnfType_boxed_88_ = lean_unbox(v_whnfType_81_);
v_res_89_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_type_78_, v_k_79_, v_cleanupAnnotations_boxed_87_, v_whnfType_boxed_88_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(lean_object* v_00_u03b1_90_, lean_object* v_type_91_, lean_object* v_k_92_, uint8_t v_cleanupAnnotations_93_, uint8_t v_whnfType_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_type_91_, v_k_92_, v_cleanupAnnotations_93_, v_whnfType_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___boxed(lean_object* v_00_u03b1_101_, lean_object* v_type_102_, lean_object* v_k_103_, lean_object* v_cleanupAnnotations_104_, lean_object* v_whnfType_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_111_; uint8_t v_whnfType_boxed_112_; lean_object* v_res_113_; 
v_cleanupAnnotations_boxed_111_ = lean_unbox(v_cleanupAnnotations_104_);
v_whnfType_boxed_112_ = lean_unbox(v_whnfType_105_);
v_res_113_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(v_00_u03b1_101_, v_type_102_, v_k_103_, v_cleanupAnnotations_boxed_111_, v_whnfType_boxed_112_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(lean_object* v_msgData_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___x_120_; lean_object* v_env_121_; uint8_t v___x_122_; lean_object* v_env_123_; lean_object* v___x_124_; lean_object* v_toCold_125_; lean_object* v_mctx_126_; lean_object* v_lctx_127_; lean_object* v_options_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_120_ = lean_st_ref_get(v___y_118_);
v_env_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc_ref(v_env_121_);
lean_dec(v___x_120_);
v___x_122_ = 0;
v_env_123_ = l_Lean_Environment_setRecordingDeps(v_env_121_, v___x_122_);
v___x_124_ = lean_st_ref_get(v___y_116_);
v_toCold_125_ = lean_ctor_get(v___y_117_, 0);
v_mctx_126_ = lean_ctor_get(v___x_124_, 0);
lean_inc_ref(v_mctx_126_);
lean_dec(v___x_124_);
v_lctx_127_ = lean_ctor_get(v___y_115_, 2);
v_options_128_ = lean_ctor_get(v_toCold_125_, 2);
lean_inc_ref(v_options_128_);
lean_inc_ref(v_lctx_127_);
v___x_129_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_129_, 0, v_env_123_);
lean_ctor_set(v___x_129_, 1, v_mctx_126_);
lean_ctor_set(v___x_129_, 2, v_lctx_127_);
lean_ctor_set(v___x_129_, 3, v_options_128_);
v___x_130_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v_msgData_114_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0___boxed(lean_object* v_msgData_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msgData_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_ref_145_; lean_object* v___x_146_; lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_ref_145_ = lean_ctor_get(v___y_142_, 2);
v___x_146_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_155_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
lean_inc(v_ref_145_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v_ref_145_);
lean_ctor_set(v___x_151_, 1, v_a_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set_tag(v___x_149_, 1);
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg___boxed(lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_162_;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0));
v___x_165_ = l_Lean_stringToMessageData(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(lean_object* v_a_166_, lean_object* v_x_167_, lean_object* v_sort_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; 
lean_inc(v___y_172_);
lean_inc_ref(v___y_171_);
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
v___x_174_ = lean_whnf(v_sort_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_187_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_187_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_187_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_187_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
if (lean_obj_tag(v_a_175_) == 3)
{
lean_object* v_u_179_; lean_object* v___x_181_; 
lean_dec_ref(v_a_166_);
v_u_179_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_u_179_);
lean_dec_ref_known(v_a_175_, 1);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v_u_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_u_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_del_object(v___x_177_);
lean_dec(v_a_175_);
v___x_183_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1);
v___x_184_ = l_Lean_indentExpr(v_a_166_);
v___x_185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_185_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
return v___x_186_;
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec_ref(v_a_166_);
v_a_188_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_174_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_174_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed(lean_object* v_a_196_, lean_object* v_x_197_, lean_object* v_sort_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(v_a_196_, v_x_197_, v_sort_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec_ref(v_x_197_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(lean_object* v_r_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; 
lean_inc(v_a_209_);
lean_inc_ref(v_a_208_);
lean_inc(v_a_207_);
lean_inc_ref(v_a_206_);
v___x_211_ = lean_infer_type(v_r_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___f_213_; uint8_t v___x_214_; lean_object* v___x_215_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_n(v_a_212_, 2);
lean_dec_ref_known(v___x_211_, 1);
v___f_213_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed), 8, 1);
lean_closure_set(v___f_213_, 0, v_a_212_);
v___x_214_ = 0;
v___x_215_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_a_212_, v___f_213_, v___x_214_, v___x_214_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
return v___x_215_;
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_a_216_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_211_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_211_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___boxed(lean_object* v_r_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_r_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(lean_object* v_00_u03b1_231_, lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___boxed(lean_object* v_00_u03b1_239_, lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(v_00_u03b1_239_, v_msg_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(lean_object* v_e_247_, lean_object* v___y_248_){
_start:
{
uint8_t v___x_250_; 
v___x_250_ = l_Lean_Expr_hasMVar(v_e_247_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v_e_247_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v_mctx_253_; lean_object* v___x_254_; lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v___x_257_; lean_object* v_cache_258_; lean_object* v_zetaDeltaFVarIds_259_; lean_object* v_postponed_260_; lean_object* v_diag_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_270_; 
v___x_252_ = lean_st_ref_get(v___y_248_);
v_mctx_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc_ref(v_mctx_253_);
lean_dec(v___x_252_);
v___x_254_ = l_Lean_instantiateMVarsCore(v_mctx_253_, v_e_247_);
v_fst_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_fst_255_);
v_snd_256_ = lean_ctor_get(v___x_254_, 1);
lean_inc(v_snd_256_);
lean_dec_ref(v___x_254_);
v___x_257_ = lean_st_ref_take(v___y_248_);
v_cache_258_ = lean_ctor_get(v___x_257_, 1);
v_zetaDeltaFVarIds_259_ = lean_ctor_get(v___x_257_, 2);
v_postponed_260_ = lean_ctor_get(v___x_257_, 3);
v_diag_261_ = lean_ctor_get(v___x_257_, 4);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v___x_257_, 0);
lean_dec(v_unused_271_);
v___x_263_ = v___x_257_;
v_isShared_264_ = v_isSharedCheck_270_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_diag_261_);
lean_inc(v_postponed_260_);
lean_inc(v_zetaDeltaFVarIds_259_);
lean_inc(v_cache_258_);
lean_dec(v___x_257_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_270_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v_snd_256_);
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_snd_256_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_cache_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_zetaDeltaFVarIds_259_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_postponed_260_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_diag_261_);
v___x_266_ = v_reuseFailAlloc_269_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_st_ref_put(v___y_248_, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v_fst_255_);
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg___boxed(lean_object* v_e_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_e_272_, v___y_273_);
lean_dec(v___y_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(lean_object* v_e_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_e_276_, v___y_278_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___boxed(lean_object* v_e_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(v_e_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(lean_object* v_msg_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___f_297_; lean_object* v___x_7150__overap_298_; lean_object* v___x_299_; 
v___f_297_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_7150__overap_298_ = lean_panic_fn_borrowed(v___f_297_, v_msg_291_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
v___x_299_ = lean_apply_5(v___x_7150__overap_298_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, lean_box(0));
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___boxed(lean_object* v_msg_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v_msg_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__5(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__4));
v___x_316_ = l_Lean_stringToMessageData(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__7(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__6));
v___x_319_ = l_Lean_stringToMessageData(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__11(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_324_ = lean_unsigned_to_nat(72u);
v___x_325_ = lean_unsigned_to_nat(35u);
v___x_326_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__9));
v___x_327_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_328_ = l_mkPanicMessageWithDecl(v___x_327_, v___x_326_, v___x_325_, v___x_324_, v___x_323_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__12(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_329_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_330_ = lean_unsigned_to_nat(53u);
v___x_331_ = lean_unsigned_to_nat(34u);
v___x_332_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__9));
v___x_333_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_334_ = l_mkPanicMessageWithDecl(v___x_333_, v___x_332_, v___x_331_, v___x_330_, v___x_329_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object* v_result_335_, lean_object* v_resultType_336_, lean_object* v_step_337_, lean_object* v_stepType_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_344_; lean_object* v_a_345_; 
v___x_344_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_resultType_336_);
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref(v___x_344_);
if (lean_obj_tag(v_a_345_) == 1)
{
lean_object* v_val_346_; lean_object* v_snd_347_; lean_object* v_fst_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_604_; 
v_val_346_ = lean_ctor_get(v_a_345_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v_a_345_, 1);
v_snd_347_ = lean_ctor_get(v_val_346_, 1);
v_fst_348_ = lean_ctor_get(v_val_346_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v_val_346_);
if (v_isSharedCheck_604_ == 0)
{
v___x_350_ = v_val_346_;
v_isShared_351_ = v_isSharedCheck_604_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_snd_347_);
lean_inc(v_fst_348_);
lean_dec(v_val_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_604_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v_fst_352_; lean_object* v_snd_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_603_; 
v_fst_352_ = lean_ctor_get(v_snd_347_, 0);
v_snd_353_ = lean_ctor_get(v_snd_347_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_snd_347_);
if (v_isSharedCheck_603_ == 0)
{
v___x_355_ = v_snd_347_;
v_isShared_356_ = v_isSharedCheck_603_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_snd_353_);
lean_inc(v_fst_352_);
lean_dec(v_snd_347_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_603_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v_a_360_; 
v___x_357_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_stepType_338_, v_a_340_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
v___x_359_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_358_);
lean_dec(v_a_358_);
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref(v___x_359_);
if (lean_obj_tag(v_a_360_) == 1)
{
lean_object* v_val_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_600_; 
v_val_361_ = lean_ctor_get(v_a_360_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_a_360_);
if (v_isSharedCheck_600_ == 0)
{
v___x_363_ = v_a_360_;
v_isShared_364_ = v_isSharedCheck_600_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_val_361_);
lean_dec(v_a_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_600_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v_snd_365_; lean_object* v_fst_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_599_; 
v_snd_365_ = lean_ctor_get(v_val_361_, 1);
v_fst_366_ = lean_ctor_get(v_val_361_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_val_361_);
if (v_isSharedCheck_599_ == 0)
{
v___x_368_ = v_val_361_;
v_isShared_369_ = v_isSharedCheck_599_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snd_365_);
lean_inc(v_fst_366_);
lean_dec(v_val_361_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_599_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_snd_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_597_; 
v_snd_370_ = lean_ctor_get(v_snd_365_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_snd_365_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v_snd_365_, 0);
lean_dec(v_unused_598_);
v___x_372_ = v_snd_365_;
v_isShared_373_ = v_isSharedCheck_597_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_snd_370_);
lean_dec(v_snd_365_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_597_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; 
lean_inc(v_fst_348_);
v___x_374_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_fst_348_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
lean_inc(v_fst_366_);
v___x_376_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_fst_366_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
lean_inc(v_a_342_);
lean_inc_ref(v_a_341_);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
lean_inc(v_fst_352_);
v___x_378_ = lean_infer_type(v_fst_352_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_378_, 1);
lean_inc(v_a_342_);
lean_inc_ref(v_a_341_);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
lean_inc(v_snd_353_);
v___x_380_ = lean_infer_type(v_snd_353_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
lean_inc(v_a_342_);
lean_inc_ref(v_a_341_);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
lean_inc(v_snd_370_);
v___x_382_ = lean_infer_type(v_snd_370_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
lean_inc(v_a_379_);
v___x_384_ = l_Lean_Meta_getLevel(v_a_379_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
lean_inc(v_a_381_);
v___x_386_ = l_Lean_Meta_getLevel(v_a_381_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
lean_inc(v_a_383_);
v___x_388_ = l_Lean_Meta_getLevel(v_a_383_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = l_Lean_Meta_mkFreshLevelMVar(v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc_n(v_a_391_, 2);
lean_dec_ref_known(v___x_390_, 1);
v___x_392_ = l_Lean_mkSort(v_a_391_);
lean_inc(v_a_383_);
v___x_393_ = l_Lean_mkArrow(v_a_383_, v___x_392_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_395_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
lean_inc(v_a_379_);
v___x_395_ = l_Lean_mkArrow(v_a_379_, v_a_394_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v_a_396_);
v___x_398_ = v___x_363_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_396_);
v___x_398_ = v_reuseFailAlloc_508_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = 0;
v___x_400_ = lean_box(0);
v___x_401_ = l_Lean_Meta_mkFreshExprMVar(v___x_398_, v___x_399_, v___x_400_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__1));
v___x_404_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 1);
lean_ctor_set(v___x_368_, 1, v___x_404_);
lean_ctor_set(v___x_368_, 0, v_a_389_);
v___x_406_ = v___x_368_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_389_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_499_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 1);
lean_ctor_set(v___x_355_, 1, v___x_406_);
lean_ctor_set(v___x_355_, 0, v_a_387_);
v___x_408_ = v___x_355_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_387_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_498_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_410_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 1);
lean_ctor_set(v___x_350_, 1, v___x_408_);
lean_ctor_set(v___x_350_, 0, v_a_385_);
v___x_410_ = v___x_350_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_385_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_497_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v_a_391_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_412_, 0, v_a_377_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v_a_375_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_inc_ref(v___x_413_);
v___x_414_ = l_Lean_mkConst(v___x_403_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(6u);
v___x_416_ = lean_mk_empty_array_with_capacity(v___x_415_);
lean_inc(v_a_379_);
v___x_417_ = lean_array_push(v___x_416_, v_a_379_);
lean_inc(v_a_381_);
v___x_418_ = lean_array_push(v___x_417_, v_a_381_);
lean_inc(v_a_383_);
v___x_419_ = lean_array_push(v___x_418_, v_a_383_);
lean_inc(v_fst_348_);
v___x_420_ = lean_array_push(v___x_419_, v_fst_348_);
lean_inc(v_fst_366_);
v___x_421_ = lean_array_push(v___x_420_, v_fst_366_);
lean_inc(v_a_402_);
v___x_422_ = lean_array_push(v___x_421_, v_a_402_);
v___x_423_ = l_Lean_mkAppN(v___x_414_, v___x_422_);
lean_dec_ref(v___x_422_);
v___x_424_ = lean_box(0);
lean_inc_ref(v___x_423_);
v___x_425_ = l_Lean_Meta_trySynthInstance(v___x_423_, v___x_424_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
if (lean_obj_tag(v_a_426_) == 1)
{
lean_object* v_a_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec_ref(v___x_423_);
v_a_427_ = lean_ctor_get(v_a_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v_a_426_, 1);
v___x_428_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__3));
v___x_429_ = l_Lean_mkConst(v___x_428_, v___x_413_);
v___x_430_ = lean_unsigned_to_nat(12u);
v___x_431_ = lean_mk_empty_array_with_capacity(v___x_430_);
v___x_432_ = lean_array_push(v___x_431_, v_a_379_);
v___x_433_ = lean_array_push(v___x_432_, v_a_381_);
v___x_434_ = lean_array_push(v___x_433_, v_a_383_);
v___x_435_ = lean_array_push(v___x_434_, v_fst_348_);
v___x_436_ = lean_array_push(v___x_435_, v_fst_366_);
v___x_437_ = lean_array_push(v___x_436_, v_a_402_);
v___x_438_ = lean_array_push(v___x_437_, v_a_427_);
v___x_439_ = lean_array_push(v___x_438_, v_fst_352_);
v___x_440_ = lean_array_push(v___x_439_, v_snd_353_);
v___x_441_ = lean_array_push(v___x_440_, v_snd_370_);
v___x_442_ = lean_array_push(v___x_441_, v_result_335_);
v___x_443_ = lean_array_push(v___x_442_, v_step_337_);
v___x_444_ = l_Lean_mkAppN(v___x_429_, v___x_443_);
lean_dec_ref(v___x_443_);
lean_inc(v_a_342_);
lean_inc_ref(v_a_341_);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
lean_inc_ref(v___x_444_);
v___x_445_ = lean_infer_type(v___x_444_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_474_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
v___x_447_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_446_, v_a_340_);
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_474_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_474_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_474_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_460_; lean_object* v_a_461_; 
v___x_452_ = l_Lean_Expr_headBeta(v_a_448_);
v___x_460_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_452_);
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref(v___x_460_);
if (lean_obj_tag(v_a_461_) == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_del_object(v___x_450_);
lean_dec_ref(v___x_444_);
lean_del_object(v___x_372_);
v___x_462_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__5, &l_Lean_Elab_Term_mkCalcTrans___closed__5_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__5);
v___x_463_ = l_Lean_indentExpr(v___x_452_);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_464_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
else
{
lean_dec_ref_known(v_a_461_, 1);
goto v___jp_453_;
}
v___jp_453_:
{
lean_object* v___x_455_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___x_452_);
lean_ctor_set(v___x_372_, 0, v___x_444_);
v___x_455_ = v___x_372_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_452_);
v___x_455_ = v_reuseFailAlloc_459_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_455_);
v___x_457_ = v___x_450_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v___x_444_);
lean_del_object(v___x_372_);
v_a_475_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_445_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_445_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v_a_426_);
lean_dec_ref_known(v___x_413_, 2);
lean_dec(v_a_402_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_dec(v_fst_366_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v___x_483_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__7, &l_Lean_Elab_Term_mkCalcTrans___closed__7_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__7);
v___x_484_ = l_Lean_indentExpr(v___x_423_);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_useDiagnosticMsg;
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_487_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
return v___x_488_;
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec_ref(v___x_423_);
lean_dec_ref_known(v___x_413_, 2);
lean_dec(v_a_402_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_dec(v_fst_366_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_489_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_425_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_425_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v_a_391_);
lean_dec(v_a_389_);
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_500_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_401_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_401_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_a_391_);
lean_dec(v_a_389_);
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_509_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_395_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_395_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v_a_391_);
lean_dec(v_a_389_);
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_517_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_393_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_393_);
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
lean_dec(v_a_389_);
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_525_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_390_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_390_);
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
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_533_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_388_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_388_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_541_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_386_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_386_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_549_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_384_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_384_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_557_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_382_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_382_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_565_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_380_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_380_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_573_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_378_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_378_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_581_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_376_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_376_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_del_object(v___x_372_);
lean_dec(v_snd_370_);
lean_del_object(v___x_368_);
lean_dec(v_fst_366_);
lean_del_object(v___x_363_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v_a_589_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_374_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_374_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_a_360_);
lean_del_object(v___x_355_);
lean_dec(v_snd_353_);
lean_dec(v_fst_352_);
lean_del_object(v___x_350_);
lean_dec(v_fst_348_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v___x_601_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__11, &l_Lean_Elab_Term_mkCalcTrans___closed__11_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__11);
v___x_602_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v___x_601_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
return v___x_602_;
}
}
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_a_345_);
lean_dec_ref(v_stepType_338_);
lean_dec_ref(v_step_337_);
lean_dec_ref(v_result_335_);
v___x_605_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__12, &l_Lean_Elab_Term_mkCalcTrans___closed__12_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__12);
v___x_606_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v___x_605_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___boxed(lean_object* v_result_607_, lean_object* v_resultType_608_, lean_object* v_step_609_, lean_object* v_stepType_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Elab_Term_mkCalcTrans(v_result_607_, v_resultType_608_, v_step_609_, v_stepType_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec_ref(v_resultType_608_);
return v_res_616_;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
v___x_639_ = l_String_toRawSubstring_x27(v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(lean_object* v_type_664_, lean_object* v_t_665_, uint8_t v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
if (v_a_666_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref(v_type_664_);
v___x_674_ = lean_box(v_a_666_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_t_665_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
else
{
if (lean_obj_tag(v_t_665_) == 1)
{
lean_object* v_info_677_; lean_object* v_kind_678_; lean_object* v_args_679_; lean_object* v_k_681_; uint8_t v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; 
v_info_677_ = lean_ctor_get(v_t_665_, 0);
v_kind_678_ = lean_ctor_get(v_t_665_, 1);
v_args_679_ = lean_ctor_get(v_t_665_, 2);
if (lean_obj_tag(v_kind_678_) == 1)
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_kind_678_, 0);
if (lean_obj_tag(v_pre_718_) == 1)
{
lean_object* v_pre_719_; 
v_pre_719_ = lean_ctor_get(v_pre_718_, 0);
if (lean_obj_tag(v_pre_719_) == 1)
{
lean_object* v_pre_720_; 
v_pre_720_ = lean_ctor_get(v_pre_719_, 0);
if (lean_obj_tag(v_pre_720_) == 1)
{
lean_object* v_pre_721_; 
v_pre_721_ = lean_ctor_get(v_pre_720_, 0);
if (lean_obj_tag(v_pre_721_) == 0)
{
lean_object* v_str_722_; lean_object* v_str_723_; lean_object* v_str_724_; lean_object* v_str_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_str_722_ = lean_ctor_get(v_kind_678_, 1);
v_str_723_ = lean_ctor_get(v_pre_718_, 1);
v_str_724_ = lean_ctor_get(v_pre_719_, 1);
v_str_725_ = lean_ctor_get(v_pre_720_, 1);
v___x_726_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0));
v___x_727_ = lean_string_dec_eq(v_str_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_inc_ref(v_kind_678_);
lean_inc_ref(v_args_679_);
lean_inc(v_info_677_);
lean_dec_ref_known(v_t_665_, 3);
v_k_681_ = v_kind_678_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
v___y_687_ = v_a_671_;
v___y_688_ = v_a_672_;
goto v___jp_680_;
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1));
v___x_729_ = lean_string_dec_eq(v_str_724_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_inc_ref(v_str_724_);
lean_inc_ref(v_str_723_);
lean_inc(v_pre_721_);
lean_inc_ref(v_str_722_);
lean_inc_ref(v_args_679_);
lean_inc(v_info_677_);
lean_dec_ref_known(v_t_665_, 3);
v___x_730_ = l_Lean_Name_str___override(v_pre_721_, v___x_726_);
v___x_731_ = l_Lean_Name_str___override(v___x_730_, v_str_724_);
v___x_732_ = l_Lean_Name_str___override(v___x_731_, v_str_723_);
v___x_733_ = l_Lean_Name_str___override(v___x_732_, v_str_722_);
v_k_681_ = v___x_733_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
v___y_687_ = v_a_671_;
v___y_688_ = v_a_672_;
goto v___jp_680_;
}
else
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2));
v___x_735_ = lean_string_dec_eq(v_str_723_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_inc_ref(v_str_723_);
lean_inc(v_pre_721_);
lean_inc_ref(v_str_722_);
lean_inc_ref(v_args_679_);
lean_inc(v_info_677_);
lean_dec_ref_known(v_t_665_, 3);
v___x_736_ = l_Lean_Name_str___override(v_pre_721_, v___x_726_);
v___x_737_ = l_Lean_Name_str___override(v___x_736_, v___x_728_);
v___x_738_ = l_Lean_Name_str___override(v___x_737_, v_str_723_);
v___x_739_ = l_Lean_Name_str___override(v___x_738_, v_str_722_);
v_k_681_ = v___x_739_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
v___y_687_ = v_a_671_;
v___y_688_ = v_a_672_;
goto v___jp_680_;
}
else
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3));
v___x_741_ = lean_string_dec_eq(v_str_722_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_inc_ref(v_str_722_);
lean_inc(v_pre_721_);
lean_inc_ref(v_args_679_);
lean_inc(v_info_677_);
lean_dec_ref_known(v_t_665_, 3);
v___x_742_ = l_Lean_Name_str___override(v_pre_721_, v___x_726_);
v___x_743_ = l_Lean_Name_str___override(v___x_742_, v___x_728_);
v___x_744_ = l_Lean_Name_str___override(v___x_743_, v___x_734_);
v___x_745_ = l_Lean_Name_str___override(v___x_744_, v_str_722_);
v_k_681_ = v___x_745_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
v___y_687_ = v_a_671_;
v___y_688_ = v_a_672_;
goto v___jp_680_;
}
else
{
uint8_t v___x_746_; lean_object* v___x_747_; 
v___x_746_ = 0;
v___x_747_ = l_Lean_Elab_Term_exprToSyntax(v_type_664_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_toCold_748_; lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_780_; 
v_toCold_748_ = lean_ctor_get(v_a_671_, 0);
v_a_749_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_780_ == 0)
{
v___x_751_ = v___x_747_;
v_isShared_752_ = v_isSharedCheck_780_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_747_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_780_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_ref_753_; lean_object* v_quotContext_754_; lean_object* v_currMacroScope_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v_ref_753_ = lean_ctor_get(v_a_671_, 2);
v_quotContext_754_ = lean_ctor_get(v_toCold_748_, 8);
v_currMacroScope_755_ = lean_ctor_get(v_toCold_748_, 9);
v___x_756_ = l_Lean_SourceInfo_fromRef(v_ref_753_, v___x_746_);
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5));
v___x_758_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7));
v___x_759_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8));
lean_inc_n(v___x_756_, 7);
v___x_760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_756_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10));
v___x_762_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12);
lean_inc(v_currMacroScope_755_);
lean_inc(v_quotContext_754_);
v___x_763_ = l_Lean_addMacroScope(v_quotContext_754_, v_pre_721_, v_currMacroScope_755_);
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20));
v___x_765_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_765_, 0, v___x_756_);
lean_ctor_set(v___x_765_, 1, v___x_762_);
lean_ctor_set(v___x_765_, 2, v___x_763_);
lean_ctor_set(v___x_765_, 3, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___x_756_, v___x_761_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node2(v___x_756_, v___x_758_, v___x_760_, v___x_766_);
v___x_768_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21));
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_756_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23));
v___x_771_ = l_Lean_Syntax_node1(v___x_756_, v___x_770_, v_a_749_);
v___x_772_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24));
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_756_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_Syntax_node5(v___x_756_, v___x_757_, v___x_767_, v_t_665_, v___x_769_, v___x_771_, v___x_773_);
v___x_775_ = lean_box(v___x_746_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_776_);
v___x_778_ = v___x_751_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref_known(v_t_665_, 3);
v_a_781_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_747_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_747_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
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
lean_inc_ref(v_kind_678_);
lean_inc_ref(v_args_679_);
lean_inc(v_info_677_);
lean_dec_ref_known(v_t_665_, 3);
v_k_681_ = v_kind_678_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
v___y_687_ = v_a_671_;
v___y_688_ = v_a_672_;
goto v___jp_680_;
}
}
else
{
lean_inc_ref(v_kind_678_);
lean_inc_ref(v_args_679_);
lean_inc(v_info_677_);
lean_dec_ref_known(v_t_665_, 3);
v_k_681_ = v_kind_678_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
v___y_687_ = v_a_671_;
v___y_688_ = v_a_672_;
goto v___jp_680_;
}
}
else
{
lean_inc_ref(v_kind_678_);
lean_inc_ref(v_args_679_);
lean_inc(v_info_677_);
lean_dec_ref_known(v_t_665_, 3);
v_k_681_ = v_kind_678_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
v___y_687_ = v_a_671_;
v___y_688_ = v_a_672_;
goto v___jp_680_;
}
}
else
{
lean_inc_ref(v_kind_678_);
lean_inc_ref(v_args_679_);
lean_inc(v_info_677_);
lean_dec_ref_known(v_t_665_, 3);
v_k_681_ = v_kind_678_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
v___y_687_ = v_a_671_;
v___y_688_ = v_a_672_;
goto v___jp_680_;
}
}
else
{
lean_inc_ref(v_args_679_);
lean_inc(v_kind_678_);
lean_inc(v_info_677_);
lean_dec_ref_known(v_t_665_, 3);
v_k_681_ = v_kind_678_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
v___y_687_ = v_a_671_;
v___y_688_ = v_a_672_;
goto v___jp_680_;
}
v___jp_680_:
{
size_t v_sz_689_; size_t v___x_690_; lean_object* v___x_691_; 
v_sz_689_ = lean_array_size(v_args_679_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_664_, v_sz_689_, v___x_690_, v_args_679_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_709_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_709_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_709_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_709_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_708_; 
v_fst_696_ = lean_ctor_get(v_a_692_, 0);
v_snd_697_ = lean_ctor_get(v_a_692_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_699_ = v_a_692_;
v_isShared_700_ = v_isSharedCheck_708_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_snd_697_);
lean_inc(v_fst_696_);
lean_dec(v_a_692_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_708_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_701_, 0, v_info_677_);
lean_ctor_set(v___x_701_, 1, v_k_681_);
lean_ctor_set(v___x_701_, 2, v_fst_696_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_snd_697_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_703_);
v___x_705_ = v___x_694_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_k_681_);
lean_dec(v_info_677_);
v_a_710_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_691_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_691_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
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
}
else
{
uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v_type_664_);
v___x_789_ = 0;
v___x_790_ = lean_box(v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_t_665_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(lean_object* v_type_793_, size_t v_sz_794_, size_t v_i_795_, lean_object* v_bs_796_, uint8_t v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_type_793_);
v___x_806_ = lean_box(v___y_797_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_bs_796_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
else
{
lean_object* v_v_809_; lean_object* v___x_810_; lean_object* v_bs_x27_811_; lean_object* v___x_812_; 
v_v_809_ = lean_array_uget(v_bs_796_, v_i_795_);
v___x_810_ = lean_unsigned_to_nat(0u);
v_bs_x27_811_ = lean_array_uset(v_bs_796_, v_i_795_, v___x_810_);
lean_inc_ref(v_type_793_);
v___x_812_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_793_, v_v_809_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v_fst_814_; lean_object* v_snd_815_; size_t v___x_816_; size_t v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
v_fst_814_ = lean_ctor_get(v_a_813_, 0);
lean_inc(v_fst_814_);
v_snd_815_ = lean_ctor_get(v_a_813_, 1);
lean_inc(v_snd_815_);
lean_dec(v_a_813_);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_795_, v___x_816_);
v___x_818_ = lean_array_uset(v_bs_x27_811_, v_i_795_, v_fst_814_);
v___x_819_ = lean_unbox(v_snd_815_);
lean_dec(v_snd_815_);
v_i_795_ = v___x_817_;
v_bs_796_ = v___x_818_;
v___y_797_ = v___x_819_;
goto _start;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref(v_bs_x27_811_);
lean_dec_ref(v_type_793_);
v_a_821_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_812_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_812_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0___boxed(lean_object* v_type_829_, lean_object* v_sz_830_, lean_object* v_i_831_, lean_object* v_bs_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
size_t v_sz_boxed_841_; size_t v_i_boxed_842_; uint8_t v___y_7558__boxed_843_; lean_object* v_res_844_; 
v_sz_boxed_841_ = lean_unbox_usize(v_sz_830_);
lean_dec(v_sz_830_);
v_i_boxed_842_ = lean_unbox_usize(v_i_831_);
lean_dec(v_i_831_);
v___y_7558__boxed_843_ = lean_unbox(v___y_833_);
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_829_, v_sz_boxed_841_, v_i_boxed_842_, v_bs_832_, v___y_7558__boxed_843_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object* v_type_845_, lean_object* v_t_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
uint8_t v_a_7627__boxed_855_; lean_object* v_res_856_; 
v_a_7627__boxed_855_ = lean_unbox(v_a_847_);
v_res_856_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_845_, v_t_846_, v_a_7627__boxed_855_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object* v_t_857_, lean_object* v_type_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v___x_866_; lean_object* v___x_867_; 
v___x_866_ = 1;
v___x_867_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_858_, v_t_857_, v___x_866_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_876_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_876_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_fst_872_; lean_object* v___x_874_; 
v_fst_872_ = lean_ctor_get(v_a_868_, 0);
lean_inc(v_fst_872_);
lean_dec(v_a_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_fst_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_fst_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_867_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_867_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType___boxed(lean_object* v_t_885_, lean_object* v_type_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_t_885_, v_type_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_894_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
v___x_900_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg(){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0);
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___boxed(lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(lean_object* v_00_u03b1_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___boxed(lean_object* v_00_u03b1_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(v_00_u03b1_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_924_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__7));
v___x_941_ = l_String_toRawSubstring_x27(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView(lean_object* v_step0_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_toCold_958_; lean_object* v_ref_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_toCold_958_ = lean_ctor_get(v_a_955_, 0);
v_ref_959_ = lean_ctor_get(v_a_955_, 2);
v___x_960_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_950_);
v___x_961_ = l_Lean_Syntax_isOfKind(v_step0_950_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v_step0_950_);
v___x_962_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v_term_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_963_ = lean_unsigned_to_nat(0u);
v_term_964_ = l_Lean_Syntax_getArg(v_step0_950_, v___x_963_);
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = l_Lean_Syntax_getArg(v_step0_950_, v___x_965_);
lean_inc(v___x_966_);
v___x_967_ = l_Lean_Syntax_matchesNull(v___x_966_, v___x_963_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_966_);
v___x_969_ = l_Lean_Syntax_matchesNull(v___x_966_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
lean_dec(v___x_966_);
lean_dec(v_term_964_);
lean_dec(v_step0_950_);
v___x_970_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_970_;
}
else
{
lean_object* v_proof_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_proof_971_ = l_Lean_Syntax_getArg(v___x_966_, v___x_965_);
lean_dec(v___x_966_);
v___x_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_972_, 0, v_step0_950_);
lean_ctor_set(v___x_972_, 1, v_term_964_);
lean_ctor_set(v___x_972_, 2, v_proof_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
else
{
lean_object* v_ref_974_; uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_quotContext_981_; lean_object* v_currMacroScope_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec(v___x_966_);
v_ref_974_ = l_Lean_replaceRef(v_step0_950_, v_ref_959_);
v___x_975_ = 0;
v___x_976_ = l_Lean_SourceInfo_fromRef(v_ref_974_, v___x_975_);
lean_dec(v_ref_974_);
v___x_977_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__2));
lean_inc_n(v___x_976_, 4);
v___x_978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__3));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_976_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v_quotContext_981_ = lean_ctor_get(v_toCold_958_, 8);
v_currMacroScope_982_ = lean_ctor_get(v_toCold_958_, 9);
v___x_983_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__4));
v___x_984_ = l_Lean_Syntax_node1(v___x_976_, v___x_983_, v___x_980_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__6));
v___x_986_ = l_Lean_Syntax_node3(v___x_976_, v___x_985_, v_term_964_, v___x_978_, v___x_984_);
v___x_987_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcFirstStepView___closed__8, &l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once, _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8);
v___x_988_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__9));
lean_inc(v_currMacroScope_982_);
lean_inc(v_quotContext_981_);
v___x_989_ = l_Lean_addMacroScope(v_quotContext_981_, v___x_988_, v_currMacroScope_982_);
v___x_990_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__11));
v___x_991_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_991_, 0, v___x_976_);
lean_ctor_set(v___x_991_, 1, v___x_987_);
lean_ctor_set(v___x_991_, 2, v___x_989_);
lean_ctor_set(v___x_991_, 3, v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_992_, 0, v_step0_950_);
lean_ctor_set(v___x_992_, 1, v___x_986_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___boxed(lean_object* v_step0_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(lean_object* v_as_1007_, size_t v_sz_1008_, size_t v_i_1009_, lean_object* v_b_1010_){
_start:
{
lean_object* v_a_1013_; uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1009_, v_sz_1008_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_b_1010_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_a_1020_; uint8_t v___x_1021_; 
v___x_1019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1));
v_a_1020_ = lean_array_uget_borrowed(v_as_1007_, v_i_1009_);
lean_inc(v_a_1020_);
v___x_1021_ = l_Lean_Syntax_isOfKind(v_a_1020_, v___x_1019_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_dec_ref_known(v___x_1022_, 1);
v_a_1013_ = v_b_1010_;
goto v___jp_1012_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_b_1010_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = l_Lean_Syntax_getArg(v_a_1020_, v___x_1031_);
v___x_1033_ = lean_unsigned_to_nat(2u);
v___x_1034_ = l_Lean_Syntax_getArg(v_a_1020_, v___x_1033_);
lean_inc(v_a_1020_);
v___x_1035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1035_, 0, v_a_1020_);
lean_ctor_set(v___x_1035_, 1, v___x_1032_);
lean_ctor_set(v___x_1035_, 2, v___x_1034_);
v___x_1036_ = lean_array_push(v_b_1010_, v___x_1035_);
v_a_1013_ = v___x_1036_;
goto v___jp_1012_;
}
}
v___jp_1012_:
{
size_t v___x_1014_; size_t v___x_1015_; 
v___x_1014_ = ((size_t)1ULL);
v___x_1015_ = lean_usize_add(v_i_1009_, v___x_1014_);
v_i_1009_ = v___x_1015_;
v_b_1010_ = v_a_1013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___boxed(lean_object* v_as_1037_, lean_object* v_sz_1038_, lean_object* v_i_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_){
_start:
{
size_t v_sz_boxed_1042_; size_t v_i_boxed_1043_; lean_object* v_res_1044_; 
v_sz_boxed_1042_ = lean_unbox_usize(v_sz_1038_);
lean_dec(v_sz_1038_);
v_i_boxed_1043_ = lean_unbox_usize(v_i_1039_);
lean_dec(v_i_1039_);
v_res_1044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1037_, v_sz_boxed_1042_, v_i_boxed_1043_, v_b_1040_);
lean_dec_ref(v_as_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object* v_steps_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_1049_);
v___x_1058_ = l_Lean_Syntax_isOfKind(v_steps_1049_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec(v_steps_1049_);
v___x_1059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; lean_object* v_step0_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v_step0_1061_ = l_Lean_Syntax_getArg(v_steps_1049_, v___x_1060_);
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_1061_);
v___x_1063_ = l_Lean_Syntax_isOfKind(v_step0_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_dec(v_step0_1061_);
lean_dec(v_steps_1049_);
v___x_1064_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_rest_1067_; lean_object* v___x_1068_; 
v___x_1065_ = lean_unsigned_to_nat(1u);
v___x_1066_ = l_Lean_Syntax_getArg(v_steps_1049_, v___x_1065_);
lean_dec(v_steps_1049_);
v_rest_1067_ = l_Lean_Syntax_getArgs(v___x_1066_);
lean_dec(v___x_1066_);
v___x_1068_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_1061_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; size_t v_sz_1072_; size_t v___x_1073_; lean_object* v___x_1074_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = lean_mk_empty_array_with_capacity(v___x_1065_);
v___x_1071_ = lean_array_push(v___x_1070_, v_a_1069_);
v_sz_1072_ = lean_array_size(v_rest_1067_);
v___x_1073_ = ((size_t)0ULL);
v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_rest_1067_, v_sz_1072_, v___x_1073_, v___x_1071_);
lean_dec_ref(v_rest_1067_);
return v___x_1074_;
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref(v_rest_1067_);
v_a_1075_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1068_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1068_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews___boxed(lean_object* v_steps_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(lean_object* v_as_1092_, size_t v_sz_1093_, size_t v_i_1094_, lean_object* v_b_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1092_, v_sz_1093_, v_i_1094_, v_b_1095_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(lean_object* v_as_1104_, lean_object* v_sz_1105_, lean_object* v_i_1106_, lean_object* v_b_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
size_t v_sz_boxed_1115_; size_t v_i_boxed_1116_; lean_object* v_res_1117_; 
v_sz_boxed_1115_ = lean_unbox_usize(v_sz_1105_);
lean_dec(v_sz_1105_);
v_i_boxed_1116_ = lean_unbox_usize(v_i_1106_);
lean_dec(v_i_1106_);
v_res_1117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(v_as_1104_, v_sz_boxed_1115_, v_i_boxed_1116_, v_b_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec_ref(v_as_1104_);
return v_res_1117_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = l_Lean_instInhabitedExpr;
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(lean_object* v_msg_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_obj_once(&l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0, &l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0);
v___x_1122_ = lean_panic_fn_borrowed(v___x_1121_, v_msg_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(lean_object* v_opts_1123_, lean_object* v_opt_1124_){
_start:
{
lean_object* v_name_1125_; lean_object* v_defValue_1126_; lean_object* v_map_1127_; lean_object* v___x_1128_; 
v_name_1125_ = lean_ctor_get(v_opt_1124_, 0);
v_defValue_1126_ = lean_ctor_get(v_opt_1124_, 1);
v_map_1127_ = lean_ctor_get(v_opts_1123_, 0);
v___x_1128_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1127_, v_name_1125_);
if (lean_obj_tag(v___x_1128_) == 0)
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_unbox(v_defValue_1126_);
return v___x_1129_;
}
else
{
lean_object* v_val_1130_; 
v_val_1130_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v___x_1128_, 1);
if (lean_obj_tag(v_val_1130_) == 1)
{
uint8_t v_v_1131_; 
v_v_1131_ = lean_ctor_get_uint8(v_val_1130_, 0);
lean_dec_ref_known(v_val_1130_, 0);
return v_v_1131_;
}
else
{
uint8_t v___x_1132_; 
lean_dec(v_val_1130_);
v___x_1132_ = lean_unbox(v_defValue_1126_);
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_opts_1133_, lean_object* v_opt_1134_){
_start:
{
uint8_t v_res_1135_; lean_object* v_r_1136_; 
v_res_1135_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_opts_1133_, v_opt_1134_);
lean_dec_ref(v_opt_1134_);
lean_dec_ref(v_opts_1133_);
v_r_1136_ = lean_box(v_res_1135_);
return v_r_1136_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_box(1);
v___x_1138_ = l_Lean_MessageData_ofFormat(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2));
v___x_1143_ = l_Lean_MessageData_ofFormat(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
if (lean_obj_tag(v_x_1145_) == 0)
{
return v_x_1144_;
}
else
{
lean_object* v_head_1146_; lean_object* v_tail_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1169_; 
v_head_1146_ = lean_ctor_get(v_x_1145_, 0);
v_tail_1147_ = lean_ctor_get(v_x_1145_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1145_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1149_ = v_x_1145_;
v_isShared_1150_ = v_isSharedCheck_1169_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_tail_1147_);
lean_inc(v_head_1146_);
lean_dec(v_x_1145_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1169_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v_before_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1167_; 
v_before_1151_ = lean_ctor_get(v_head_1146_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_head_1146_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; 
v_unused_1168_ = lean_ctor_get(v_head_1146_, 1);
lean_dec(v_unused_1168_);
v___x_1153_ = v_head_1146_;
v_isShared_1154_ = v_isSharedCheck_1167_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_before_1151_);
lean_dec(v_head_1146_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1167_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set_tag(v___x_1153_, 7);
lean_ctor_set(v___x_1153_, 1, v___x_1155_);
lean_ctor_set(v___x_1153_, 0, v_x_1144_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_x_1144_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 7);
lean_ctor_set(v___x_1149_, 1, v___x_1158_);
lean_ctor_set(v___x_1149_, 0, v___x_1157_);
v___x_1160_ = v___x_1149_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_MessageData_ofSyntax(v_before_1151_);
v___x_1162_ = l_Lean_indentD(v___x_1161_);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1160_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v_x_1144_ = v___x_1163_;
v_x_1145_ = v_tail_1147_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_1174_ = l_Lean_MessageData_ofFormat(v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_1175_, lean_object* v_macroStack_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1177_);
v___x_1180_ = l_Lean_Elab_pp_macroStack;
v___x_1181_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v___x_1179_, v___x_1180_);
lean_dec_ref(v___x_1179_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_dec(v_macroStack_1176_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_msgData_1175_);
return v___x_1182_;
}
else
{
if (lean_obj_tag(v_macroStack_1176_) == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_msgData_1175_);
return v___x_1183_;
}
else
{
lean_object* v_head_1184_; lean_object* v_after_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1200_; 
v_head_1184_ = lean_ctor_get(v_macroStack_1176_, 0);
lean_inc(v_head_1184_);
v_after_1185_ = lean_ctor_get(v_head_1184_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_head_1184_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v_head_1184_, 0);
lean_dec(v_unused_1201_);
v___x_1187_ = v_head_1184_;
v_isShared_1188_ = v_isSharedCheck_1200_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_after_1185_);
lean_dec(v_head_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1200_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 7);
lean_ctor_set(v___x_1187_, 1, v___x_1189_);
lean_ctor_set(v___x_1187_, 0, v_msgData_1175_);
v___x_1191_ = v___x_1187_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_msgData_1175_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_msgData_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1192_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Lean_MessageData_ofSyntax(v_after_1185_);
v___x_1195_ = l_Lean_indentD(v___x_1194_);
v_msgData_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1196_, 0, v___x_1193_);
lean_ctor_set(v_msgData_1196_, 1, v___x_1195_);
v___x_1197_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(v_msgData_1196_, v_macroStack_1176_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1202_, lean_object* v_macroStack_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1202_, v_macroStack_1203_, v___y_1204_);
lean_dec_ref(v___y_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(lean_object* v_msg_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_ref_1215_; lean_object* v_macroStack_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_a_1219_; lean_object* v___x_1220_; lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1229_; 
v_ref_1215_ = lean_ctor_get(v___y_1212_, 2);
v_macroStack_1216_ = lean_ctor_get(v___y_1208_, 1);
v___x_1217_ = l_Lean_Elab_getBetterRef(v_ref_1215_, v_macroStack_1216_);
v___x_1218_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_1207_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref(v___x_1218_);
lean_inc(v_macroStack_1216_);
v___x_1220_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_a_1219_, v_macroStack_1216_, v___y_1212_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1217_);
lean_ctor_set(v___x_1225_, 1, v_a_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 1);
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(lean_object* v_ref_1239_, lean_object* v_msg_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_toCold_1248_; lean_object* v_currRecDepth_1249_; lean_object* v_ref_1250_; uint16_t v_optionFlags_1251_; uint8_t v_suppressElabErrors_1252_; uint8_t v_checkDeprecated_1253_; uint8_t v_isRecordingDeps_1254_; lean_object* v_ref_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_toCold_1248_ = lean_ctor_get(v___y_1245_, 0);
v_currRecDepth_1249_ = lean_ctor_get(v___y_1245_, 1);
v_ref_1250_ = lean_ctor_get(v___y_1245_, 2);
v_optionFlags_1251_ = lean_ctor_get_uint16(v___y_1245_, sizeof(void*)*3);
v_suppressElabErrors_1252_ = lean_ctor_get_uint8(v___y_1245_, sizeof(void*)*3 + 2);
v_checkDeprecated_1253_ = lean_ctor_get_uint8(v___y_1245_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1254_ = lean_ctor_get_uint8(v___y_1245_, sizeof(void*)*3 + 4);
v_ref_1255_ = l_Lean_replaceRef(v_ref_1239_, v_ref_1250_);
lean_inc(v_currRecDepth_1249_);
lean_inc_ref(v_toCold_1248_);
v___x_1256_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1256_, 0, v_toCold_1248_);
lean_ctor_set(v___x_1256_, 1, v_currRecDepth_1249_);
lean_ctor_set(v___x_1256_, 2, v_ref_1255_);
lean_ctor_set_uint16(v___x_1256_, sizeof(void*)*3, v_optionFlags_1251_);
lean_ctor_set_uint8(v___x_1256_, sizeof(void*)*3 + 2, v_suppressElabErrors_1252_);
lean_ctor_set_uint8(v___x_1256_, sizeof(void*)*3 + 3, v_checkDeprecated_1253_);
lean_ctor_set_uint8(v___x_1256_, sizeof(void*)*3 + 4, v_isRecordingDeps_1254_);
v___x_1257_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___x_1256_, v___y_1246_);
lean_dec_ref_known(v___x_1256_, 3);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg___boxed(lean_object* v_ref_1258_, lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1258_, v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v_ref_1258_);
return v_res_1267_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4));
v___x_1276_ = l_Lean_stringToMessageData(v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(lean_object* v_as_1280_, size_t v_sz_1281_, size_t v_i_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_a_1292_; lean_object* v___y_1297_; lean_object* v_____do__lift_1298_; uint8_t v___x_1302_; 
v___x_1302_ = lean_usize_dec_lt(v_i_1282_, v_sz_1281_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_b_1283_);
return v___x_1303_;
}
else
{
lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1512_; 
v_fst_1304_ = lean_ctor_get(v_b_1283_, 0);
v_snd_1305_ = lean_ctor_get(v_b_1283_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_b_1283_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1307_ = v_b_1283_;
v_isShared_1308_ = v_isSharedCheck_1512_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_snd_1305_);
lean_inc(v_fst_1304_);
lean_dec(v_b_1283_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1512_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_a_1309_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v_____do__lift_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; 
v_a_1309_ = lean_array_uget_borrowed(v_as_1280_, v_i_1282_);
if (lean_obj_tag(v_snd_1305_) == 1)
{
lean_object* v_val_1489_; lean_object* v___x_1490_; 
v_val_1489_ = lean_ctor_get(v_snd_1305_, 0);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v_val_1489_);
v___x_1490_ = lean_infer_type(v_val_1489_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v_term_1492_; lean_object* v___x_1493_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v_term_1492_ = lean_ctor_get(v_a_1309_, 1);
lean_inc(v_term_1492_);
v___x_1493_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_term_1492_, v_a_1491_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v_____do__lift_1372_ = v_a_1494_;
v___y_1373_ = v___y_1284_;
v___y_1374_ = v___y_1285_;
v___y_1375_ = v___y_1286_;
v___y_1376_ = v___y_1287_;
v___y_1377_ = v___y_1288_;
v___y_1378_ = v___y_1289_;
goto v___jp_1371_;
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref_known(v_snd_1305_, 1);
lean_del_object(v___x_1307_);
lean_dec(v_fst_1304_);
v_a_1495_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1493_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1493_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec_ref_known(v_snd_1305_, 1);
lean_del_object(v___x_1307_);
lean_dec(v_fst_1304_);
v_a_1503_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1490_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1490_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_object* v_term_1511_; 
v_term_1511_ = lean_ctor_get(v_a_1309_, 1);
lean_inc(v_term_1511_);
v_____do__lift_1372_ = v_term_1511_;
v___y_1373_ = v___y_1284_;
v___y_1374_ = v___y_1285_;
v___y_1375_ = v___y_1286_;
v___y_1376_ = v___y_1287_;
v___y_1377_ = v___y_1288_;
v___y_1378_ = v___y_1289_;
goto v___jp_1371_;
}
v___jp_1310_:
{
lean_object* v_term_1319_; lean_object* v_proof_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_term_1319_ = lean_ctor_get(v_a_1309_, 1);
v_proof_1320_ = lean_ctor_get(v_a_1309_, 2);
lean_inc_ref(v___y_1312_);
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___y_1312_);
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_box(v___x_1302_);
v___x_1324_ = lean_box(v___x_1302_);
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1313_);
lean_inc(v_proof_1320_);
v___x_1325_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 9);
lean_closure_set(v___x_1325_, 0, v_proof_1320_);
lean_closure_set(v___x_1325_, 1, v___x_1321_);
lean_closure_set(v___x_1325_, 2, v___x_1323_);
lean_closure_set(v___x_1325_, 3, v___x_1324_);
lean_closure_set(v___x_1325_, 4, v___x_1322_);
lean_closure_set(v___x_1325_, 5, v___y_1313_);
lean_closure_set(v___x_1325_, 6, v___y_1314_);
lean_closure_set(v___x_1325_, 7, v___y_1315_);
lean_closure_set(v___x_1325_, 8, v___y_1316_);
v___x_1326_ = l_Lean_Core_withFreshMacroScope___redArg(v___x_1325_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1326_) == 0)
{
if (lean_obj_tag(v_fst_1304_) == 1)
{
lean_object* v_val_1327_; lean_object* v_a_1328_; lean_object* v_fst_1329_; lean_object* v_snd_1330_; lean_object* v___x_1331_; 
lean_del_object(v___x_1307_);
v_val_1327_ = lean_ctor_get(v_fst_1304_, 0);
lean_inc(v_val_1327_);
lean_dec_ref_known(v_fst_1304_, 1);
v_a_1328_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1326_, 1);
v_fst_1329_ = lean_ctor_get(v_val_1327_, 0);
lean_inc(v_fst_1329_);
v_snd_1330_ = lean_ctor_get(v_val_1327_, 1);
lean_inc(v_snd_1330_);
lean_dec(v_val_1327_);
v___x_1331_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_toCold_1332_; lean_object* v_currRecDepth_1333_; lean_object* v_ref_1334_; uint16_t v_optionFlags_1335_; uint8_t v_suppressElabErrors_1336_; uint8_t v_checkDeprecated_1337_; uint8_t v_isRecordingDeps_1338_; lean_object* v_ref_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref_known(v___x_1331_, 1);
v_toCold_1332_ = lean_ctor_get(v___y_1317_, 0);
v_currRecDepth_1333_ = lean_ctor_get(v___y_1317_, 1);
v_ref_1334_ = lean_ctor_get(v___y_1317_, 2);
v_optionFlags_1335_ = lean_ctor_get_uint16(v___y_1317_, sizeof(void*)*3);
v_suppressElabErrors_1336_ = lean_ctor_get_uint8(v___y_1317_, sizeof(void*)*3 + 2);
v_checkDeprecated_1337_ = lean_ctor_get_uint8(v___y_1317_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1338_ = lean_ctor_get_uint8(v___y_1317_, sizeof(void*)*3 + 4);
v_ref_1339_ = l_Lean_replaceRef(v_term_1319_, v_ref_1334_);
lean_inc(v_currRecDepth_1333_);
lean_inc_ref(v_toCold_1332_);
v___x_1340_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1340_, 0, v_toCold_1332_);
lean_ctor_set(v___x_1340_, 1, v_currRecDepth_1333_);
lean_ctor_set(v___x_1340_, 2, v_ref_1339_);
lean_ctor_set_uint16(v___x_1340_, sizeof(void*)*3, v_optionFlags_1335_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*3 + 2, v_suppressElabErrors_1336_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*3 + 3, v_checkDeprecated_1337_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*3 + 4, v_isRecordingDeps_1338_);
v___x_1341_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_1329_, v_snd_1330_, v_a_1328_, v___y_1312_, v___y_1315_, v___y_1316_, v___x_1340_, v___y_1318_);
lean_dec_ref_known(v___x_1340_, 3);
lean_dec(v_snd_1330_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___y_1297_ = v___y_1311_;
v_____do__lift_1298_ = v_a_1342_;
goto v___jp_1296_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v___y_1311_);
v_a_1343_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1341_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_snd_1330_);
lean_dec(v_fst_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v___y_1311_);
v_a_1351_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1331_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1331_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; 
lean_dec(v_fst_1304_);
v_a_1359_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1326_, 1);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___y_1312_);
lean_ctor_set(v___x_1307_, 0, v_a_1359_);
v___x_1361_ = v___x_1307_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1359_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___y_1312_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
v___y_1297_ = v___y_1311_;
v_____do__lift_1298_ = v___x_1361_;
goto v___jp_1296_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec_ref(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_del_object(v___x_1307_);
lean_dec(v_fst_1304_);
v_a_1363_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1326_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1326_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
v___jp_1371_:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Elab_Term_elabType(v_____do__lift_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_1380_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
if (lean_obj_tag(v_a_1382_) == 1)
{
lean_object* v_val_1383_; lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1457_; 
v_val_1383_ = lean_ctor_get(v_a_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_a_1382_, 1);
v_snd_1384_ = lean_ctor_get(v_val_1383_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_val_1383_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v_val_1383_, 0);
lean_dec(v_unused_1458_);
v___x_1386_ = v_val_1383_;
v_isShared_1387_ = v_isSharedCheck_1457_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_dec(v_val_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1457_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
if (lean_obj_tag(v_snd_1305_) == 1)
{
lean_object* v_fst_1388_; lean_object* v_snd_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1455_; 
v_fst_1388_ = lean_ctor_get(v_snd_1384_, 0);
v_snd_1389_ = lean_ctor_get(v_snd_1384_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_snd_1384_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1391_ = v_snd_1384_;
v_isShared_1392_ = v_isSharedCheck_1455_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_snd_1389_);
lean_inc(v_fst_1388_);
lean_dec(v_snd_1384_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1455_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_val_1393_; lean_object* v___x_1394_; 
v_val_1393_ = lean_ctor_get(v_snd_1305_, 0);
lean_inc_n(v_val_1393_, 2);
lean_dec_ref_known(v_snd_1305_, 1);
lean_inc(v_fst_1388_);
v___x_1394_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1388_, v_val_1393_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; uint8_t v___x_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = lean_unbox(v_a_1395_);
lean_dec(v_a_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v_fst_1388_);
v___x_1397_ = lean_infer_type(v_fst_1388_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v_val_1393_);
v___x_1399_ = lean_infer_type(v_val_1393_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v_term_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v_term_1401_ = lean_ctor_get(v_a_1309_, 1);
v___x_1402_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_1403_ = l_Lean_MessageData_ofExpr(v_fst_1388_);
v___x_1404_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 7);
lean_ctor_set(v___x_1391_, 1, v___x_1404_);
lean_ctor_set(v___x_1391_, 0, v___x_1403_);
v___x_1406_ = v___x_1391_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = l_Lean_MessageData_ofExpr(v_a_1398_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 7);
lean_ctor_set(v___x_1386_, 1, v___x_1407_);
lean_ctor_set(v___x_1386_, 0, v___x_1406_);
v___x_1409_ = v___x_1386_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1410_ = l_Lean_indentD(v___x_1409_);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1402_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_MessageData_ofExpr(v_val_1393_);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v___x_1404_);
v___x_1416_ = l_Lean_MessageData_ofExpr(v_a_1400_);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Lean_indentD(v___x_1417_);
v___x_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1413_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1401_, v___x_1419_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_dec_ref_known(v___x_1420_, 1);
v___y_1311_ = v_snd_1389_;
v___y_1312_ = v_a_1380_;
v___y_1313_ = v___y_1373_;
v___y_1314_ = v___y_1374_;
v___y_1315_ = v___y_1375_;
v___y_1316_ = v___y_1376_;
v___y_1317_ = v___y_1377_;
v___y_1318_ = v___y_1378_;
goto v___jp_1310_;
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_snd_1389_);
lean_dec(v_a_1380_);
lean_del_object(v___x_1307_);
lean_dec(v_fst_1304_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_a_1398_);
lean_dec(v_val_1393_);
lean_del_object(v___x_1391_);
lean_dec(v_snd_1389_);
lean_dec(v_fst_1388_);
lean_del_object(v___x_1386_);
lean_dec(v_a_1380_);
lean_del_object(v___x_1307_);
lean_dec(v_fst_1304_);
v_a_1431_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1399_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1399_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_val_1393_);
lean_del_object(v___x_1391_);
lean_dec(v_snd_1389_);
lean_dec(v_fst_1388_);
lean_del_object(v___x_1386_);
lean_dec(v_a_1380_);
lean_del_object(v___x_1307_);
lean_dec(v_fst_1304_);
v_a_1439_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1397_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1397_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_dec(v_val_1393_);
lean_del_object(v___x_1391_);
lean_dec(v_fst_1388_);
lean_del_object(v___x_1386_);
v___y_1311_ = v_snd_1389_;
v___y_1312_ = v_a_1380_;
v___y_1313_ = v___y_1373_;
v___y_1314_ = v___y_1374_;
v___y_1315_ = v___y_1375_;
v___y_1316_ = v___y_1376_;
v___y_1317_ = v___y_1377_;
v___y_1318_ = v___y_1378_;
goto v___jp_1310_;
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_val_1393_);
lean_del_object(v___x_1391_);
lean_dec(v_snd_1389_);
lean_dec(v_fst_1388_);
lean_del_object(v___x_1386_);
lean_dec(v_a_1380_);
lean_del_object(v___x_1307_);
lean_dec(v_fst_1304_);
v_a_1447_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1394_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1394_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v_snd_1456_; 
lean_del_object(v___x_1386_);
lean_dec(v_snd_1305_);
v_snd_1456_ = lean_ctor_get(v_snd_1384_, 1);
lean_inc(v_snd_1456_);
lean_dec(v_snd_1384_);
v___y_1311_ = v_snd_1456_;
v___y_1312_ = v_a_1380_;
v___y_1313_ = v___y_1373_;
v___y_1314_ = v___y_1374_;
v___y_1315_ = v___y_1375_;
v___y_1316_ = v___y_1376_;
v___y_1317_ = v___y_1377_;
v___y_1318_ = v___y_1378_;
goto v___jp_1310_;
}
}
}
else
{
lean_object* v_term_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec(v_a_1382_);
lean_del_object(v___x_1307_);
v_term_1459_ = lean_ctor_get(v_a_1309_, 1);
v___x_1460_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7);
v___x_1461_ = l_Lean_indentExpr(v_a_1380_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1459_, v___x_1462_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; 
lean_dec_ref_known(v___x_1463_, 1);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_fst_1304_);
lean_ctor_set(v___x_1464_, 1, v_snd_1305_);
v_a_1292_ = v___x_1464_;
goto v___jp_1291_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_snd_1305_);
lean_dec(v_fst_1304_);
v_a_1465_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1463_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_a_1380_);
lean_del_object(v___x_1307_);
lean_dec(v_snd_1305_);
lean_dec(v_fst_1304_);
v_a_1473_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1381_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1381_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_del_object(v___x_1307_);
lean_dec(v_snd_1305_);
lean_dec(v_fst_1304_);
v_a_1481_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1379_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1379_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
v___jp_1291_:
{
size_t v___x_1293_; size_t v___x_1294_; 
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1282_, v___x_1293_);
v_i_1282_ = v___x_1294_;
v_b_1283_ = v_a_1292_;
goto _start;
}
v___jp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_____do__lift_1298_);
v___x_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___y_1297_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v_a_1292_ = v___x_1301_;
goto v___jp_1291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___boxed(lean_object* v_as_1513_, lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
size_t v_sz_boxed_1524_; size_t v_i_boxed_1525_; lean_object* v_res_1526_; 
v_sz_boxed_1524_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1525_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_as_1513_, v_sz_boxed_1524_, v_i_boxed_1525_, v_b_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v_as_1513_);
return v_res_1526_;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__4(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1532_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__3));
v___x_1533_ = lean_unsigned_to_nat(14u);
v___x_1534_ = lean_unsigned_to_nat(22u);
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__2));
v___x_1536_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__1));
v___x_1537_ = l_mkPanicMessageWithDecl(v___x_1536_, v___x_1535_, v___x_1534_, v___x_1533_, v___x_1532_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object* v_steps_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1546_; size_t v_sz_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v___x_1546_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__0));
v_sz_1547_ = lean_array_size(v_steps_1538_);
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_steps_1538_, v_sz_1547_, v___x_1548_, v___x_1546_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v_fst_1551_; lean_object* v___x_1552_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v_fst_1551_ = lean_ctor_get(v_a_1550_, 0);
lean_inc(v_fst_1551_);
lean_dec(v_a_1550_);
v___x_1552_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1565_; 
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v___x_1552_, 0);
lean_dec(v_unused_1566_);
v___x_1554_ = v___x_1552_;
v_isShared_1555_ = v_isSharedCheck_1565_;
goto v_resetjp_1553_;
}
else
{
lean_dec(v___x_1552_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1565_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
if (lean_obj_tag(v_fst_1551_) == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Term_elabCalcSteps___closed__4, &l_Lean_Elab_Term_elabCalcSteps___closed__4_once, _init_l_Lean_Elab_Term_elabCalcSteps___closed__4);
v___x_1557_ = l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(v___x_1556_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1557_);
v___x_1559_ = v___x_1554_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
lean_object* v_val_1561_; lean_object* v___x_1563_; 
v_val_1561_ = lean_ctor_get(v_fst_1551_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v_fst_1551_, 1);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v_val_1561_);
v___x_1563_ = v___x_1554_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_val_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_fst_1551_);
v_a_1567_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1552_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1552_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_a_1575_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1549_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1549_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps___boxed(lean_object* v_steps_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Elab_Term_elabCalcSteps(v_steps_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec_ref(v_steps_1583_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(lean_object* v_00_u03b1_1592_, lean_object* v_ref_1593_, lean_object* v_msg_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1593_, v_msg_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_ref_1604_, lean_object* v_msg_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(v_00_u03b1_1603_, v_ref_1604_, v_msg_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v_ref_1604_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(lean_object* v_00_u03b1_1614_, lean_object* v_msg_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1624_, lean_object* v_msg_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(v_00_u03b1_1624_, v_msg_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(lean_object* v_msgData_1634_, lean_object* v_macroStack_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1634_, v_macroStack_1635_, v___y_1640_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1644_, lean_object* v_macroStack_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(v_msgData_1644_, v_macroStack_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1653_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_box(0);
v___x_1655_ = l_Lean_Elab_abortTermExceptionId;
v___x_1656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v___x_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg(){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0);
v___x_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___boxed(lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(lean_object* v_00_u03b1_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___boxed(lean_object* v_00_u03b1_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(v_00_u03b1_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(lean_object* v_msg_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___f_1682_; lean_object* v___x_4885__overap_1683_; lean_object* v___x_1684_; 
v___f_1682_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_4885__overap_1683_ = lean_panic_fn_borrowed(v___f_1682_, v_msg_1676_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
v___x_1684_ = lean_apply_5(v___x_4885__overap_1683_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, lean_box(0));
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg___boxed(lean_object* v_msg_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(lean_object* v_00_u03b1_1692_, lean_object* v_msg_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(v_00_u03b1_1700_, v_msg_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(uint8_t v_suppressElabErrors_1715_, lean_object* v_x_1716_){
_start:
{
if (lean_obj_tag(v_x_1716_) == 1)
{
lean_object* v_pre_1717_; 
v_pre_1717_ = lean_ctor_get(v_x_1716_, 0);
switch(lean_obj_tag(v_pre_1717_))
{
case 1:
{
lean_object* v_pre_1718_; 
v_pre_1718_ = lean_ctor_get(v_pre_1717_, 0);
switch(lean_obj_tag(v_pre_1718_))
{
case 0:
{
lean_object* v_str_1719_; lean_object* v_str_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_str_1719_ = lean_ctor_get(v_x_1716_, 1);
v_str_1720_ = lean_ctor_get(v_pre_1717_, 1);
v___x_1721_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13));
v___x_1722_ = lean_string_dec_eq(v_str_1720_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0));
v___x_1724_ = lean_string_dec_eq(v_str_1720_, v___x_1723_);
if (v___x_1724_ == 0)
{
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1));
v___x_1726_ = lean_string_dec_eq(v_str_1719_, v___x_1725_);
if (v___x_1726_ == 0)
{
return v___x_1726_;
}
else
{
return v_suppressElabErrors_1715_;
}
}
}
else
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2));
v___x_1728_ = lean_string_dec_eq(v_str_1719_, v___x_1727_);
if (v___x_1728_ == 0)
{
return v___x_1728_;
}
else
{
return v_suppressElabErrors_1715_;
}
}
}
case 1:
{
lean_object* v_pre_1729_; 
v_pre_1729_ = lean_ctor_get(v_pre_1718_, 0);
if (lean_obj_tag(v_pre_1729_) == 0)
{
lean_object* v_str_1730_; lean_object* v_str_1731_; lean_object* v_str_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v_str_1730_ = lean_ctor_get(v_x_1716_, 1);
v_str_1731_ = lean_ctor_get(v_pre_1717_, 1);
v_str_1732_ = lean_ctor_get(v_pre_1718_, 1);
v___x_1733_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3));
v___x_1734_ = lean_string_dec_eq(v_str_1732_, v___x_1733_);
if (v___x_1734_ == 0)
{
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4));
v___x_1736_ = lean_string_dec_eq(v_str_1731_, v___x_1735_);
if (v___x_1736_ == 0)
{
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5));
v___x_1738_ = lean_string_dec_eq(v_str_1730_, v___x_1737_);
if (v___x_1738_ == 0)
{
return v___x_1738_;
}
else
{
return v_suppressElabErrors_1715_;
}
}
}
}
else
{
uint8_t v___x_1739_; 
v___x_1739_ = 0;
return v___x_1739_;
}
}
default: 
{
uint8_t v___x_1740_; 
v___x_1740_ = 0;
return v___x_1740_;
}
}
}
case 0:
{
lean_object* v_str_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_str_1741_ = lean_ctor_get(v_x_1716_, 1);
v___x_1742_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6));
v___x_1743_ = lean_string_dec_eq(v_str_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
return v___x_1743_;
}
else
{
return v_suppressElabErrors_1715_;
}
}
default: 
{
uint8_t v___x_1744_; 
v___x_1744_ = 0;
return v___x_1744_;
}
}
}
else
{
uint8_t v___x_1745_; 
v___x_1745_ = 0;
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1746_, lean_object* v_x_1747_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1748_; uint8_t v_res_1749_; lean_object* v_r_1750_; 
v_suppressElabErrors_boxed_1748_ = lean_unbox(v_suppressElabErrors_1746_);
v_res_1749_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_1748_, v_x_1747_);
lean_dec(v_x_1747_);
v_r_1750_ = lean_box(v_res_1749_);
return v_r_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(lean_object* v_ref_1751_, lean_object* v_msgData_1752_, uint8_t v_severity_1753_, uint8_t v_isSilent_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; uint8_t v___y_1765_; uint8_t v___y_1766_; lean_object* v___y_1767_; lean_object* v_toCold_1768_; lean_object* v___y_1769_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; uint8_t v___y_1801_; uint8_t v___y_1802_; uint8_t v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1825_; lean_object* v___y_1826_; uint8_t v___y_1827_; lean_object* v___y_1828_; uint8_t v___y_1829_; uint8_t v___y_1830_; lean_object* v___y_1831_; uint8_t v___y_1835_; uint8_t v___y_1836_; uint8_t v___x_1846_; uint8_t v___y_1848_; uint8_t v___x_1854_; 
v___x_1846_ = 2;
v___x_1854_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1753_, v___x_1846_);
if (v___x_1854_ == 0)
{
v___y_1848_ = v___x_1854_;
goto v___jp_1847_;
}
else
{
uint8_t v___x_1855_; 
lean_inc_ref(v_msgData_1752_);
v___x_1855_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1752_);
if (v___x_1855_ == 0)
{
v___y_1848_ = v___x_1855_;
goto v___jp_1847_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec_ref(v_msgData_1752_);
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
v___jp_1760_:
{
lean_object* v_currNamespace_1770_; lean_object* v_openDecls_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v_env_1776_; lean_object* v_nextMacroScope_1777_; lean_object* v_ngen_1778_; lean_object* v_auxDeclNGen_1779_; lean_object* v_traceState_1780_; lean_object* v_cache_1781_; lean_object* v_recordedDeps_1782_; lean_object* v_messages_1783_; lean_object* v_infoState_1784_; lean_object* v_snapshotTasks_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1796_; 
v_currNamespace_1770_ = lean_ctor_get(v_toCold_1768_, 4);
v_openDecls_1771_ = lean_ctor_get(v_toCold_1768_, 5);
lean_inc(v_openDecls_1771_);
lean_inc(v_currNamespace_1770_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_currNamespace_1770_);
lean_ctor_set(v___x_1772_, 1, v_openDecls_1771_);
v___x_1773_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___y_1762_);
lean_inc_ref(v___y_1763_);
lean_inc_ref(v___y_1761_);
v___x_1774_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1774_, 0, v___y_1761_);
lean_ctor_set(v___x_1774_, 1, v___y_1764_);
lean_ctor_set(v___x_1774_, 2, v___y_1767_);
lean_ctor_set(v___x_1774_, 3, v___y_1763_);
lean_ctor_set(v___x_1774_, 4, v___x_1773_);
lean_ctor_set_uint8(v___x_1774_, sizeof(void*)*5, v___y_1766_);
lean_ctor_set_uint8(v___x_1774_, sizeof(void*)*5 + 1, v___y_1765_);
lean_ctor_set_uint8(v___x_1774_, sizeof(void*)*5 + 2, v_isSilent_1754_);
v___x_1775_ = lean_st_ref_take(v___y_1769_);
v_env_1776_ = lean_ctor_get(v___x_1775_, 0);
v_nextMacroScope_1777_ = lean_ctor_get(v___x_1775_, 1);
v_ngen_1778_ = lean_ctor_get(v___x_1775_, 2);
v_auxDeclNGen_1779_ = lean_ctor_get(v___x_1775_, 3);
v_traceState_1780_ = lean_ctor_get(v___x_1775_, 4);
v_cache_1781_ = lean_ctor_get(v___x_1775_, 5);
v_recordedDeps_1782_ = lean_ctor_get(v___x_1775_, 6);
v_messages_1783_ = lean_ctor_get(v___x_1775_, 7);
v_infoState_1784_ = lean_ctor_get(v___x_1775_, 8);
v_snapshotTasks_1785_ = lean_ctor_get(v___x_1775_, 9);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1787_ = v___x_1775_;
v_isShared_1788_ = v_isSharedCheck_1796_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_snapshotTasks_1785_);
lean_inc(v_infoState_1784_);
lean_inc(v_messages_1783_);
lean_inc(v_recordedDeps_1782_);
lean_inc(v_cache_1781_);
lean_inc(v_traceState_1780_);
lean_inc(v_auxDeclNGen_1779_);
lean_inc(v_ngen_1778_);
lean_inc(v_nextMacroScope_1777_);
lean_inc(v_env_1776_);
lean_dec(v___x_1775_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1796_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1789_ = lean_box(0);
v___x_1790_ = l_Lean_MessageLog_add(v___x_1774_, v_messages_1783_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 7, v___x_1790_);
v___x_1792_ = v___x_1787_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_env_1776_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_nextMacroScope_1777_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_ngen_1778_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v_auxDeclNGen_1779_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v_traceState_1780_);
lean_ctor_set(v_reuseFailAlloc_1795_, 5, v_cache_1781_);
lean_ctor_set(v_reuseFailAlloc_1795_, 6, v_recordedDeps_1782_);
lean_ctor_set(v_reuseFailAlloc_1795_, 7, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1795_, 8, v_infoState_1784_);
lean_ctor_set(v_reuseFailAlloc_1795_, 9, v_snapshotTasks_1785_);
v___x_1792_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_st_ref_put(v___y_1769_, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1789_);
return v___x_1794_;
}
}
}
v___jp_1797_:
{
lean_object* v_fileName_1806_; lean_object* v_fileMap_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1823_; 
v_fileName_1806_ = lean_ctor_get(v___y_1800_, 0);
v_fileMap_1807_ = lean_ctor_get(v___y_1800_, 1);
v___x_1808_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1752_);
v___x_1809_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v___x_1808_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_inc_ref_n(v_fileMap_1807_, 2);
v___x_1814_ = l_Lean_FileMap_toPosition(v_fileMap_1807_, v___y_1804_);
lean_dec(v___y_1804_);
v___x_1815_ = l_Lean_FileMap_toPosition(v_fileMap_1807_, v___y_1805_);
lean_dec(v___y_1805_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
v___x_1817_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
if (v___y_1803_ == 0)
{
lean_del_object(v___x_1812_);
lean_dec_ref(v___y_1798_);
v___y_1761_ = v_fileName_1806_;
v___y_1762_ = v_a_1810_;
v___y_1763_ = v___x_1817_;
v___y_1764_ = v___x_1814_;
v___y_1765_ = v___y_1802_;
v___y_1766_ = v___y_1801_;
v___y_1767_ = v___x_1816_;
v_toCold_1768_ = v___y_1799_;
v___y_1769_ = v___y_1758_;
goto v___jp_1760_;
}
else
{
uint8_t v___x_1818_; 
lean_inc(v_a_1810_);
v___x_1818_ = l_Lean_MessageData_hasTag(v___y_1798_, v_a_1810_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_dec_ref_known(v___x_1816_, 1);
lean_dec_ref(v___x_1814_);
lean_dec(v_a_1810_);
v___x_1819_ = lean_box(0);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1819_);
v___x_1821_ = v___x_1812_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
else
{
lean_del_object(v___x_1812_);
v___y_1761_ = v_fileName_1806_;
v___y_1762_ = v_a_1810_;
v___y_1763_ = v___x_1817_;
v___y_1764_ = v___x_1814_;
v___y_1765_ = v___y_1802_;
v___y_1766_ = v___y_1801_;
v___y_1767_ = v___x_1816_;
v_toCold_1768_ = v___y_1799_;
v___y_1769_ = v___y_1758_;
goto v___jp_1760_;
}
}
}
}
v___jp_1824_:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Syntax_getTailPos_x3f(v___y_1828_, v___y_1830_);
lean_dec(v___y_1828_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_inc(v___y_1831_);
v___y_1798_ = v___y_1825_;
v___y_1799_ = v___y_1826_;
v___y_1800_ = v___y_1826_;
v___y_1801_ = v___y_1830_;
v___y_1802_ = v___y_1829_;
v___y_1803_ = v___y_1827_;
v___y_1804_ = v___y_1831_;
v___y_1805_ = v___y_1831_;
goto v___jp_1797_;
}
else
{
lean_object* v_val_1833_; 
v_val_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v___y_1798_ = v___y_1825_;
v___y_1799_ = v___y_1826_;
v___y_1800_ = v___y_1826_;
v___y_1801_ = v___y_1830_;
v___y_1802_ = v___y_1829_;
v___y_1803_ = v___y_1827_;
v___y_1804_ = v___y_1831_;
v___y_1805_ = v_val_1833_;
goto v___jp_1797_;
}
}
v___jp_1834_:
{
lean_object* v_toCold_1837_; lean_object* v_ref_1838_; uint8_t v_suppressElabErrors_1839_; lean_object* v___x_1840_; lean_object* v___f_1841_; lean_object* v_ref_1842_; lean_object* v___x_1843_; 
v_toCold_1837_ = lean_ctor_get(v___y_1757_, 0);
v_ref_1838_ = lean_ctor_get(v___y_1757_, 2);
v_suppressElabErrors_1839_ = lean_ctor_get_uint8(v___y_1757_, sizeof(void*)*3 + 2);
v___x_1840_ = lean_box(v_suppressElabErrors_1839_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1841_, 0, v___x_1840_);
v_ref_1842_ = l_Lean_replaceRef(v_ref_1751_, v_ref_1838_);
v___x_1843_ = l_Lean_Syntax_getPos_x3f(v_ref_1842_, v___y_1835_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_unsigned_to_nat(0u);
v___y_1825_ = v___f_1841_;
v___y_1826_ = v_toCold_1837_;
v___y_1827_ = v_suppressElabErrors_1839_;
v___y_1828_ = v_ref_1842_;
v___y_1829_ = v___y_1836_;
v___y_1830_ = v___y_1835_;
v___y_1831_ = v___x_1844_;
goto v___jp_1824_;
}
else
{
lean_object* v_val_1845_; 
v_val_1845_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_val_1845_);
lean_dec_ref_known(v___x_1843_, 1);
v___y_1825_ = v___f_1841_;
v___y_1826_ = v_toCold_1837_;
v___y_1827_ = v_suppressElabErrors_1839_;
v___y_1828_ = v_ref_1842_;
v___y_1829_ = v___y_1836_;
v___y_1830_ = v___y_1835_;
v___y_1831_ = v_val_1845_;
goto v___jp_1824_;
}
}
v___jp_1847_:
{
uint8_t v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = 1;
v___x_1850_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1753_, v___x_1849_);
if (v___x_1850_ == 0)
{
v___y_1835_ = v___y_1848_;
v___y_1836_ = v_severity_1753_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1851_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1757_);
v___x_1852_ = l_Lean_warningAsError;
v___x_1853_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v___x_1851_, v___x_1852_);
lean_dec_ref(v___x_1851_);
if (v___x_1853_ == 0)
{
v___y_1835_ = v___y_1848_;
v___y_1836_ = v_severity_1753_;
goto v___jp_1834_;
}
else
{
v___y_1835_ = v___y_1848_;
v___y_1836_ = v___x_1846_;
goto v___jp_1834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___boxed(lean_object* v_ref_1858_, lean_object* v_msgData_1859_, lean_object* v_severity_1860_, lean_object* v_isSilent_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
uint8_t v_severity_boxed_1867_; uint8_t v_isSilent_boxed_1868_; lean_object* v_res_1869_; 
v_severity_boxed_1867_ = lean_unbox(v_severity_1860_);
v_isSilent_boxed_1868_ = lean_unbox(v_isSilent_1861_);
v_res_1869_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1858_, v_msgData_1859_, v_severity_boxed_1867_, v_isSilent_boxed_1868_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v_ref_1858_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(lean_object* v_ref_1870_, lean_object* v_msgData_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
uint8_t v___x_1877_; uint8_t v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = 2;
v___x_1878_ = 0;
v___x_1879_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1870_, v_msgData_1871_, v___x_1877_, v___x_1878_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1___boxed(lean_object* v_ref_1880_, lean_object* v_msgData_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_ref_1880_, v_msgData_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v_ref_1880_);
return v_res_1887_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1));
v___x_1892_ = l_Lean_MessageData_ofFormat(v___x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2);
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4));
v___x_1897_ = l_Lean_stringToMessageData(v___x_1896_);
return v___x_1897_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6));
v___x_1900_ = l_Lean_stringToMessageData(v___x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1902_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_1903_ = lean_unsigned_to_nat(57u);
v___x_1904_ = lean_unsigned_to_nat(133u);
v___x_1905_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8));
v___x_1906_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_1907_ = l_mkPanicMessageWithDecl(v___x_1906_, v___x_1905_, v___x_1904_, v___x_1903_, v___x_1902_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object* v_steps_1908_, lean_object* v_expectedType_1909_, lean_object* v_result_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lean_Elab_Term_instInhabitedCalcStepView_default));
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc_ref(v_result_1910_);
v___x_1917_ = lean_infer_type(v_result_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___x_1944_; lean_object* v_a_1945_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_1918_, v_a_1912_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = l_Lean_Expr_headBeta(v_a_1920_);
v___x_1944_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_1921_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1944_);
if (lean_obj_tag(v_a_1945_) == 1)
{
lean_object* v_val_1946_; lean_object* v_snd_1947_; lean_object* v_fst_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_2192_; 
v_val_1946_ = lean_ctor_get(v_a_1945_, 0);
lean_inc(v_val_1946_);
lean_dec_ref_known(v_a_1945_, 1);
v_snd_1947_ = lean_ctor_get(v_val_1946_, 1);
v_fst_1948_ = lean_ctor_get(v_val_1946_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_val_1946_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_1950_ = v_val_1946_;
v_isShared_1951_ = v_isSharedCheck_2192_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snd_1947_);
lean_inc(v_fst_1948_);
lean_dec(v_val_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_2192_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_fst_1952_; lean_object* v_snd_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_2191_; 
v_fst_1952_ = lean_ctor_get(v_snd_1947_, 0);
v_snd_1953_ = lean_ctor_get(v_snd_1947_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_snd_1947_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_1955_ = v_snd_1947_;
v_isShared_1956_ = v_isSharedCheck_2191_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_snd_1953_);
lean_inc(v_fst_1952_);
lean_dec(v_snd_1947_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_2191_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; lean_object* v_a_1958_; 
v___x_1957_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_expectedType_1909_);
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___x_1957_);
if (lean_obj_tag(v_a_1958_) == 1)
{
lean_object* v_val_1959_; lean_object* v_snd_1960_; lean_object* v_fst_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2190_; 
v_val_1959_ = lean_ctor_get(v_a_1958_, 0);
lean_inc(v_val_1959_);
lean_dec_ref_known(v_a_1958_, 1);
v_snd_1960_ = lean_ctor_get(v_val_1959_, 1);
v_fst_1961_ = lean_ctor_get(v_val_1959_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_val_1959_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_1963_ = v_val_1959_;
v_isShared_1964_ = v_isSharedCheck_2190_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_snd_1960_);
lean_inc(v_fst_1961_);
lean_dec(v_val_1959_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2190_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_fst_1965_; lean_object* v_snd_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2189_; 
v_fst_1965_ = lean_ctor_get(v_snd_1960_, 0);
v_snd_1966_ = lean_ctor_get(v_snd_1960_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_snd_1960_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_1968_ = v_snd_1960_;
v_isShared_1969_ = v_isSharedCheck_2189_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_snd_1966_);
lean_inc(v_fst_1965_);
lean_dec(v_snd_1960_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2189_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
uint8_t v_failed_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1948_, v_fst_1961_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; uint8_t v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = lean_unbox(v_a_2082_);
if (v___x_2083_ == 0)
{
lean_dec(v_a_2082_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_dec(v_fst_1965_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_dec(v_fst_1952_);
lean_del_object(v___x_1950_);
v___y_1923_ = v_a_1911_;
v___y_1924_ = v_a_1912_;
v___y_1925_ = v_a_1913_;
v___y_1926_ = v_a_1914_;
goto v___jp_1922_;
}
else
{
uint8_t v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = 0;
lean_inc(v_fst_1965_);
lean_inc(v_fst_1952_);
v___x_2085_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1952_, v_fst_1965_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; uint8_t v___x_2087_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2087_ = lean_unbox(v_a_2086_);
lean_dec(v_a_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_1952_, v_fst_1965_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v_fst_2090_; lean_object* v_snd_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2164_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v_fst_2090_ = lean_ctor_get(v_a_2089_, 0);
v_snd_2091_ = lean_ctor_get(v_a_2089_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_a_2089_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2093_ = v_a_2089_;
v_isShared_2094_ = v_isSharedCheck_2164_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_snd_2091_);
lean_inc(v_fst_2090_);
lean_dec(v_a_2089_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2164_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; 
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc(v_fst_2090_);
v___x_2095_ = lean_infer_type(v_fst_2090_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc(v_snd_2091_);
v___x_2097_ = lean_infer_type(v_snd_2091_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2096_, v_a_2098_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v_fst_2101_; lean_object* v_snd_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2139_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v_fst_2101_ = lean_ctor_get(v_a_2100_, 0);
v_snd_2102_ = lean_ctor_get(v_a_2100_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_a_2100_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2104_ = v_a_2100_;
v_isShared_2105_ = v_isSharedCheck_2139_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_snd_2102_);
lean_inc(v_fst_2101_);
lean_dec(v_a_2100_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2139_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v_term_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = lean_array_get_borrowed(v___x_1916_, v_steps_1908_, v___x_2106_);
v_term_2108_ = lean_ctor_get(v___x_2107_, 1);
v___x_2109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_2110_ = l_Lean_MessageData_ofExpr(v_fst_2090_);
v___x_2111_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 7);
lean_ctor_set(v___x_2104_, 1, v___x_2111_);
lean_ctor_set(v___x_2104_, 0, v___x_2110_);
v___x_2113_ = v___x_2104_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = l_Lean_MessageData_ofExpr(v_fst_2101_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set_tag(v___x_2093_, 7);
lean_ctor_set(v___x_2093_, 1, v___x_2114_);
lean_ctor_set(v___x_2093_, 0, v___x_2113_);
v___x_2116_ = v___x_2093_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2117_ = l_Lean_indentD(v___x_2116_);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2109_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
v___x_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = l_Lean_MessageData_ofExpr(v_snd_2091_);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___x_2111_);
v___x_2123_ = l_Lean_MessageData_ofExpr(v_snd_2102_);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = l_Lean_indentD(v___x_2124_);
v___x_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2120_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2108_, v___x_2126_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_2127_) == 0)
{
uint8_t v___x_2128_; 
lean_dec_ref_known(v___x_2127_, 1);
v___x_2128_ = lean_unbox(v_a_2082_);
lean_dec(v_a_2082_);
v_failed_1971_ = v___x_2128_;
v___y_1972_ = v_a_1911_;
v___y_1973_ = v_a_1912_;
v___y_1974_ = v_a_1913_;
v___y_1975_ = v_a_1914_;
goto v___jp_1970_;
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v_a_2082_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v_a_2129_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2127_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2127_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_del_object(v___x_2093_);
lean_dec(v_snd_2091_);
lean_dec(v_fst_2090_);
lean_dec(v_a_2082_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v_a_2140_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2099_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2099_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2096_);
lean_del_object(v___x_2093_);
lean_dec(v_snd_2091_);
lean_dec(v_fst_2090_);
lean_dec(v_a_2082_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v_a_2148_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2097_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2097_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_del_object(v___x_2093_);
lean_dec(v_snd_2091_);
lean_dec(v_fst_2090_);
lean_dec(v_a_2082_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v_a_2156_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2095_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2095_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec(v_a_2082_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v_a_2165_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2088_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2088_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_dec(v_a_2082_);
lean_dec(v_fst_1965_);
lean_dec(v_fst_1952_);
v_failed_1971_ = v___x_2084_;
v___y_1972_ = v_a_1911_;
v___y_1973_ = v_a_1912_;
v___y_1974_ = v_a_1913_;
v___y_1975_ = v_a_1914_;
goto v___jp_1970_;
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2082_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_dec(v_fst_1965_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_dec(v_fst_1952_);
lean_del_object(v___x_1950_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v_a_2173_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2085_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2085_);
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
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_dec(v_fst_1965_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_dec(v_fst_1952_);
lean_del_object(v___x_1950_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v_a_2181_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2081_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2081_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
v___jp_1970_:
{
lean_object* v___x_1976_; 
lean_inc(v_snd_1966_);
lean_inc(v_snd_1953_);
v___x_1976_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_1953_, v_snd_1966_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; uint8_t v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1978_ = lean_unbox(v_a_1977_);
lean_dec(v_a_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v___x_1979_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_snd_1953_, v_snd_1966_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v_fst_1981_; lean_object* v_snd_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2064_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v_fst_1981_ = lean_ctor_get(v_a_1980_, 0);
v_snd_1982_ = lean_ctor_get(v_a_1980_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_a_1980_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_1984_ = v_a_1980_;
v_isShared_1985_ = v_isSharedCheck_2064_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_snd_1982_);
lean_inc(v_fst_1981_);
lean_dec(v_a_1980_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2064_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; 
lean_inc(v___y_1975_);
lean_inc_ref(v___y_1974_);
lean_inc(v___y_1973_);
lean_inc_ref(v___y_1972_);
lean_inc(v_fst_1981_);
v___x_1986_ = lean_infer_type(v_fst_1981_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1988_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
lean_inc(v___y_1975_);
lean_inc_ref(v___y_1974_);
lean_inc(v___y_1973_);
lean_inc_ref(v___y_1972_);
lean_inc(v_snd_1982_);
v___x_1988_ = lean_infer_type(v_snd_1982_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_1987_, v_a_1989_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v_fst_1992_; lean_object* v_snd_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2039_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v_fst_1992_ = lean_ctor_get(v_a_1991_, 0);
v_snd_1993_ = lean_ctor_get(v_a_1991_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_a_1991_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_1995_ = v_a_1991_;
v_isShared_1996_ = v_isSharedCheck_2039_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_snd_1993_);
lean_inc(v_fst_1992_);
lean_dec(v_a_1991_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2039_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v_term_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_1997_ = lean_array_get_size(v_steps_1908_);
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = lean_nat_sub(v___x_1997_, v___x_1998_);
v___x_2000_ = lean_array_get_borrowed(v___x_1916_, v_steps_1908_, v___x_1999_);
lean_dec(v___x_1999_);
v_term_2001_ = lean_ctor_get(v___x_2000_, 1);
v___x_2002_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5);
v___x_2003_ = l_Lean_MessageData_ofExpr(v_fst_1981_);
v___x_2004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_1996_ == 0)
{
lean_ctor_set_tag(v___x_1995_, 7);
lean_ctor_set(v___x_1995_, 1, v___x_2004_);
lean_ctor_set(v___x_1995_, 0, v___x_2003_);
v___x_2006_ = v___x_1995_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = l_Lean_MessageData_ofExpr(v_fst_1992_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 7);
lean_ctor_set(v___x_1984_, 1, v___x_2007_);
lean_ctor_set(v___x_1984_, 0, v___x_2006_);
v___x_2009_ = v___x_1984_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = l_Lean_indentD(v___x_2009_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 7);
lean_ctor_set(v___x_1968_, 1, v___x_2010_);
lean_ctor_set(v___x_1968_, 0, v___x_2002_);
v___x_2012_ = v___x_1968_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
if (v_isShared_1964_ == 0)
{
lean_ctor_set_tag(v___x_1963_, 7);
lean_ctor_set(v___x_1963_, 1, v___x_2013_);
lean_ctor_set(v___x_1963_, 0, v___x_2012_);
v___x_2015_ = v___x_1963_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = l_Lean_MessageData_ofExpr(v_snd_1982_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set_tag(v___x_1955_, 7);
lean_ctor_set(v___x_1955_, 1, v___x_2004_);
lean_ctor_set(v___x_1955_, 0, v___x_2016_);
v___x_2018_ = v___x_1955_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2004_);
v___x_2018_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = l_Lean_MessageData_ofExpr(v_snd_1993_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set_tag(v___x_1950_, 7);
lean_ctor_set(v___x_1950_, 1, v___x_2019_);
lean_ctor_set(v___x_1950_, 0, v___x_2018_);
v___x_2021_ = v___x_1950_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = l_Lean_indentD(v___x_2021_);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2015_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2001_, v___x_2023_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_dec_ref_known(v___x_2024_, 1);
v___y_1931_ = v___y_1972_;
v___y_1932_ = v___y_1973_;
v___y_1933_ = v___y_1974_;
v___y_1934_ = v___y_1975_;
goto v___jp_1930_;
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
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
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_del_object(v___x_1984_);
lean_dec(v_snd_1982_);
lean_dec(v_fst_1981_);
lean_del_object(v___x_1968_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_del_object(v___x_1950_);
v_a_2040_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1990_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_1990_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_a_1987_);
lean_del_object(v___x_1984_);
lean_dec(v_snd_1982_);
lean_dec(v_fst_1981_);
lean_del_object(v___x_1968_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_del_object(v___x_1950_);
v_a_2048_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_1988_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_1988_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_del_object(v___x_1984_);
lean_dec(v_snd_1982_);
lean_dec(v_fst_1981_);
lean_del_object(v___x_1968_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_del_object(v___x_1950_);
v_a_2056_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_1986_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_1986_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_del_object(v___x_1968_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_del_object(v___x_1950_);
v_a_2065_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_1979_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_1979_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_del_object(v___x_1950_);
if (v_failed_1971_ == 0)
{
v___y_1923_ = v___y_1972_;
v___y_1924_ = v___y_1973_;
v___y_1925_ = v___y_1974_;
v___y_1926_ = v___y_1975_;
goto v___jp_1922_;
}
else
{
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v___y_1931_ = v___y_1972_;
v___y_1932_ = v___y_1973_;
v___y_1933_ = v___y_1974_;
v___y_1934_ = v___y_1975_;
goto v___jp_1930_;
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_del_object(v___x_1950_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v_a_2073_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_1976_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_1976_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1958_);
lean_del_object(v___x_1955_);
lean_dec(v_snd_1953_);
lean_dec(v_fst_1952_);
lean_del_object(v___x_1950_);
lean_dec(v_fst_1948_);
v___y_1923_ = v_a_1911_;
v___y_1924_ = v_a_1912_;
v___y_1925_ = v_a_1913_;
v___y_1926_ = v_a_1914_;
goto v___jp_1922_;
}
}
}
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_dec(v_a_1945_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v___x_2193_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9);
v___x_2194_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v___x_2193_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
return v___x_2194_;
}
v___jp_1922_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3);
v___x_1928_ = lean_box(0);
v___x_1929_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1927_, v_expectedType_1909_, v___x_1921_, v_result_1910_, v___x_1928_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
return v___x_1929_;
}
v___jp_1930_:
{
lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v___x_1935_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec_ref(v_result_1910_);
lean_dec_ref(v_expectedType_1909_);
v_a_2195_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_1917_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_1917_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(lean_object* v_steps_2203_, lean_object* v_expectedType_2204_, lean_object* v_result_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2203_, v_expectedType_2204_, v_result_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_steps_2203_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure(lean_object* v_00_u03b1_2212_, lean_object* v_steps_2213_, lean_object* v_expectedType_2214_, lean_object* v_result_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2213_, v_expectedType_2214_, v_result_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___boxed(lean_object* v_00_u03b1_2222_, lean_object* v_steps_2223_, lean_object* v_expectedType_2224_, lean_object* v_result_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Elab_Term_throwCalcFailure(v_00_u03b1_2222_, v_steps_2223_, v_expectedType_2224_, v_result_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec_ref(v_steps_2223_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0(lean_object* v_a_2232_, lean_object* v_x_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2232_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0___boxed(lean_object* v_a_2242_, lean_object* v_x_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Elab_Term_elabCalc___lam__0(v_a_2242_, v_x_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v_x_2243_);
lean_dec_ref(v_a_2242_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1(lean_object* v_a_2252_, lean_object* v_x_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2252_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1___boxed(lean_object* v_a_2262_, lean_object* v_x_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Elab_Term_elabCalc___lam__1(v_a_2262_, v_x_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v_x_2263_);
lean_dec_ref(v_a_2262_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object* v_x_2276_, lean_object* v_x_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
lean_inc(v_x_2276_);
v___x_2286_ = l_Lean_Syntax_isOfKind(v_x_2276_, v___x_2285_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
lean_dec(v_x_2277_);
lean_dec(v_x_2276_);
v___x_2287_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; lean_object* v_steps_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2288_ = lean_unsigned_to_nat(1u);
v_steps_2289_ = l_Lean_Syntax_getArg(v_x_2276_, v___x_2288_);
v___x_2290_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_2289_);
v___x_2291_ = l_Lean_Syntax_isOfKind(v_steps_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; 
lean_dec(v_steps_2289_);
lean_dec(v_x_2277_);
lean_dec(v_x_2276_);
v___x_2292_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2292_;
}
else
{
lean_object* v_toCold_2293_; lean_object* v_currRecDepth_2294_; lean_object* v_ref_2295_; uint16_t v_optionFlags_2296_; uint8_t v_suppressElabErrors_2297_; uint8_t v_checkDeprecated_2298_; uint8_t v_isRecordingDeps_2299_; lean_object* v___x_2300_; lean_object* v_tk_2301_; lean_object* v_ref_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_toCold_2293_ = lean_ctor_get(v_a_2282_, 0);
v_currRecDepth_2294_ = lean_ctor_get(v_a_2282_, 1);
v_ref_2295_ = lean_ctor_get(v_a_2282_, 2);
v_optionFlags_2296_ = lean_ctor_get_uint16(v_a_2282_, sizeof(void*)*3);
v_suppressElabErrors_2297_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*3 + 2);
v_checkDeprecated_2298_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2299_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*3 + 4);
v___x_2300_ = lean_unsigned_to_nat(0u);
v_tk_2301_ = l_Lean_Syntax_getArg(v_x_2276_, v___x_2300_);
lean_dec(v_x_2276_);
v_ref_2302_ = l_Lean_replaceRef(v_tk_2301_, v_ref_2295_);
lean_dec(v_tk_2301_);
lean_inc(v_currRecDepth_2294_);
lean_inc_ref(v_toCold_2293_);
v___x_2303_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2303_, 0, v_toCold_2293_);
lean_ctor_set(v___x_2303_, 1, v_currRecDepth_2294_);
lean_ctor_set(v___x_2303_, 2, v_ref_2302_);
lean_ctor_set_uint16(v___x_2303_, sizeof(void*)*3, v_optionFlags_2296_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*3 + 2, v_suppressElabErrors_2297_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*3 + 3, v_checkDeprecated_2298_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*3 + 4, v_isRecordingDeps_2299_);
v___x_2304_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_2289_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v___x_2303_, v_a_2283_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___f_2306_; lean_object* v___f_2307_; lean_object* v___x_2308_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc_n(v_a_2305_, 3);
lean_dec_ref_known(v___x_2304_, 1);
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2306_, 0, v_a_2305_);
v___f_2307_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__1___boxed), 9, 1);
lean_closure_set(v___f_2307_, 0, v_a_2305_);
v___x_2308_ = l_Lean_Elab_Term_elabCalcSteps(v_a_2305_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v___x_2303_, v_a_2283_);
lean_dec(v_a_2305_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v_fst_2310_; lean_object* v___x_2311_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v_fst_2310_ = lean_ctor_get(v_a_2309_, 0);
lean_inc(v_fst_2310_);
lean_dec(v_a_2309_);
v___x_2311_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(v_x_2277_, v_fst_2310_, v___f_2306_, v___f_2307_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v___x_2303_, v_a_2283_);
lean_dec_ref_known(v___x_2303_, 3);
return v___x_2311_;
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v___f_2307_);
lean_dec_ref(v___f_2306_);
lean_dec_ref_known(v___x_2303_, 3);
lean_dec(v_x_2277_);
v_a_2312_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2308_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2308_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref_known(v___x_2303_, 3);
lean_dec(v_x_2277_);
v_a_2320_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2304_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2304_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object* v_x_2328_, lean_object* v_x_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Elab_Term_elabCalc(v_x_2328_, v_x_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1(){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2345_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2346_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
v___x_2347_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2348_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___boxed), 9, 0);
v___x_2349_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2345_, v___x_2346_, v___x_2347_, v___x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___boxed(lean_object* v_a_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3(){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2355_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0));
v___x_2356_ = l_Lean_addBuiltinDocString(v___x_2354_, v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___boxed(lean_object* v_a_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5(){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2386_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6));
v___x_2387_ = l_Lean_addBuiltinDeclarationRanges(v___x_2385_, v___x_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___boxed(lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
return v_res_2389_;
}
}
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Calc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Calc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_App(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Calc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Calc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Calc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Calc(builtin);
}
#ifdef __cplusplus
}
#endif
