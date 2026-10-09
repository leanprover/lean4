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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg(lean_object* v_e_1_){
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
LEAN_EXPORT void l_Lean_Elab_Term_getCalcRelation_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_e_1_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg___boxed(lean_object* v_e_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_e_17_);
lean_dec_ref(v_e_17_);
return v_res_19_;
}
}
lean_object* l_Lean_Elab_Term_getCalcRelation_x3f(lean_object* v_e_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_e_20_);
return v___x_26_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_getCalcRelation_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_20_ = stack[0].m_obj;
lean_object* v_a_21_ = stack[1].m_obj;
lean_object* v_a_22_ = stack[2].m_obj;
lean_object* v_a_23_ = stack[3].m_obj;
lean_object* v_a_24_ = stack[4].m_obj;
lean_object* v_res_27_;
v_res_27_ = l_Lean_Elab_Term_getCalcRelation_x3f(v_e_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___boxed(lean_object* v_e_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Elab_Term_getCalcRelation_x3f(v_e_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec_ref(v_e_28_);
return v_res_34_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(lean_object* v_k_35_, lean_object* v_b_36_, lean_object* v_c_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; 
lean_inc(v___y_41_);
lean_inc_ref(v___y_40_);
lean_inc(v___y_39_);
lean_inc_ref(v___y_38_);
v___x_43_ = lean_apply_7(v_k_35_, v_b_36_, v_c_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_35_ = stack[0].m_obj;
lean_object* v_b_36_ = stack[1].m_obj;
lean_object* v_c_37_ = stack[2].m_obj;
lean_object* v___y_38_ = stack[3].m_obj;
lean_object* v___y_39_ = stack[4].m_obj;
lean_object* v___y_40_ = stack[5].m_obj;
lean_object* v___y_41_ = stack[6].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(v_k_35_, v_b_36_, v_c_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed(lean_object* v_k_45_, lean_object* v_b_46_, lean_object* v_c_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(v_k_45_, v_b_46_, v_c_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
return v_res_53_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(lean_object* v_type_54_, lean_object* v_k_55_, uint8_t v_cleanupAnnotations_56_, uint8_t v_whnfType_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___f_63_; lean_object* v___x_64_; 
v___f_63_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_63_, 0, v_k_55_);
v___x_64_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_54_, v___f_63_, v_cleanupAnnotations_56_, v_whnfType_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_a_73_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_64_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_64_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_54_ = stack[0].m_obj;
lean_object* v_k_55_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_56_ = stack[2].m_num;
uint8_t v_whnfType_57_ = stack[3].m_num;
lean_object* v___y_58_ = stack[4].m_obj;
lean_object* v___y_59_ = stack[5].m_obj;
lean_object* v___y_60_ = stack[6].m_obj;
lean_object* v___y_61_ = stack[7].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_type_54_, v_k_55_, v_cleanupAnnotations_56_, v_whnfType_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___boxed(lean_object* v_type_82_, lean_object* v_k_83_, lean_object* v_cleanupAnnotations_84_, lean_object* v_whnfType_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_91_; uint8_t v_whnfType_boxed_92_; lean_object* v_res_93_; 
v_cleanupAnnotations_boxed_91_ = lean_unbox(v_cleanupAnnotations_84_);
v_whnfType_boxed_92_ = lean_unbox(v_whnfType_85_);
v_res_93_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_type_82_, v_k_83_, v_cleanupAnnotations_boxed_91_, v_whnfType_boxed_92_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
return v_res_93_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(lean_object* v_00_u03b1_94_, lean_object* v_type_95_, lean_object* v_k_96_, uint8_t v_cleanupAnnotations_97_, uint8_t v_whnfType_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_type_95_, v_k_96_, v_cleanupAnnotations_97_, v_whnfType_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_95_ = stack[1].m_obj;
lean_object* v_k_96_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_97_ = stack[3].m_num;
uint8_t v_whnfType_98_ = stack[4].m_num;
lean_object* v___y_99_ = stack[5].m_obj;
lean_object* v___y_100_ = stack[6].m_obj;
lean_object* v___y_101_ = stack[7].m_obj;
lean_object* v___y_102_ = stack[8].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(lean_box(0), v_type_95_, v_k_96_, v_cleanupAnnotations_97_, v_whnfType_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___boxed(lean_object* v_00_u03b1_106_, lean_object* v_type_107_, lean_object* v_k_108_, lean_object* v_cleanupAnnotations_109_, lean_object* v_whnfType_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_116_; uint8_t v_whnfType_boxed_117_; lean_object* v_res_118_; 
v_cleanupAnnotations_boxed_116_ = lean_unbox(v_cleanupAnnotations_109_);
v_whnfType_boxed_117_ = lean_unbox(v_whnfType_110_);
v_res_118_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(v_00_u03b1_106_, v_type_107_, v_k_108_, v_cleanupAnnotations_boxed_116_, v_whnfType_boxed_117_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_118_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(lean_object* v_msgData_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___x_125_; lean_object* v_env_126_; uint8_t v___x_127_; lean_object* v_env_128_; lean_object* v___x_129_; lean_object* v_toCold_130_; lean_object* v_mctx_131_; lean_object* v_lctx_132_; lean_object* v_options_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_125_ = lean_st_ref_get(v___y_123_);
v_env_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc_ref(v_env_126_);
lean_dec(v___x_125_);
v___x_127_ = 0;
v_env_128_ = l_Lean_Environment_setRecordingDeps(v_env_126_, v___x_127_);
v___x_129_ = lean_st_ref_get(v___y_121_);
v_toCold_130_ = lean_ctor_get(v___y_122_, 0);
v_mctx_131_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_mctx_131_);
lean_dec(v___x_129_);
v_lctx_132_ = lean_ctor_get(v___y_120_, 2);
v_options_133_ = lean_ctor_get(v_toCold_130_, 2);
lean_inc_ref(v_options_133_);
lean_inc_ref(v_lctx_132_);
v___x_134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_134_, 0, v_env_128_);
lean_ctor_set(v___x_134_, 1, v_mctx_131_);
lean_ctor_set(v___x_134_, 2, v_lctx_132_);
lean_ctor_set(v___x_134_, 3, v_options_133_);
v___x_135_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_msgData_119_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_119_ = stack[0].m_obj;
lean_object* v___y_120_ = stack[1].m_obj;
lean_object* v___y_121_ = stack[2].m_obj;
lean_object* v___y_122_ = stack[3].m_obj;
lean_object* v___y_123_ = stack[4].m_obj;
lean_object* v_res_137_;
v_res_137_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msgData_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0___boxed(lean_object* v_msgData_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msgData_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_144_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_ref_151_; lean_object* v___x_152_; lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_161_; 
v_ref_151_ = lean_ctor_get(v___y_148_, 2);
v___x_152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_161_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
lean_inc(v_ref_151_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_ref_151_);
lean_ctor_set(v___x_157_, 1, v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 1);
lean_ctor_set(v___x_155_, 0, v___x_157_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_145_ = stack[0].m_obj;
lean_object* v___y_146_ = stack[1].m_obj;
lean_object* v___y_147_ = stack[2].m_obj;
lean_object* v___y_148_ = stack[3].m_obj;
lean_object* v___y_149_ = stack[4].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg___boxed(lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_169_;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0));
v___x_172_ = l_Lean_stringToMessageData(v___x_171_);
return v___x_172_;
}
}
lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(lean_object* v_a_173_, lean_object* v_x_174_, lean_object* v_sort_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
lean_inc(v___y_179_);
lean_inc_ref(v___y_178_);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
v___x_181_ = lean_whnf(v_sort_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_194_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_194_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_194_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_194_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
if (lean_obj_tag(v_a_182_) == 3)
{
lean_object* v_u_186_; lean_object* v___x_188_; 
lean_dec_ref(v_a_173_);
v_u_186_ = lean_ctor_get(v_a_182_, 0);
lean_inc(v_u_186_);
lean_dec_ref_known(v_a_182_, 1);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v_u_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_u_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
lean_del_object(v___x_184_);
lean_dec(v_a_182_);
v___x_190_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1);
v___x_191_ = l_Lean_indentExpr(v_a_173_);
v___x_192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_192_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
return v___x_193_;
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec_ref(v_a_173_);
v_a_195_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_181_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_181_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_173_ = stack[0].m_obj;
lean_object* v_x_174_ = stack[1].m_obj;
lean_object* v_sort_175_ = stack[2].m_obj;
lean_object* v___y_176_ = stack[3].m_obj;
lean_object* v___y_177_ = stack[4].m_obj;
lean_object* v___y_178_ = stack[5].m_obj;
lean_object* v___y_179_ = stack[6].m_obj;
lean_object* v_res_203_;
v_res_203_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(v_a_173_, v_x_174_, v_sort_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
stack->m_obj
 = v_res_203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed(lean_object* v_a_204_, lean_object* v_x_205_, lean_object* v_sort_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(v_a_204_, v_x_205_, v_sort_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec_ref(v_x_205_);
return v_res_212_;
}
}
lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(lean_object* v_r_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_219_; 
lean_inc(v_a_217_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_215_);
lean_inc_ref(v_a_214_);
v___x_219_ = lean_infer_type(v_r_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___f_221_; uint8_t v___x_222_; lean_object* v___x_223_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc_n(v_a_220_, 2);
lean_dec_ref_known(v___x_219_, 1);
v___f_221_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed), 8, 1);
lean_closure_set(v___f_221_, 0, v_a_220_);
v___x_222_ = 0;
v___x_223_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_a_220_, v___f_221_, v___x_222_, v___x_222_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_223_;
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v_a_224_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_219_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_219_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_213_ = stack[0].m_obj;
lean_object* v_a_214_ = stack[1].m_obj;
lean_object* v_a_215_ = stack[2].m_obj;
lean_object* v_a_216_ = stack[3].m_obj;
lean_object* v_a_217_ = stack[4].m_obj;
lean_object* v_res_232_;
v_res_232_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_r_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___boxed(lean_object* v_r_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_r_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_239_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(lean_object* v_00_u03b1_240_, lean_object* v_msg_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_241_ = stack[1].m_obj;
lean_object* v___y_242_ = stack[2].m_obj;
lean_object* v___y_243_ = stack[3].m_obj;
lean_object* v___y_244_ = stack[4].m_obj;
lean_object* v___y_245_ = stack[5].m_obj;
lean_object* v_res_248_;
v_res_248_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(lean_box(0), v_msg_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___boxed(lean_object* v_00_u03b1_249_, lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(v_00_u03b1_249_, v_msg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_256_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(lean_object* v_e_257_, lean_object* v___y_258_){
_start:
{
uint8_t v___x_260_; 
v___x_260_ = l_Lean_Expr_hasMVar(v_e_257_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v_e_257_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v_mctx_263_; lean_object* v___x_264_; lean_object* v_fst_265_; lean_object* v_snd_266_; lean_object* v___x_267_; lean_object* v_cache_268_; lean_object* v_zetaDeltaFVarIds_269_; lean_object* v_postponed_270_; lean_object* v_diag_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_280_; 
v___x_262_ = lean_st_ref_get(v___y_258_);
v_mctx_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc_ref(v_mctx_263_);
lean_dec(v___x_262_);
v___x_264_ = l_Lean_instantiateMVarsCore(v_mctx_263_, v_e_257_);
v_fst_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_fst_265_);
v_snd_266_ = lean_ctor_get(v___x_264_, 1);
lean_inc(v_snd_266_);
lean_dec_ref(v___x_264_);
v___x_267_ = lean_st_ref_take(v___y_258_);
v_cache_268_ = lean_ctor_get(v___x_267_, 1);
v_zetaDeltaFVarIds_269_ = lean_ctor_get(v___x_267_, 2);
v_postponed_270_ = lean_ctor_get(v___x_267_, 3);
v_diag_271_ = lean_ctor_get(v___x_267_, 4);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v___x_267_, 0);
lean_dec(v_unused_281_);
v___x_273_ = v___x_267_;
v_isShared_274_ = v_isSharedCheck_280_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_diag_271_);
lean_inc(v_postponed_270_);
lean_inc(v_zetaDeltaFVarIds_269_);
lean_inc(v_cache_268_);
lean_dec(v___x_267_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_280_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v_snd_266_);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_snd_266_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_cache_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_zetaDeltaFVarIds_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_postponed_270_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_diag_271_);
v___x_276_ = v_reuseFailAlloc_279_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_st_ref_put(v___y_258_, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_fst_265_);
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_257_ = stack[0].m_obj;
lean_object* v___y_258_ = stack[1].m_obj;
lean_object* v_res_282_;
v_res_282_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_e_257_, v___y_258_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg___boxed(lean_object* v_e_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_e_283_, v___y_284_);
lean_dec(v___y_284_);
return v_res_286_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(lean_object* v_e_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_e_287_, v___y_289_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_287_ = stack[0].m_obj;
lean_object* v___y_288_ = stack[1].m_obj;
lean_object* v___y_289_ = stack[2].m_obj;
lean_object* v___y_290_ = stack[3].m_obj;
lean_object* v___y_291_ = stack[4].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(v_e_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___boxed(lean_object* v_e_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(v_e_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_301_;
}
}
lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___f_309_; lean_object* v___x_7150__overap_310_; lean_object* v___x_311_; 
v___f_309_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_7150__overap_310_ = lean_panic_fn_borrowed(v___f_309_, v_msg_303_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
v___x_311_ = lean_apply_5(v___x_7150__overap_310_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, lean_box(0));
return v___x_311_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_303_ = stack[0].m_obj;
lean_object* v___y_304_ = stack[1].m_obj;
lean_object* v___y_305_ = stack[2].m_obj;
lean_object* v___y_306_ = stack[3].m_obj;
lean_object* v___y_307_ = stack[4].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v_msg_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___boxed(lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v_msg_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__5(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__4));
v___x_329_ = l_Lean_stringToMessageData(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__7(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__6));
v___x_332_ = l_Lean_stringToMessageData(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__11(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_336_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_337_ = lean_unsigned_to_nat(72u);
v___x_338_ = lean_unsigned_to_nat(35u);
v___x_339_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__9));
v___x_340_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_341_ = l_mkPanicMessageWithDecl(v___x_340_, v___x_339_, v___x_338_, v___x_337_, v___x_336_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__12(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_342_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_343_ = lean_unsigned_to_nat(53u);
v___x_344_ = lean_unsigned_to_nat(34u);
v___x_345_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__9));
v___x_346_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_347_ = l_mkPanicMessageWithDecl(v___x_346_, v___x_345_, v___x_344_, v___x_343_, v___x_342_);
return v___x_347_;
}
}
lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object* v_result_348_, lean_object* v_resultType_349_, lean_object* v_step_350_, lean_object* v_stepType_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; lean_object* v_a_358_; 
v___x_357_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_resultType_349_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
if (lean_obj_tag(v_a_358_) == 1)
{
lean_object* v_val_359_; lean_object* v_snd_360_; lean_object* v_fst_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_617_; 
v_val_359_ = lean_ctor_get(v_a_358_, 0);
lean_inc(v_val_359_);
lean_dec_ref_known(v_a_358_, 1);
v_snd_360_ = lean_ctor_get(v_val_359_, 1);
v_fst_361_ = lean_ctor_get(v_val_359_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_val_359_);
if (v_isSharedCheck_617_ == 0)
{
v___x_363_ = v_val_359_;
v_isShared_364_ = v_isSharedCheck_617_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_snd_360_);
lean_inc(v_fst_361_);
lean_dec(v_val_359_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_617_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v_fst_365_; lean_object* v_snd_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_616_; 
v_fst_365_ = lean_ctor_get(v_snd_360_, 0);
v_snd_366_ = lean_ctor_get(v_snd_360_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_snd_360_);
if (v_isSharedCheck_616_ == 0)
{
v___x_368_ = v_snd_360_;
v_isShared_369_ = v_isSharedCheck_616_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snd_366_);
lean_inc(v_fst_365_);
lean_dec(v_snd_360_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_616_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_372_; lean_object* v_a_373_; 
v___x_370_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_stepType_351_, v_a_353_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref(v___x_370_);
v___x_372_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_371_);
lean_dec(v_a_371_);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref(v___x_372_);
if (lean_obj_tag(v_a_373_) == 1)
{
lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_613_; 
v_val_374_ = lean_ctor_get(v_a_373_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v_a_373_);
if (v_isSharedCheck_613_ == 0)
{
v___x_376_ = v_a_373_;
v_isShared_377_ = v_isSharedCheck_613_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_dec(v_a_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_613_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v_snd_378_; lean_object* v_fst_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_612_; 
v_snd_378_ = lean_ctor_get(v_val_374_, 1);
v_fst_379_ = lean_ctor_get(v_val_374_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v_val_374_);
if (v_isSharedCheck_612_ == 0)
{
v___x_381_ = v_val_374_;
v_isShared_382_ = v_isSharedCheck_612_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snd_378_);
lean_inc(v_fst_379_);
lean_dec(v_val_374_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_612_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_snd_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_610_; 
v_snd_383_ = lean_ctor_get(v_snd_378_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_snd_378_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_snd_378_, 0);
lean_dec(v_unused_611_);
v___x_385_ = v_snd_378_;
v_isShared_386_ = v_isSharedCheck_610_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_snd_383_);
lean_dec(v_snd_378_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_610_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; 
lean_inc(v_fst_361_);
v___x_387_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_fst_361_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
lean_inc(v_fst_379_);
v___x_389_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_fst_379_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_391_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
lean_inc(v_a_355_);
lean_inc_ref(v_a_354_);
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
lean_inc(v_fst_365_);
v___x_391_ = lean_infer_type(v_fst_365_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
lean_inc(v_a_355_);
lean_inc_ref(v_a_354_);
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
lean_inc(v_snd_366_);
v___x_393_ = lean_infer_type(v_snd_366_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_395_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
lean_inc(v_a_355_);
lean_inc_ref(v_a_354_);
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
lean_inc(v_snd_383_);
v___x_395_ = lean_infer_type(v_snd_383_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_397_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
lean_inc(v_a_392_);
v___x_397_ = l_Lean_Meta_getLevel(v_a_392_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_399_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
lean_inc(v_a_394_);
v___x_399_ = l_Lean_Meta_getLevel(v_a_394_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_401_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
lean_inc(v_a_396_);
v___x_401_ = l_Lean_Meta_getLevel(v_a_396_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = l_Lean_Meta_mkFreshLevelMVar(v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc_n(v_a_404_, 2);
lean_dec_ref_known(v___x_403_, 1);
v___x_405_ = l_Lean_mkSort(v_a_404_);
lean_inc(v_a_396_);
v___x_406_ = l_Lean_mkArrow(v_a_396_, v___x_405_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
lean_inc(v_a_392_);
v___x_408_ = l_Lean_mkArrow(v_a_392_, v_a_407_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_a_409_);
v___x_411_ = v___x_376_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_409_);
v___x_411_ = v_reuseFailAlloc_521_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = 0;
v___x_413_ = lean_box(0);
v___x_414_ = l_Lean_Meta_mkFreshExprMVar(v___x_411_, v___x_412_, v___x_413_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__1));
v___x_417_ = lean_box(0);
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 1);
lean_ctor_set(v___x_381_, 1, v___x_417_);
lean_ctor_set(v___x_381_, 0, v_a_402_);
v___x_419_ = v___x_381_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_402_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_417_);
v___x_419_ = v_reuseFailAlloc_512_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 1);
lean_ctor_set(v___x_368_, 1, v___x_419_);
lean_ctor_set(v___x_368_, 0, v_a_400_);
v___x_421_ = v___x_368_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_400_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_511_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_423_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 1);
lean_ctor_set(v___x_363_, 1, v___x_421_);
lean_ctor_set(v___x_363_, 0, v_a_398_);
v___x_423_ = v___x_363_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_398_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_510_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_424_, 0, v_a_404_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v_a_390_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_426_, 0, v_a_388_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
lean_inc_ref(v___x_426_);
v___x_427_ = l_Lean_mkConst(v___x_416_, v___x_426_);
v___x_428_ = lean_unsigned_to_nat(6u);
v___x_429_ = lean_mk_empty_array_with_capacity(v___x_428_);
lean_inc(v_a_392_);
v___x_430_ = lean_array_push(v___x_429_, v_a_392_);
lean_inc(v_a_394_);
v___x_431_ = lean_array_push(v___x_430_, v_a_394_);
lean_inc(v_a_396_);
v___x_432_ = lean_array_push(v___x_431_, v_a_396_);
lean_inc(v_fst_361_);
v___x_433_ = lean_array_push(v___x_432_, v_fst_361_);
lean_inc(v_fst_379_);
v___x_434_ = lean_array_push(v___x_433_, v_fst_379_);
lean_inc(v_a_415_);
v___x_435_ = lean_array_push(v___x_434_, v_a_415_);
v___x_436_ = l_Lean_mkAppN(v___x_427_, v___x_435_);
lean_dec_ref(v___x_435_);
v___x_437_ = lean_box(0);
lean_inc_ref(v___x_436_);
v___x_438_ = l_Lean_Meta_trySynthInstance(v___x_436_, v___x_437_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
if (lean_obj_tag(v_a_439_) == 1)
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec_ref(v___x_436_);
v_a_440_ = lean_ctor_get(v_a_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v_a_439_, 1);
v___x_441_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__3));
v___x_442_ = l_Lean_mkConst(v___x_441_, v___x_426_);
v___x_443_ = lean_unsigned_to_nat(12u);
v___x_444_ = lean_mk_empty_array_with_capacity(v___x_443_);
v___x_445_ = lean_array_push(v___x_444_, v_a_392_);
v___x_446_ = lean_array_push(v___x_445_, v_a_394_);
v___x_447_ = lean_array_push(v___x_446_, v_a_396_);
v___x_448_ = lean_array_push(v___x_447_, v_fst_361_);
v___x_449_ = lean_array_push(v___x_448_, v_fst_379_);
v___x_450_ = lean_array_push(v___x_449_, v_a_415_);
v___x_451_ = lean_array_push(v___x_450_, v_a_440_);
v___x_452_ = lean_array_push(v___x_451_, v_fst_365_);
v___x_453_ = lean_array_push(v___x_452_, v_snd_366_);
v___x_454_ = lean_array_push(v___x_453_, v_snd_383_);
v___x_455_ = lean_array_push(v___x_454_, v_result_348_);
v___x_456_ = lean_array_push(v___x_455_, v_step_350_);
v___x_457_ = l_Lean_mkAppN(v___x_442_, v___x_456_);
lean_dec_ref(v___x_456_);
lean_inc(v_a_355_);
lean_inc_ref(v_a_354_);
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
lean_inc_ref(v___x_457_);
v___x_458_ = lean_infer_type(v___x_457_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_487_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_459_, v_a_353_);
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_487_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_487_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_487_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_473_; lean_object* v_a_474_; 
v___x_465_ = l_Lean_Expr_headBeta(v_a_461_);
v___x_473_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_465_);
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___x_473_);
if (lean_obj_tag(v_a_474_) == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_del_object(v___x_463_);
lean_dec_ref(v___x_457_);
lean_del_object(v___x_385_);
v___x_475_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__5, &l_Lean_Elab_Term_mkCalcTrans___closed__5_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__5);
v___x_476_ = l_Lean_indentExpr(v___x_465_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_477_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
else
{
lean_dec_ref_known(v_a_474_, 1);
goto v___jp_466_;
}
v___jp_466_:
{
lean_object* v___x_468_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v___x_465_);
lean_ctor_set(v___x_385_, 0, v___x_457_);
v___x_468_ = v___x_385_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_465_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_468_);
v___x_470_ = v___x_463_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v___x_457_);
lean_del_object(v___x_385_);
v_a_488_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_458_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_458_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v_a_439_);
lean_dec_ref_known(v___x_426_, 2);
lean_dec(v_a_415_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_dec(v_fst_379_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v___x_496_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__7, &l_Lean_Elab_Term_mkCalcTrans___closed__7_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__7);
v___x_497_ = l_Lean_indentExpr(v___x_436_);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_useDiagnosticMsg;
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_500_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_501_;
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v___x_436_);
lean_dec_ref_known(v___x_426_, 2);
lean_dec(v_a_415_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_dec(v_fst_379_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_502_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_438_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_438_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_a_404_);
lean_dec(v_a_402_);
lean_dec(v_a_400_);
lean_dec(v_a_398_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_513_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_414_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_414_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_a_404_);
lean_dec(v_a_402_);
lean_dec(v_a_400_);
lean_dec(v_a_398_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_522_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_408_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_408_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_a_404_);
lean_dec(v_a_402_);
lean_dec(v_a_400_);
lean_dec(v_a_398_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_530_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_406_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_406_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec(v_a_402_);
lean_dec(v_a_400_);
lean_dec(v_a_398_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_538_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_403_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_403_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec(v_a_400_);
lean_dec(v_a_398_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_546_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_401_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_401_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_a_398_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_554_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_399_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_399_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_562_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_397_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_397_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec(v_a_394_);
lean_dec(v_a_392_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_570_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_395_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_395_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_a_392_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_578_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_393_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_393_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_586_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_391_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_391_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_a_388_);
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_594_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_389_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_389_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_del_object(v___x_385_);
lean_dec(v_snd_383_);
lean_del_object(v___x_381_);
lean_dec(v_fst_379_);
lean_del_object(v___x_376_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v_a_602_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_387_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_387_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec(v_a_373_);
lean_del_object(v___x_368_);
lean_dec(v_snd_366_);
lean_dec(v_fst_365_);
lean_del_object(v___x_363_);
lean_dec(v_fst_361_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v___x_614_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__11, &l_Lean_Elab_Term_mkCalcTrans___closed__11_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__11);
v___x_615_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v___x_614_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_615_;
}
}
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_a_358_);
lean_dec_ref(v_stepType_351_);
lean_dec_ref(v_step_350_);
lean_dec_ref(v_result_348_);
v___x_618_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__12, &l_Lean_Elab_Term_mkCalcTrans___closed__12_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__12);
v___x_619_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v___x_618_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_619_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_mkCalcTrans_0interp(lean_interpreter_value* stack)
{
lean_object* v_result_348_ = stack[0].m_obj;
lean_object* v_resultType_349_ = stack[1].m_obj;
lean_object* v_step_350_ = stack[2].m_obj;
lean_object* v_stepType_351_ = stack[3].m_obj;
lean_object* v_a_352_ = stack[4].m_obj;
lean_object* v_a_353_ = stack[5].m_obj;
lean_object* v_a_354_ = stack[6].m_obj;
lean_object* v_a_355_ = stack[7].m_obj;
lean_object* v_res_620_;
v_res_620_ = l_Lean_Elab_Term_mkCalcTrans(v_result_348_, v_resultType_349_, v_step_350_, v_stepType_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
stack->m_obj
 = v_res_620_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___boxed(lean_object* v_result_621_, lean_object* v_resultType_622_, lean_object* v_step_623_, lean_object* v_stepType_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Elab_Term_mkCalcTrans(v_result_621_, v_resultType_622_, v_step_623_, v_stepType_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec_ref(v_resultType_622_);
return v_res_630_;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
v___x_653_ = l_String_toRawSubstring_x27(v___x_652_);
return v___x_653_;
}
}
lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(lean_object* v_type_678_, lean_object* v_t_679_, uint8_t v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
if (v_a_680_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec_ref(v_type_678_);
v___x_688_ = lean_box(v_a_680_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_t_679_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
else
{
if (lean_obj_tag(v_t_679_) == 1)
{
lean_object* v_info_691_; lean_object* v_kind_692_; lean_object* v_args_693_; lean_object* v_k_695_; uint8_t v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; 
v_info_691_ = lean_ctor_get(v_t_679_, 0);
v_kind_692_ = lean_ctor_get(v_t_679_, 1);
v_args_693_ = lean_ctor_get(v_t_679_, 2);
if (lean_obj_tag(v_kind_692_) == 1)
{
lean_object* v_pre_732_; 
v_pre_732_ = lean_ctor_get(v_kind_692_, 0);
if (lean_obj_tag(v_pre_732_) == 1)
{
lean_object* v_pre_733_; 
v_pre_733_ = lean_ctor_get(v_pre_732_, 0);
if (lean_obj_tag(v_pre_733_) == 1)
{
lean_object* v_pre_734_; 
v_pre_734_ = lean_ctor_get(v_pre_733_, 0);
if (lean_obj_tag(v_pre_734_) == 1)
{
lean_object* v_pre_735_; 
v_pre_735_ = lean_ctor_get(v_pre_734_, 0);
if (lean_obj_tag(v_pre_735_) == 0)
{
lean_object* v_str_736_; lean_object* v_str_737_; lean_object* v_str_738_; lean_object* v_str_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_str_736_ = lean_ctor_get(v_kind_692_, 1);
v_str_737_ = lean_ctor_get(v_pre_732_, 1);
v_str_738_ = lean_ctor_get(v_pre_733_, 1);
v_str_739_ = lean_ctor_get(v_pre_734_, 1);
v___x_740_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0));
v___x_741_ = lean_string_dec_eq(v_str_739_, v___x_740_);
if (v___x_741_ == 0)
{
lean_inc_ref(v_kind_692_);
lean_inc_ref(v_args_693_);
lean_inc(v_info_691_);
lean_dec_ref_known(v_t_679_, 3);
v_k_695_ = v_kind_692_;
v___y_696_ = v_a_680_;
v___y_697_ = v_a_681_;
v___y_698_ = v_a_682_;
v___y_699_ = v_a_683_;
v___y_700_ = v_a_684_;
v___y_701_ = v_a_685_;
v___y_702_ = v_a_686_;
goto v___jp_694_;
}
else
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1));
v___x_743_ = lean_string_dec_eq(v_str_738_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_inc_ref(v_str_738_);
lean_inc_ref(v_str_737_);
lean_inc(v_pre_735_);
lean_inc_ref(v_str_736_);
lean_inc_ref(v_args_693_);
lean_inc(v_info_691_);
lean_dec_ref_known(v_t_679_, 3);
v___x_744_ = l_Lean_Name_str___override(v_pre_735_, v___x_740_);
v___x_745_ = l_Lean_Name_str___override(v___x_744_, v_str_738_);
v___x_746_ = l_Lean_Name_str___override(v___x_745_, v_str_737_);
v___x_747_ = l_Lean_Name_str___override(v___x_746_, v_str_736_);
v_k_695_ = v___x_747_;
v___y_696_ = v_a_680_;
v___y_697_ = v_a_681_;
v___y_698_ = v_a_682_;
v___y_699_ = v_a_683_;
v___y_700_ = v_a_684_;
v___y_701_ = v_a_685_;
v___y_702_ = v_a_686_;
goto v___jp_694_;
}
else
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2));
v___x_749_ = lean_string_dec_eq(v_str_737_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_inc_ref(v_str_737_);
lean_inc(v_pre_735_);
lean_inc_ref(v_str_736_);
lean_inc_ref(v_args_693_);
lean_inc(v_info_691_);
lean_dec_ref_known(v_t_679_, 3);
v___x_750_ = l_Lean_Name_str___override(v_pre_735_, v___x_740_);
v___x_751_ = l_Lean_Name_str___override(v___x_750_, v___x_742_);
v___x_752_ = l_Lean_Name_str___override(v___x_751_, v_str_737_);
v___x_753_ = l_Lean_Name_str___override(v___x_752_, v_str_736_);
v_k_695_ = v___x_753_;
v___y_696_ = v_a_680_;
v___y_697_ = v_a_681_;
v___y_698_ = v_a_682_;
v___y_699_ = v_a_683_;
v___y_700_ = v_a_684_;
v___y_701_ = v_a_685_;
v___y_702_ = v_a_686_;
goto v___jp_694_;
}
else
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3));
v___x_755_ = lean_string_dec_eq(v_str_736_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_inc_ref(v_str_736_);
lean_inc(v_pre_735_);
lean_inc_ref(v_args_693_);
lean_inc(v_info_691_);
lean_dec_ref_known(v_t_679_, 3);
v___x_756_ = l_Lean_Name_str___override(v_pre_735_, v___x_740_);
v___x_757_ = l_Lean_Name_str___override(v___x_756_, v___x_742_);
v___x_758_ = l_Lean_Name_str___override(v___x_757_, v___x_748_);
v___x_759_ = l_Lean_Name_str___override(v___x_758_, v_str_736_);
v_k_695_ = v___x_759_;
v___y_696_ = v_a_680_;
v___y_697_ = v_a_681_;
v___y_698_ = v_a_682_;
v___y_699_ = v_a_683_;
v___y_700_ = v_a_684_;
v___y_701_ = v_a_685_;
v___y_702_ = v_a_686_;
goto v___jp_694_;
}
else
{
uint8_t v___x_760_; lean_object* v___x_761_; 
v___x_760_ = 0;
v___x_761_ = l_Lean_Elab_Term_exprToSyntax(v_type_678_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_toCold_762_; lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_794_; 
v_toCold_762_ = lean_ctor_get(v_a_685_, 0);
v_a_763_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_794_ == 0)
{
v___x_765_ = v___x_761_;
v_isShared_766_ = v_isSharedCheck_794_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_794_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_ref_767_; lean_object* v_quotContext_768_; lean_object* v_currMacroScope_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v_ref_767_ = lean_ctor_get(v_a_685_, 2);
v_quotContext_768_ = lean_ctor_get(v_toCold_762_, 8);
v_currMacroScope_769_ = lean_ctor_get(v_toCold_762_, 9);
v___x_770_ = l_Lean_SourceInfo_fromRef(v_ref_767_, v___x_760_);
v___x_771_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5));
v___x_772_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7));
v___x_773_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8));
lean_inc_n(v___x_770_, 7);
v___x_774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_770_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10));
v___x_776_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12);
lean_inc(v_currMacroScope_769_);
lean_inc(v_quotContext_768_);
v___x_777_ = l_Lean_addMacroScope(v_quotContext_768_, v_pre_735_, v_currMacroScope_769_);
v___x_778_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20));
v___x_779_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_779_, 0, v___x_770_);
lean_ctor_set(v___x_779_, 1, v___x_776_);
lean_ctor_set(v___x_779_, 2, v___x_777_);
lean_ctor_set(v___x_779_, 3, v___x_778_);
v___x_780_ = l_Lean_Syntax_node1(v___x_770_, v___x_775_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node2(v___x_770_, v___x_772_, v___x_774_, v___x_780_);
v___x_782_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21));
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_770_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23));
v___x_785_ = l_Lean_Syntax_node1(v___x_770_, v___x_784_, v_a_763_);
v___x_786_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24));
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_770_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_Syntax_node5(v___x_770_, v___x_771_, v___x_781_, v_t_679_, v___x_783_, v___x_785_, v___x_787_);
v___x_789_ = lean_box(v___x_760_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_790_);
v___x_792_ = v___x_765_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref_known(v_t_679_, 3);
v_a_795_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_761_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_761_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
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
lean_inc_ref(v_kind_692_);
lean_inc_ref(v_args_693_);
lean_inc(v_info_691_);
lean_dec_ref_known(v_t_679_, 3);
v_k_695_ = v_kind_692_;
v___y_696_ = v_a_680_;
v___y_697_ = v_a_681_;
v___y_698_ = v_a_682_;
v___y_699_ = v_a_683_;
v___y_700_ = v_a_684_;
v___y_701_ = v_a_685_;
v___y_702_ = v_a_686_;
goto v___jp_694_;
}
}
else
{
lean_inc_ref(v_kind_692_);
lean_inc_ref(v_args_693_);
lean_inc(v_info_691_);
lean_dec_ref_known(v_t_679_, 3);
v_k_695_ = v_kind_692_;
v___y_696_ = v_a_680_;
v___y_697_ = v_a_681_;
v___y_698_ = v_a_682_;
v___y_699_ = v_a_683_;
v___y_700_ = v_a_684_;
v___y_701_ = v_a_685_;
v___y_702_ = v_a_686_;
goto v___jp_694_;
}
}
else
{
lean_inc_ref(v_kind_692_);
lean_inc_ref(v_args_693_);
lean_inc(v_info_691_);
lean_dec_ref_known(v_t_679_, 3);
v_k_695_ = v_kind_692_;
v___y_696_ = v_a_680_;
v___y_697_ = v_a_681_;
v___y_698_ = v_a_682_;
v___y_699_ = v_a_683_;
v___y_700_ = v_a_684_;
v___y_701_ = v_a_685_;
v___y_702_ = v_a_686_;
goto v___jp_694_;
}
}
else
{
lean_inc_ref(v_kind_692_);
lean_inc_ref(v_args_693_);
lean_inc(v_info_691_);
lean_dec_ref_known(v_t_679_, 3);
v_k_695_ = v_kind_692_;
v___y_696_ = v_a_680_;
v___y_697_ = v_a_681_;
v___y_698_ = v_a_682_;
v___y_699_ = v_a_683_;
v___y_700_ = v_a_684_;
v___y_701_ = v_a_685_;
v___y_702_ = v_a_686_;
goto v___jp_694_;
}
}
else
{
lean_inc_ref(v_args_693_);
lean_inc(v_kind_692_);
lean_inc(v_info_691_);
lean_dec_ref_known(v_t_679_, 3);
v_k_695_ = v_kind_692_;
v___y_696_ = v_a_680_;
v___y_697_ = v_a_681_;
v___y_698_ = v_a_682_;
v___y_699_ = v_a_683_;
v___y_700_ = v_a_684_;
v___y_701_ = v_a_685_;
v___y_702_ = v_a_686_;
goto v___jp_694_;
}
v___jp_694_:
{
size_t v_sz_703_; size_t v___x_704_; lean_object* v___x_705_; 
v_sz_703_ = lean_array_size(v_args_693_);
v___x_704_ = ((size_t)0ULL);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_678_, v_sz_703_, v___x_704_, v_args_693_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_723_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_723_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_723_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_723_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_fst_710_; lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_722_; 
v_fst_710_ = lean_ctor_get(v_a_706_, 0);
v_snd_711_ = lean_ctor_get(v_a_706_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_a_706_);
if (v_isSharedCheck_722_ == 0)
{
v___x_713_ = v_a_706_;
v_isShared_714_ = v_isSharedCheck_722_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_inc(v_fst_710_);
lean_dec(v_a_706_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_722_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_715_, 0, v_info_691_);
lean_ctor_set(v___x_715_, 1, v_k_695_);
lean_ctor_set(v___x_715_, 2, v_fst_710_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_snd_711_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_717_);
v___x_719_ = v___x_708_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_k_695_);
lean_dec(v_info_691_);
v_a_724_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_705_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_705_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
else
{
uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_type_678_);
v___x_803_ = 0;
v___x_804_ = lean_box(v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_t_679_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_678_ = stack[0].m_obj;
lean_object* v_t_679_ = stack[1].m_obj;
uint8_t v_a_680_ = stack[2].m_num;
lean_object* v_a_681_ = stack[3].m_obj;
lean_object* v_a_682_ = stack[4].m_obj;
lean_object* v_a_683_ = stack[5].m_obj;
lean_object* v_a_684_ = stack[6].m_obj;
lean_object* v_a_685_ = stack[7].m_obj;
lean_object* v_a_686_ = stack[8].m_obj;
lean_object* v_res_807_;
v_res_807_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_678_, v_t_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
stack->m_obj
 = v_res_807_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(lean_object* v_type_808_, size_t v_sz_809_, size_t v_i_810_, lean_object* v_bs_811_, uint8_t v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
uint8_t v___x_820_; 
v___x_820_ = lean_usize_dec_lt(v_i_810_, v_sz_809_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec_ref(v_type_808_);
v___x_821_ = lean_box(v___y_812_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v_bs_811_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v_v_824_; lean_object* v___x_825_; lean_object* v_bs_x27_826_; lean_object* v___x_827_; 
v_v_824_ = lean_array_uget(v_bs_811_, v_i_810_);
v___x_825_ = lean_unsigned_to_nat(0u);
v_bs_x27_826_ = lean_array_uset(v_bs_811_, v_i_810_, v___x_825_);
lean_inc_ref(v_type_808_);
v___x_827_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_808_, v_v_824_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v_fst_829_; lean_object* v_snd_830_; size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
v_fst_829_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_fst_829_);
v_snd_830_ = lean_ctor_get(v_a_828_, 1);
lean_inc(v_snd_830_);
lean_dec(v_a_828_);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_add(v_i_810_, v___x_831_);
v___x_833_ = lean_array_uset(v_bs_x27_826_, v_i_810_, v_fst_829_);
v___x_834_ = lean_unbox(v_snd_830_);
lean_dec(v_snd_830_);
v_i_810_ = v___x_832_;
v_bs_811_ = v___x_833_;
v___y_812_ = v___x_834_;
goto _start;
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref(v_bs_x27_826_);
lean_dec_ref(v_type_808_);
v_a_836_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_827_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_827_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_808_ = stack[0].m_obj;
size_t v_sz_809_ = stack[1].m_num;
size_t v_i_810_ = stack[2].m_num;
lean_object* v_bs_811_ = stack[3].m_obj;
uint8_t v___y_812_ = stack[4].m_num;
lean_object* v___y_813_ = stack[5].m_obj;
lean_object* v___y_814_ = stack[6].m_obj;
lean_object* v___y_815_ = stack[7].m_obj;
lean_object* v___y_816_ = stack[8].m_obj;
lean_object* v___y_817_ = stack[9].m_obj;
lean_object* v___y_818_ = stack[10].m_obj;
lean_object* v_res_844_;
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_808_, v_sz_809_, v_i_810_, v_bs_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0___boxed(lean_object* v_type_845_, lean_object* v_sz_846_, lean_object* v_i_847_, lean_object* v_bs_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
size_t v_sz_boxed_857_; size_t v_i_boxed_858_; uint8_t v___y_7635__boxed_859_; lean_object* v_res_860_; 
v_sz_boxed_857_ = lean_unbox_usize(v_sz_846_);
lean_dec(v_sz_846_);
v_i_boxed_858_ = lean_unbox_usize(v_i_847_);
lean_dec(v_i_847_);
v___y_7635__boxed_859_ = lean_unbox(v___y_849_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_845_, v_sz_boxed_857_, v_i_boxed_858_, v_bs_848_, v___y_7635__boxed_859_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object* v_type_861_, lean_object* v_t_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
uint8_t v_a_7704__boxed_871_; lean_object* v_res_872_; 
v_a_7704__boxed_871_ = lean_unbox(v_a_863_);
v_res_872_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_861_, v_t_862_, v_a_7704__boxed_871_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_872_;
}
}
lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object* v_t_873_, lean_object* v_type_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
uint8_t v___x_882_; lean_object* v___x_883_; 
v___x_882_ = 1;
v___x_883_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_874_, v_t_873_, v___x_882_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_892_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_892_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_fst_888_; lean_object* v___x_890_; 
v_fst_888_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_fst_888_);
lean_dec(v_a_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_fst_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_fst_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v_a_893_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_883_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_883_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_annotateFirstHoleWithType_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_873_ = stack[0].m_obj;
lean_object* v_type_874_ = stack[1].m_obj;
lean_object* v_a_875_ = stack[2].m_obj;
lean_object* v_a_876_ = stack[3].m_obj;
lean_object* v_a_877_ = stack[4].m_obj;
lean_object* v_a_878_ = stack[5].m_obj;
lean_object* v_a_879_ = stack[6].m_obj;
lean_object* v_a_880_ = stack[7].m_obj;
lean_object* v_res_901_;
v_res_901_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_t_873_, v_type_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType___boxed(lean_object* v_t_902_, lean_object* v_type_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_t_902_, v_type_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
return v_res_911_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_box(0);
v___x_917_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_916_);
return v___x_918_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg(){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0);
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_922_;
v_res_922_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___boxed(lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v_res_924_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(lean_object* v_00_u03b1_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_933_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_926_ = stack[1].m_obj;
lean_object* v___y_927_ = stack[2].m_obj;
lean_object* v___y_928_ = stack[3].m_obj;
lean_object* v___y_929_ = stack[4].m_obj;
lean_object* v___y_930_ = stack[5].m_obj;
lean_object* v___y_931_ = stack[6].m_obj;
lean_object* v_res_934_;
v_res_934_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(lean_box(0), v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___boxed(lean_object* v_00_u03b1_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(v_00_u03b1_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__7));
v___x_960_ = l_String_toRawSubstring_x27(v___x_959_);
return v___x_960_;
}
}
lean_object* l_Lean_Elab_Term_mkCalcFirstStepView(lean_object* v_step0_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_toCold_977_; lean_object* v_ref_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_toCold_977_ = lean_ctor_get(v_a_974_, 0);
v_ref_978_ = lean_ctor_get(v_a_974_, 2);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_969_);
v___x_980_ = l_Lean_Syntax_isOfKind(v_step0_969_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_dec(v_step0_969_);
v___x_981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_981_;
}
else
{
lean_object* v___x_982_; lean_object* v_term_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_982_ = lean_unsigned_to_nat(0u);
v_term_983_ = l_Lean_Syntax_getArg(v_step0_969_, v___x_982_);
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = l_Lean_Syntax_getArg(v_step0_969_, v___x_984_);
lean_inc(v___x_985_);
v___x_986_ = l_Lean_Syntax_matchesNull(v___x_985_, v___x_982_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_985_);
v___x_988_ = l_Lean_Syntax_matchesNull(v___x_985_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec(v___x_985_);
lean_dec(v_term_983_);
lean_dec(v_step0_969_);
v___x_989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_989_;
}
else
{
lean_object* v_proof_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_proof_990_ = l_Lean_Syntax_getArg(v___x_985_, v___x_984_);
lean_dec(v___x_985_);
v___x_991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_991_, 0, v_step0_969_);
lean_ctor_set(v___x_991_, 1, v_term_983_);
lean_ctor_set(v___x_991_, 2, v_proof_990_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
else
{
lean_object* v_ref_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_quotContext_1000_; lean_object* v_currMacroScope_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec(v___x_985_);
v_ref_993_ = l_Lean_replaceRef(v_step0_969_, v_ref_978_);
v___x_994_ = 0;
v___x_995_ = l_Lean_SourceInfo_fromRef(v_ref_993_, v___x_994_);
lean_dec(v_ref_993_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__2));
lean_inc_n(v___x_995_, 4);
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__3));
v___x_999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_995_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v_quotContext_1000_ = lean_ctor_get(v_toCold_977_, 8);
v_currMacroScope_1001_ = lean_ctor_get(v_toCold_977_, 9);
v___x_1002_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__4));
v___x_1003_ = l_Lean_Syntax_node1(v___x_995_, v___x_1002_, v___x_999_);
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__6));
v___x_1005_ = l_Lean_Syntax_node3(v___x_995_, v___x_1004_, v_term_983_, v___x_997_, v___x_1003_);
v___x_1006_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcFirstStepView___closed__8, &l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once, _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__9));
lean_inc(v_currMacroScope_1001_);
lean_inc(v_quotContext_1000_);
v___x_1008_ = l_Lean_addMacroScope(v_quotContext_1000_, v___x_1007_, v_currMacroScope_1001_);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__11));
v___x_1010_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1010_, 0, v___x_995_);
lean_ctor_set(v___x_1010_, 1, v___x_1006_);
lean_ctor_set(v___x_1010_, 2, v___x_1008_);
lean_ctor_set(v___x_1010_, 3, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1011_, 0, v_step0_969_);
lean_ctor_set(v___x_1011_, 1, v___x_1005_);
lean_ctor_set(v___x_1011_, 2, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_mkCalcFirstStepView_0interp(lean_interpreter_value* stack)
{
lean_object* v_step0_969_ = stack[0].m_obj;
lean_object* v_a_970_ = stack[1].m_obj;
lean_object* v_a_971_ = stack[2].m_obj;
lean_object* v_a_972_ = stack[3].m_obj;
lean_object* v_a_973_ = stack[4].m_obj;
lean_object* v_a_974_ = stack[5].m_obj;
lean_object* v_a_975_ = stack[6].m_obj;
lean_object* v_res_1013_;
v_res_1013_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
stack->m_obj
 = v_res_1013_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___boxed(lean_object* v_step0_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
return v_res_1022_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(lean_object* v_as_1027_, size_t v_sz_1028_, size_t v_i_1029_, lean_object* v_b_1030_){
_start:
{
lean_object* v_a_1033_; uint8_t v___x_1037_; 
v___x_1037_ = lean_usize_dec_lt(v_i_1029_, v_sz_1028_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_b_1030_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; lean_object* v_a_1040_; uint8_t v___x_1041_; 
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1));
v_a_1040_ = lean_array_uget_borrowed(v_as_1027_, v_i_1029_);
lean_inc(v_a_1040_);
v___x_1041_ = l_Lean_Syntax_isOfKind(v_a_1040_, v___x_1039_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_dec_ref_known(v___x_1042_, 1);
v_a_1033_ = v_b_1030_;
goto v___jp_1032_;
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v_b_1030_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = l_Lean_Syntax_getArg(v_a_1040_, v___x_1051_);
v___x_1053_ = lean_unsigned_to_nat(2u);
v___x_1054_ = l_Lean_Syntax_getArg(v_a_1040_, v___x_1053_);
lean_inc(v_a_1040_);
v___x_1055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1040_);
lean_ctor_set(v___x_1055_, 1, v___x_1052_);
lean_ctor_set(v___x_1055_, 2, v___x_1054_);
v___x_1056_ = lean_array_push(v_b_1030_, v___x_1055_);
v_a_1033_ = v___x_1056_;
goto v___jp_1032_;
}
}
v___jp_1032_:
{
size_t v___x_1034_; size_t v___x_1035_; 
v___x_1034_ = ((size_t)1ULL);
v___x_1035_ = lean_usize_add(v_i_1029_, v___x_1034_);
v_i_1029_ = v___x_1035_;
v_b_1030_ = v_a_1033_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1027_ = stack[0].m_obj;
size_t v_sz_1028_ = stack[1].m_num;
size_t v_i_1029_ = stack[2].m_num;
lean_object* v_b_1030_ = stack[3].m_obj;
lean_object* v_res_1057_;
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1027_, v_sz_1028_, v_i_1029_, v_b_1030_);
stack->m_obj
 = v_res_1057_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___boxed(lean_object* v_as_1058_, lean_object* v_sz_1059_, lean_object* v_i_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_){
_start:
{
size_t v_sz_boxed_1063_; size_t v_i_boxed_1064_; lean_object* v_res_1065_; 
v_sz_boxed_1063_ = lean_unbox_usize(v_sz_1059_);
lean_dec(v_sz_1059_);
v_i_boxed_1064_ = lean_unbox_usize(v_i_1060_);
lean_dec(v_i_1060_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1058_, v_sz_boxed_1063_, v_i_boxed_1064_, v_b_1061_);
lean_dec_ref(v_as_1058_);
return v_res_1065_;
}
}
lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object* v_steps_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_1070_);
v___x_1079_ = l_Lean_Syntax_isOfKind(v_steps_1070_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
lean_dec(v_steps_1070_);
v___x_1080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; lean_object* v_step0_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v_step0_1082_ = l_Lean_Syntax_getArg(v_steps_1070_, v___x_1081_);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_1082_);
v___x_1084_ = l_Lean_Syntax_isOfKind(v_step0_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
lean_dec(v_step0_1082_);
lean_dec(v_steps_1070_);
v___x_1085_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_rest_1088_; lean_object* v___x_1089_; 
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = l_Lean_Syntax_getArg(v_steps_1070_, v___x_1086_);
lean_dec(v_steps_1070_);
v_rest_1088_ = l_Lean_Syntax_getArgs(v___x_1087_);
lean_dec(v___x_1087_);
v___x_1089_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_1082_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; size_t v_sz_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1091_ = lean_mk_empty_array_with_capacity(v___x_1086_);
v___x_1092_ = lean_array_push(v___x_1091_, v_a_1090_);
v_sz_1093_ = lean_array_size(v_rest_1088_);
v___x_1094_ = ((size_t)0ULL);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_rest_1088_, v_sz_1093_, v___x_1094_, v___x_1092_);
lean_dec_ref(v_rest_1088_);
return v___x_1095_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_rest_1088_);
v_a_1096_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1089_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1089_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_mkCalcStepViews_0interp(lean_interpreter_value* stack)
{
lean_object* v_steps_1070_ = stack[0].m_obj;
lean_object* v_a_1071_ = stack[1].m_obj;
lean_object* v_a_1072_ = stack[2].m_obj;
lean_object* v_a_1073_ = stack[3].m_obj;
lean_object* v_a_1074_ = stack[4].m_obj;
lean_object* v_a_1075_ = stack[5].m_obj;
lean_object* v_a_1076_ = stack[6].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews___boxed(lean_object* v_steps_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1113_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(lean_object* v_as_1114_, size_t v_sz_1115_, size_t v_i_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1114_, v_sz_1115_, v_i_1116_, v_b_1117_);
return v___x_1125_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1114_ = stack[0].m_obj;
size_t v_sz_1115_ = stack[1].m_num;
size_t v_i_1116_ = stack[2].m_num;
lean_object* v_b_1117_ = stack[3].m_obj;
lean_object* v___y_1118_ = stack[4].m_obj;
lean_object* v___y_1119_ = stack[5].m_obj;
lean_object* v___y_1120_ = stack[6].m_obj;
lean_object* v___y_1121_ = stack[7].m_obj;
lean_object* v___y_1122_ = stack[8].m_obj;
lean_object* v___y_1123_ = stack[9].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(v_as_1114_, v_sz_1115_, v_i_1116_, v_b_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(lean_object* v_as_1127_, lean_object* v_sz_1128_, lean_object* v_i_1129_, lean_object* v_b_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
size_t v_sz_boxed_1138_; size_t v_i_boxed_1139_; lean_object* v_res_1140_; 
v_sz_boxed_1138_ = lean_unbox_usize(v_sz_1128_);
lean_dec(v_sz_1128_);
v_i_boxed_1139_ = lean_unbox_usize(v_i_1129_);
lean_dec(v_i_1129_);
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(v_as_1127_, v_sz_boxed_1138_, v_i_boxed_1139_, v_b_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec_ref(v_as_1127_);
return v_res_1140_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = l_Lean_instInhabitedExpr;
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(lean_object* v_msg_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_obj_once(&l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0, &l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0);
v___x_1145_ = lean_panic_fn_borrowed(v___x_1144_, v_msg_1143_);
return v___x_1145_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(lean_object* v_opts_1146_, lean_object* v_opt_1147_){
_start:
{
lean_object* v_name_1148_; lean_object* v_defValue_1149_; lean_object* v_map_1150_; lean_object* v___x_1151_; 
v_name_1148_ = lean_ctor_get(v_opt_1147_, 0);
v_defValue_1149_ = lean_ctor_get(v_opt_1147_, 1);
v_map_1150_ = lean_ctor_get(v_opts_1146_, 0);
v___x_1151_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1150_, v_name_1148_);
if (lean_obj_tag(v___x_1151_) == 0)
{
uint8_t v___x_1152_; 
v___x_1152_ = lean_unbox(v_defValue_1149_);
return v___x_1152_;
}
else
{
lean_object* v_val_1153_; 
v_val_1153_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v___x_1151_, 1);
if (lean_obj_tag(v_val_1153_) == 1)
{
uint8_t v_v_1154_; 
v_v_1154_ = lean_ctor_get_uint8(v_val_1153_, 0);
lean_dec_ref_known(v_val_1153_, 0);
return v_v_1154_;
}
else
{
uint8_t v___x_1155_; 
lean_dec(v_val_1153_);
v___x_1155_ = lean_unbox(v_defValue_1149_);
return v___x_1155_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1146_ = stack[0].m_obj;
lean_object* v_opt_1147_ = stack[1].m_obj;
uint8_t v_res_1156_;
v_res_1156_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_opts_1146_, v_opt_1147_);
stack->m_num = v_res_1156_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_opts_1157_, lean_object* v_opt_1158_){
_start:
{
uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_res_1159_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_opts_1157_, v_opt_1158_);
lean_dec_ref(v_opt_1158_);
lean_dec_ref(v_opts_1157_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_box(1);
v___x_1162_ = l_Lean_MessageData_ofFormat(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2));
v___x_1167_ = l_Lean_MessageData_ofFormat(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
return v_x_1168_;
}
else
{
lean_object* v_head_1170_; lean_object* v_tail_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1193_; 
v_head_1170_ = lean_ctor_get(v_x_1169_, 0);
v_tail_1171_ = lean_ctor_get(v_x_1169_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1173_ = v_x_1169_;
v_isShared_1174_ = v_isSharedCheck_1193_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_tail_1171_);
lean_inc(v_head_1170_);
lean_dec(v_x_1169_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1193_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_before_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1191_; 
v_before_1175_ = lean_ctor_get(v_head_1170_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_head_1170_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_head_1170_, 1);
lean_dec(v_unused_1192_);
v___x_1177_ = v_head_1170_;
v_isShared_1178_ = v_isSharedCheck_1191_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_before_1175_);
lean_dec(v_head_1170_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1191_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 7);
lean_ctor_set(v___x_1177_, 1, v___x_1179_);
lean_ctor_set(v___x_1177_, 0, v_x_1168_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_x_1168_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 7);
lean_ctor_set(v___x_1173_, 1, v___x_1182_);
lean_ctor_set(v___x_1173_, 0, v___x_1181_);
v___x_1184_ = v___x_1173_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = l_Lean_MessageData_ofSyntax(v_before_1175_);
v___x_1186_ = l_Lean_indentD(v___x_1185_);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1184_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v_x_1168_ = v___x_1187_;
v_x_1169_ = v_tail_1171_;
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
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_1198_ = l_Lean_MessageData_ofFormat(v___x_1197_);
return v___x_1198_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_1199_, lean_object* v_macroStack_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1203_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1201_);
v___x_1204_ = l_Lean_Elab_pp_macroStack;
v___x_1205_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v___x_1203_, v___x_1204_);
lean_dec_ref(v___x_1203_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
lean_dec(v_macroStack_1200_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_msgData_1199_);
return v___x_1206_;
}
else
{
if (lean_obj_tag(v_macroStack_1200_) == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_msgData_1199_);
return v___x_1207_;
}
else
{
lean_object* v_head_1208_; lean_object* v_after_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1224_; 
v_head_1208_ = lean_ctor_get(v_macroStack_1200_, 0);
lean_inc(v_head_1208_);
v_after_1209_ = lean_ctor_get(v_head_1208_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_head_1208_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_head_1208_, 0);
lean_dec(v_unused_1225_);
v___x_1211_ = v_head_1208_;
v_isShared_1212_ = v_isSharedCheck_1224_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_after_1209_);
lean_dec(v_head_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1224_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 7);
lean_ctor_set(v___x_1211_, 1, v___x_1213_);
lean_ctor_set(v___x_1211_, 0, v_msgData_1199_);
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_msgData_1199_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_msgData_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1216_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l_Lean_MessageData_ofSyntax(v_after_1209_);
v___x_1219_ = l_Lean_indentD(v___x_1218_);
v_msgData_1220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1220_, 0, v___x_1217_);
lean_ctor_set(v_msgData_1220_, 1, v___x_1219_);
v___x_1221_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(v_msgData_1220_, v_macroStack_1200_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1199_ = stack[0].m_obj;
lean_object* v_macroStack_1200_ = stack[1].m_obj;
lean_object* v___y_1201_ = stack[2].m_obj;
lean_object* v_res_1226_;
v_res_1226_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1199_, v_macroStack_1200_, v___y_1201_);
stack->m_obj
 = v_res_1226_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1227_, lean_object* v_macroStack_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1227_, v_macroStack_1228_, v___y_1229_);
lean_dec_ref(v___y_1229_);
return v_res_1231_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(lean_object* v_msg_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_ref_1240_; lean_object* v_macroStack_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_a_1244_; lean_object* v___x_1245_; lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1254_; 
v_ref_1240_ = lean_ctor_get(v___y_1237_, 2);
v_macroStack_1241_ = lean_ctor_get(v___y_1233_, 1);
v___x_1242_ = l_Lean_Elab_getBetterRef(v_ref_1240_, v_macroStack_1241_);
v___x_1243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_1232_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
lean_inc(v_macroStack_1241_);
v___x_1245_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_a_1244_, v_macroStack_1241_, v___y_1237_);
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1254_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1242_);
lean_ctor_set(v___x_1250_, 1, v_a_1246_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 1);
lean_ctor_set(v___x_1248_, 0, v___x_1250_);
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1232_ = stack[0].m_obj;
lean_object* v___y_1233_ = stack[1].m_obj;
lean_object* v___y_1234_ = stack[2].m_obj;
lean_object* v___y_1235_ = stack[3].m_obj;
lean_object* v___y_1236_ = stack[4].m_obj;
lean_object* v___y_1237_ = stack[5].m_obj;
lean_object* v___y_1238_ = stack[6].m_obj;
lean_object* v_res_1255_;
v_res_1255_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
stack->m_obj
 = v_res_1255_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1264_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(lean_object* v_ref_1265_, lean_object* v_msg_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_toCold_1274_; lean_object* v_currRecDepth_1275_; lean_object* v_ref_1276_; uint16_t v_optionFlags_1277_; uint8_t v_suppressElabErrors_1278_; uint8_t v_isRecordingDeps_1279_; lean_object* v_ref_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_toCold_1274_ = lean_ctor_get(v___y_1271_, 0);
v_currRecDepth_1275_ = lean_ctor_get(v___y_1271_, 1);
v_ref_1276_ = lean_ctor_get(v___y_1271_, 2);
v_optionFlags_1277_ = lean_ctor_get_uint16(v___y_1271_, sizeof(void*)*3);
v_suppressElabErrors_1278_ = lean_ctor_get_uint8(v___y_1271_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1279_ = lean_ctor_get_uint8(v___y_1271_, sizeof(void*)*3 + 3);
v_ref_1280_ = l_Lean_replaceRef(v_ref_1265_, v_ref_1276_);
lean_inc(v_currRecDepth_1275_);
lean_inc_ref(v_toCold_1274_);
v___x_1281_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1281_, 0, v_toCold_1274_);
lean_ctor_set(v___x_1281_, 1, v_currRecDepth_1275_);
lean_ctor_set(v___x_1281_, 2, v_ref_1280_);
lean_ctor_set_uint16(v___x_1281_, sizeof(void*)*3, v_optionFlags_1277_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 2, v_suppressElabErrors_1278_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 3, v_isRecordingDeps_1279_);
v___x_1282_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___x_1281_, v___y_1272_);
lean_dec_ref_known(v___x_1281_, 3);
return v___x_1282_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1265_ = stack[0].m_obj;
lean_object* v_msg_1266_ = stack[1].m_obj;
lean_object* v___y_1267_ = stack[2].m_obj;
lean_object* v___y_1268_ = stack[3].m_obj;
lean_object* v___y_1269_ = stack[4].m_obj;
lean_object* v___y_1270_ = stack[5].m_obj;
lean_object* v___y_1271_ = stack[6].m_obj;
lean_object* v___y_1272_ = stack[7].m_obj;
lean_object* v_res_1283_;
v_res_1283_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1265_, v_msg_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
stack->m_obj
 = v_res_1283_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg___boxed(lean_object* v_ref_1284_, lean_object* v_msg_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1284_, v_msg_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v_ref_1284_);
return v_res_1293_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(lean_object* v_as_1306_, size_t v_sz_1307_, size_t v_i_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_a_1318_; lean_object* v___y_1323_; lean_object* v_____do__lift_1324_; uint8_t v___x_1328_; 
v___x_1328_ = lean_usize_dec_lt(v_i_1308_, v_sz_1307_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_b_1309_);
return v___x_1329_;
}
else
{
lean_object* v_fst_1330_; lean_object* v_snd_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1537_; 
v_fst_1330_ = lean_ctor_get(v_b_1309_, 0);
v_snd_1331_ = lean_ctor_get(v_b_1309_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_b_1309_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1333_ = v_b_1309_;
v_isShared_1334_ = v_isSharedCheck_1537_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_snd_1331_);
lean_inc(v_fst_1330_);
lean_dec(v_b_1309_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1537_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_a_1335_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v_____do__lift_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; 
v_a_1335_ = lean_array_uget_borrowed(v_as_1306_, v_i_1308_);
if (lean_obj_tag(v_snd_1331_) == 1)
{
lean_object* v_val_1514_; lean_object* v___x_1515_; 
v_val_1514_ = lean_ctor_get(v_snd_1331_, 0);
lean_inc(v___y_1315_);
lean_inc_ref(v___y_1314_);
lean_inc(v___y_1313_);
lean_inc_ref(v___y_1312_);
lean_inc(v_val_1514_);
v___x_1515_ = lean_infer_type(v_val_1514_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v_term_1517_; lean_object* v___x_1518_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v_term_1517_ = lean_ctor_get(v_a_1335_, 1);
lean_inc(v_term_1517_);
v___x_1518_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_term_1517_, v_a_1516_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v_____do__lift_1397_ = v_a_1519_;
v___y_1398_ = v___y_1310_;
v___y_1399_ = v___y_1311_;
v___y_1400_ = v___y_1312_;
v___y_1401_ = v___y_1313_;
v___y_1402_ = v___y_1314_;
v___y_1403_ = v___y_1315_;
goto v___jp_1396_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref_known(v_snd_1331_, 1);
lean_del_object(v___x_1333_);
lean_dec(v_fst_1330_);
v_a_1520_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1518_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec_ref_known(v_snd_1331_, 1);
lean_del_object(v___x_1333_);
lean_dec(v_fst_1330_);
v_a_1528_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1515_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1515_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_term_1536_; 
v_term_1536_ = lean_ctor_get(v_a_1335_, 1);
lean_inc(v_term_1536_);
v_____do__lift_1397_ = v_term_1536_;
v___y_1398_ = v___y_1310_;
v___y_1399_ = v___y_1311_;
v___y_1400_ = v___y_1312_;
v___y_1401_ = v___y_1313_;
v___y_1402_ = v___y_1314_;
v___y_1403_ = v___y_1315_;
goto v___jp_1396_;
}
v___jp_1336_:
{
lean_object* v_term_1345_; lean_object* v_proof_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_term_1345_ = lean_ctor_get(v_a_1335_, 1);
v_proof_1346_ = lean_ctor_get(v_a_1335_, 2);
lean_inc_ref(v___y_1337_);
v___x_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___y_1337_);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_box(v___x_1328_);
v___x_1350_ = lean_box(v___x_1328_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v_proof_1346_);
v___x_1351_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 9);
lean_closure_set(v___x_1351_, 0, v_proof_1346_);
lean_closure_set(v___x_1351_, 1, v___x_1347_);
lean_closure_set(v___x_1351_, 2, v___x_1349_);
lean_closure_set(v___x_1351_, 3, v___x_1350_);
lean_closure_set(v___x_1351_, 4, v___x_1348_);
lean_closure_set(v___x_1351_, 5, v___y_1339_);
lean_closure_set(v___x_1351_, 6, v___y_1340_);
lean_closure_set(v___x_1351_, 7, v___y_1341_);
lean_closure_set(v___x_1351_, 8, v___y_1342_);
v___x_1352_ = l_Lean_Core_withFreshMacroScope___redArg(v___x_1351_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1352_) == 0)
{
if (lean_obj_tag(v_fst_1330_) == 1)
{
lean_object* v_val_1353_; lean_object* v_a_1354_; lean_object* v_fst_1355_; lean_object* v_snd_1356_; lean_object* v___x_1357_; 
lean_del_object(v___x_1333_);
v_val_1353_ = lean_ctor_get(v_fst_1330_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v_fst_1330_, 1);
v_a_1354_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1352_, 1);
v_fst_1355_ = lean_ctor_get(v_val_1353_, 0);
lean_inc(v_fst_1355_);
v_snd_1356_ = lean_ctor_get(v_val_1353_, 1);
lean_inc(v_snd_1356_);
lean_dec(v_val_1353_);
v___x_1357_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_toCold_1358_; lean_object* v_currRecDepth_1359_; lean_object* v_ref_1360_; uint16_t v_optionFlags_1361_; uint8_t v_suppressElabErrors_1362_; uint8_t v_isRecordingDeps_1363_; lean_object* v_ref_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec_ref_known(v___x_1357_, 1);
v_toCold_1358_ = lean_ctor_get(v___y_1343_, 0);
v_currRecDepth_1359_ = lean_ctor_get(v___y_1343_, 1);
v_ref_1360_ = lean_ctor_get(v___y_1343_, 2);
v_optionFlags_1361_ = lean_ctor_get_uint16(v___y_1343_, sizeof(void*)*3);
v_suppressElabErrors_1362_ = lean_ctor_get_uint8(v___y_1343_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1363_ = lean_ctor_get_uint8(v___y_1343_, sizeof(void*)*3 + 3);
v_ref_1364_ = l_Lean_replaceRef(v_term_1345_, v_ref_1360_);
lean_inc(v_currRecDepth_1359_);
lean_inc_ref(v_toCold_1358_);
v___x_1365_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1365_, 0, v_toCold_1358_);
lean_ctor_set(v___x_1365_, 1, v_currRecDepth_1359_);
lean_ctor_set(v___x_1365_, 2, v_ref_1364_);
lean_ctor_set_uint16(v___x_1365_, sizeof(void*)*3, v_optionFlags_1361_);
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*3 + 2, v_suppressElabErrors_1362_);
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*3 + 3, v_isRecordingDeps_1363_);
v___x_1366_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_1355_, v_snd_1356_, v_a_1354_, v___y_1337_, v___y_1341_, v___y_1342_, v___x_1365_, v___y_1344_);
lean_dec_ref_known(v___x_1365_, 3);
lean_dec(v_snd_1356_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___y_1323_ = v___y_1338_;
v_____do__lift_1324_ = v_a_1367_;
goto v___jp_1322_;
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v___y_1338_);
v_a_1368_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1366_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_snd_1356_);
lean_dec(v_fst_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___y_1337_);
v_a_1376_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1357_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1357_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; 
lean_dec(v_fst_1330_);
v_a_1384_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1352_, 1);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___y_1337_);
lean_ctor_set(v___x_1333_, 0, v_a_1384_);
v___x_1386_ = v___x_1333_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1384_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___y_1337_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
v___y_1323_ = v___y_1338_;
v_____do__lift_1324_ = v___x_1386_;
goto v___jp_1322_;
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_del_object(v___x_1333_);
lean_dec(v_fst_1330_);
v_a_1388_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1352_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1352_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
v___jp_1396_:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Elab_Term_elabType(v_____do__lift_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_1405_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
if (lean_obj_tag(v_a_1407_) == 1)
{
lean_object* v_val_1408_; lean_object* v_snd_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1482_; 
v_val_1408_ = lean_ctor_get(v_a_1407_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v_a_1407_, 1);
v_snd_1409_ = lean_ctor_get(v_val_1408_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_val_1408_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_val_1408_, 0);
lean_dec(v_unused_1483_);
v___x_1411_ = v_val_1408_;
v_isShared_1412_ = v_isSharedCheck_1482_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_snd_1409_);
lean_dec(v_val_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1482_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
if (lean_obj_tag(v_snd_1331_) == 1)
{
lean_object* v_fst_1413_; lean_object* v_snd_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1480_; 
v_fst_1413_ = lean_ctor_get(v_snd_1409_, 0);
v_snd_1414_ = lean_ctor_get(v_snd_1409_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_snd_1409_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1416_ = v_snd_1409_;
v_isShared_1417_ = v_isSharedCheck_1480_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_snd_1414_);
lean_inc(v_fst_1413_);
lean_dec(v_snd_1409_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1480_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_val_1418_; lean_object* v___x_1419_; 
v_val_1418_ = lean_ctor_get(v_snd_1331_, 0);
lean_inc_n(v_val_1418_, 2);
lean_dec_ref_known(v_snd_1331_, 1);
lean_inc(v_fst_1413_);
v___x_1419_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1413_, v_val_1418_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; uint8_t v___x_1421_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = lean_unbox(v_a_1420_);
lean_dec(v_a_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; 
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v_fst_1413_);
v___x_1422_ = lean_infer_type(v_fst_1413_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v_val_1418_);
v___x_1424_ = lean_infer_type(v_val_1418_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v_term_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v_term_1426_ = lean_ctor_get(v_a_1335_, 1);
v___x_1427_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_1428_ = l_Lean_MessageData_ofExpr(v_fst_1413_);
v___x_1429_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 7);
lean_ctor_set(v___x_1416_, 1, v___x_1429_);
lean_ctor_set(v___x_1416_, 0, v___x_1428_);
v___x_1431_ = v___x_1416_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = l_Lean_MessageData_ofExpr(v_a_1423_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set_tag(v___x_1411_, 7);
lean_ctor_set(v___x_1411_, 1, v___x_1432_);
lean_ctor_set(v___x_1411_, 0, v___x_1431_);
v___x_1434_ = v___x_1411_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1435_ = l_Lean_indentD(v___x_1434_);
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1427_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = l_Lean_MessageData_ofExpr(v_val_1418_);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v___x_1429_);
v___x_1441_ = l_Lean_MessageData_ofExpr(v_a_1425_);
v___x_1442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = l_Lean_indentD(v___x_1442_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1438_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1426_, v___x_1444_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_dec_ref_known(v___x_1445_, 1);
v___y_1337_ = v_a_1405_;
v___y_1338_ = v_snd_1414_;
v___y_1339_ = v___y_1398_;
v___y_1340_ = v___y_1399_;
v___y_1341_ = v___y_1400_;
v___y_1342_ = v___y_1401_;
v___y_1343_ = v___y_1402_;
v___y_1344_ = v___y_1403_;
goto v___jp_1336_;
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_snd_1414_);
lean_dec(v_a_1405_);
lean_del_object(v___x_1333_);
lean_dec(v_fst_1330_);
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_a_1423_);
lean_dec(v_val_1418_);
lean_del_object(v___x_1416_);
lean_dec(v_snd_1414_);
lean_dec(v_fst_1413_);
lean_del_object(v___x_1411_);
lean_dec(v_a_1405_);
lean_del_object(v___x_1333_);
lean_dec(v_fst_1330_);
v_a_1456_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1424_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1424_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_val_1418_);
lean_del_object(v___x_1416_);
lean_dec(v_snd_1414_);
lean_dec(v_fst_1413_);
lean_del_object(v___x_1411_);
lean_dec(v_a_1405_);
lean_del_object(v___x_1333_);
lean_dec(v_fst_1330_);
v_a_1464_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1422_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1422_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_dec(v_val_1418_);
lean_del_object(v___x_1416_);
lean_dec(v_fst_1413_);
lean_del_object(v___x_1411_);
v___y_1337_ = v_a_1405_;
v___y_1338_ = v_snd_1414_;
v___y_1339_ = v___y_1398_;
v___y_1340_ = v___y_1399_;
v___y_1341_ = v___y_1400_;
v___y_1342_ = v___y_1401_;
v___y_1343_ = v___y_1402_;
v___y_1344_ = v___y_1403_;
goto v___jp_1336_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_val_1418_);
lean_del_object(v___x_1416_);
lean_dec(v_snd_1414_);
lean_dec(v_fst_1413_);
lean_del_object(v___x_1411_);
lean_dec(v_a_1405_);
lean_del_object(v___x_1333_);
lean_dec(v_fst_1330_);
v_a_1472_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1419_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1419_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
else
{
lean_object* v_snd_1481_; 
lean_del_object(v___x_1411_);
lean_dec(v_snd_1331_);
v_snd_1481_ = lean_ctor_get(v_snd_1409_, 1);
lean_inc(v_snd_1481_);
lean_dec(v_snd_1409_);
v___y_1337_ = v_a_1405_;
v___y_1338_ = v_snd_1481_;
v___y_1339_ = v___y_1398_;
v___y_1340_ = v___y_1399_;
v___y_1341_ = v___y_1400_;
v___y_1342_ = v___y_1401_;
v___y_1343_ = v___y_1402_;
v___y_1344_ = v___y_1403_;
goto v___jp_1336_;
}
}
}
else
{
lean_object* v_term_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec(v_a_1407_);
lean_del_object(v___x_1333_);
v_term_1484_ = lean_ctor_get(v_a_1335_, 1);
v___x_1485_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7);
v___x_1486_ = l_Lean_indentExpr(v_a_1405_);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1484_, v___x_1487_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1489_; 
lean_dec_ref_known(v___x_1488_, 1);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_fst_1330_);
lean_ctor_set(v___x_1489_, 1, v_snd_1331_);
v_a_1318_ = v___x_1489_;
goto v___jp_1317_;
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_snd_1331_);
lean_dec(v_fst_1330_);
v_a_1490_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1488_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1488_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_a_1405_);
lean_del_object(v___x_1333_);
lean_dec(v_snd_1331_);
lean_dec(v_fst_1330_);
v_a_1498_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1406_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1406_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_del_object(v___x_1333_);
lean_dec(v_snd_1331_);
lean_dec(v_fst_1330_);
v_a_1506_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1404_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1404_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
}
v___jp_1317_:
{
size_t v___x_1319_; size_t v___x_1320_; 
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_add(v_i_1308_, v___x_1319_);
v_i_1308_ = v___x_1320_;
v_b_1309_ = v_a_1318_;
goto _start;
}
v___jp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_____do__lift_1324_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___y_1323_);
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v_a_1318_ = v___x_1327_;
goto v___jp_1317_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1306_ = stack[0].m_obj;
size_t v_sz_1307_ = stack[1].m_num;
size_t v_i_1308_ = stack[2].m_num;
lean_object* v_b_1309_ = stack[3].m_obj;
lean_object* v___y_1310_ = stack[4].m_obj;
lean_object* v___y_1311_ = stack[5].m_obj;
lean_object* v___y_1312_ = stack[6].m_obj;
lean_object* v___y_1313_ = stack[7].m_obj;
lean_object* v___y_1314_ = stack[8].m_obj;
lean_object* v___y_1315_ = stack[9].m_obj;
lean_object* v_res_1538_;
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_as_1306_, v_sz_1307_, v_i_1308_, v_b_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
stack->m_obj
 = v_res_1538_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___boxed(lean_object* v_as_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
size_t v_sz_boxed_1550_; size_t v_i_boxed_1551_; lean_object* v_res_1552_; 
v_sz_boxed_1550_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1551_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_as_1539_, v_sz_boxed_1550_, v_i_boxed_1551_, v_b_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_as_1539_);
return v_res_1552_;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__4(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1558_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__3));
v___x_1559_ = lean_unsigned_to_nat(14u);
v___x_1560_ = lean_unsigned_to_nat(22u);
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__2));
v___x_1562_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__1));
v___x_1563_ = l_mkPanicMessageWithDecl(v___x_1562_, v___x_1561_, v___x_1560_, v___x_1559_, v___x_1558_);
return v___x_1563_;
}
}
lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object* v_steps_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1572_; size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__0));
v_sz_1573_ = lean_array_size(v_steps_1564_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_steps_1564_, v_sz_1573_, v___x_1574_, v___x_1572_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v_fst_1577_; lean_object* v___x_1578_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v_fst_1577_ = lean_ctor_get(v_a_1576_, 0);
lean_inc(v_fst_1577_);
lean_dec(v_a_1576_);
v___x_1578_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1591_; 
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v___x_1578_, 0);
lean_dec(v_unused_1592_);
v___x_1580_ = v___x_1578_;
v_isShared_1581_ = v_isSharedCheck_1591_;
goto v_resetjp_1579_;
}
else
{
lean_dec(v___x_1578_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1591_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
if (lean_obj_tag(v_fst_1577_) == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1582_ = lean_obj_once(&l_Lean_Elab_Term_elabCalcSteps___closed__4, &l_Lean_Elab_Term_elabCalcSteps___closed__4_once, _init_l_Lean_Elab_Term_elabCalcSteps___closed__4);
v___x_1583_ = l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(v___x_1582_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1583_);
v___x_1585_ = v___x_1580_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
else
{
lean_object* v_val_1587_; lean_object* v___x_1589_; 
v_val_1587_ = lean_ctor_get(v_fst_1577_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v_fst_1577_, 1);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v_val_1587_);
v___x_1589_ = v___x_1580_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_val_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_fst_1577_);
v_a_1593_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1578_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1578_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1575_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1575_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_elabCalcSteps_0interp(lean_interpreter_value* stack)
{
lean_object* v_steps_1564_ = stack[0].m_obj;
lean_object* v_a_1565_ = stack[1].m_obj;
lean_object* v_a_1566_ = stack[2].m_obj;
lean_object* v_a_1567_ = stack[3].m_obj;
lean_object* v_a_1568_ = stack[4].m_obj;
lean_object* v_a_1569_ = stack[5].m_obj;
lean_object* v_a_1570_ = stack[6].m_obj;
lean_object* v_res_1609_;
v_res_1609_ = l_Lean_Elab_Term_elabCalcSteps(v_steps_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
stack->m_obj
 = v_res_1609_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps___boxed(lean_object* v_steps_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Elab_Term_elabCalcSteps(v_steps_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec_ref(v_steps_1610_);
return v_res_1618_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(lean_object* v_00_u03b1_1619_, lean_object* v_ref_1620_, lean_object* v_msg_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1620_, v_msg_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1620_ = stack[1].m_obj;
lean_object* v_msg_1621_ = stack[2].m_obj;
lean_object* v___y_1622_ = stack[3].m_obj;
lean_object* v___y_1623_ = stack[4].m_obj;
lean_object* v___y_1624_ = stack[5].m_obj;
lean_object* v___y_1625_ = stack[6].m_obj;
lean_object* v___y_1626_ = stack[7].m_obj;
lean_object* v___y_1627_ = stack[8].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(lean_box(0), v_ref_1620_, v_msg_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___boxed(lean_object* v_00_u03b1_1631_, lean_object* v_ref_1632_, lean_object* v_msg_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(v_00_u03b1_1631_, v_ref_1632_, v_msg_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_ref_1632_);
return v_res_1641_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(lean_object* v_00_u03b1_1642_, lean_object* v_msg_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
return v___x_1651_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1643_ = stack[1].m_obj;
lean_object* v___y_1644_ = stack[2].m_obj;
lean_object* v___y_1645_ = stack[3].m_obj;
lean_object* v___y_1646_ = stack[4].m_obj;
lean_object* v___y_1647_ = stack[5].m_obj;
lean_object* v___y_1648_ = stack[6].m_obj;
lean_object* v___y_1649_ = stack[7].m_obj;
lean_object* v_res_1652_;
v_res_1652_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(lean_box(0), v_msg_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
stack->m_obj
 = v_res_1652_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1653_, lean_object* v_msg_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(v_00_u03b1_1653_, v_msg_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
return v_res_1662_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(lean_object* v_msgData_1663_, lean_object* v_macroStack_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1663_, v_macroStack_1664_, v___y_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1663_ = stack[0].m_obj;
lean_object* v_macroStack_1664_ = stack[1].m_obj;
lean_object* v___y_1665_ = stack[2].m_obj;
lean_object* v___y_1666_ = stack[3].m_obj;
lean_object* v___y_1667_ = stack[4].m_obj;
lean_object* v___y_1668_ = stack[5].m_obj;
lean_object* v___y_1669_ = stack[6].m_obj;
lean_object* v___y_1670_ = stack[7].m_obj;
lean_object* v_res_1673_;
v_res_1673_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(v_msgData_1663_, v_macroStack_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
stack->m_obj
 = v_res_1673_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1674_, lean_object* v_macroStack_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(v_msgData_1674_, v_macroStack_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
return v_res_1683_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_box(0);
v___x_1685_ = l_Lean_Elab_abortTermExceptionId;
v___x_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
return v___x_1686_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg(){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1690_;
v_res_1690_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___boxed(lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v_res_1692_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(lean_object* v_00_u03b1_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v___x_1699_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1694_ = stack[1].m_obj;
lean_object* v___y_1695_ = stack[2].m_obj;
lean_object* v___y_1696_ = stack[3].m_obj;
lean_object* v___y_1697_ = stack[4].m_obj;
lean_object* v_res_1700_;
v_res_1700_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(lean_box(0), v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
stack->m_obj
 = v_res_1700_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___boxed(lean_object* v_00_u03b1_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(v_00_u03b1_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1707_;
}
}
lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(lean_object* v_msg_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___f_1714_; lean_object* v___x_4885__overap_1715_; lean_object* v___x_1716_; 
v___f_1714_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_4885__overap_1715_ = lean_panic_fn_borrowed(v___f_1714_, v_msg_1708_);
lean_inc(v___y_1712_);
lean_inc_ref(v___y_1711_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
v___x_1716_ = lean_apply_5(v___x_4885__overap_1715_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, lean_box(0));
return v___x_1716_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1708_ = stack[0].m_obj;
lean_object* v___y_1709_ = stack[1].m_obj;
lean_object* v___y_1710_ = stack[2].m_obj;
lean_object* v___y_1711_ = stack[3].m_obj;
lean_object* v___y_1712_ = stack[4].m_obj;
lean_object* v_res_1717_;
v_res_1717_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
stack->m_obj
 = v_res_1717_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg___boxed(lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1724_;
}
}
lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(lean_object* v_00_u03b1_1725_, lean_object* v_msg_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1726_ = stack[1].m_obj;
lean_object* v___y_1727_ = stack[2].m_obj;
lean_object* v___y_1728_ = stack[3].m_obj;
lean_object* v___y_1729_ = stack[4].m_obj;
lean_object* v___y_1730_ = stack[5].m_obj;
lean_object* v_res_1733_;
v_res_1733_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(lean_box(0), v_msg_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_msg_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(v_00_u03b1_1734_, v_msg_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1741_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(uint8_t v_suppressElabErrors_1749_, uint8_t v___y_1750_, lean_object* v_x_1751_){
_start:
{
if (lean_obj_tag(v_x_1751_) == 1)
{
lean_object* v_pre_1752_; 
v_pre_1752_ = lean_ctor_get(v_x_1751_, 0);
switch(lean_obj_tag(v_pre_1752_))
{
case 1:
{
lean_object* v_pre_1753_; 
v_pre_1753_ = lean_ctor_get(v_pre_1752_, 0);
switch(lean_obj_tag(v_pre_1753_))
{
case 0:
{
lean_object* v_str_1754_; lean_object* v_str_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_str_1754_ = lean_ctor_get(v_x_1751_, 1);
v_str_1755_ = lean_ctor_get(v_pre_1752_, 1);
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13));
v___x_1757_ = lean_string_dec_eq(v_str_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0));
v___x_1759_ = lean_string_dec_eq(v_str_1755_, v___x_1758_);
if (v___x_1759_ == 0)
{
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1));
v___x_1761_ = lean_string_dec_eq(v_str_1754_, v___x_1760_);
if (v___x_1761_ == 0)
{
return v___x_1761_;
}
else
{
return v_suppressElabErrors_1749_;
}
}
}
else
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2));
v___x_1763_ = lean_string_dec_eq(v_str_1754_, v___x_1762_);
if (v___x_1763_ == 0)
{
return v___x_1763_;
}
else
{
return v_suppressElabErrors_1749_;
}
}
}
case 1:
{
lean_object* v_pre_1764_; 
v_pre_1764_ = lean_ctor_get(v_pre_1753_, 0);
if (lean_obj_tag(v_pre_1764_) == 0)
{
lean_object* v_str_1765_; lean_object* v_str_1766_; lean_object* v_str_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_str_1765_ = lean_ctor_get(v_x_1751_, 1);
v_str_1766_ = lean_ctor_get(v_pre_1752_, 1);
v_str_1767_ = lean_ctor_get(v_pre_1753_, 1);
v___x_1768_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3));
v___x_1769_ = lean_string_dec_eq(v_str_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4));
v___x_1771_ = lean_string_dec_eq(v_str_1766_, v___x_1770_);
if (v___x_1771_ == 0)
{
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5));
v___x_1773_ = lean_string_dec_eq(v_str_1765_, v___x_1772_);
if (v___x_1773_ == 0)
{
return v___x_1773_;
}
else
{
return v_suppressElabErrors_1749_;
}
}
}
}
else
{
return v___y_1750_;
}
}
default: 
{
return v___y_1750_;
}
}
}
case 0:
{
lean_object* v_str_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v_str_1774_ = lean_ctor_get(v_x_1751_, 1);
v___x_1775_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6));
v___x_1776_ = lean_string_dec_eq(v_str_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
return v___x_1776_;
}
else
{
return v_suppressElabErrors_1749_;
}
}
default: 
{
return v___y_1750_;
}
}
}
else
{
return v___y_1750_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_1749_ = stack[0].m_num;
uint8_t v___y_1750_ = stack[1].m_num;
lean_object* v_x_1751_ = stack[2].m_obj;
uint8_t v_res_1777_;
v_res_1777_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(v_suppressElabErrors_1749_, v___y_1750_, v_x_1751_);
stack->m_num = v_res_1777_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1778_, lean_object* v___y_1779_, lean_object* v_x_1780_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1781_; uint8_t v___y_7644__boxed_1782_; uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_suppressElabErrors_boxed_1781_ = lean_unbox(v_suppressElabErrors_1778_);
v___y_7644__boxed_1782_ = lean_unbox(v___y_1779_);
v_res_1783_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_1781_, v___y_7644__boxed_1782_, v_x_1780_);
lean_dec(v_x_1780_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(lean_object* v_ref_1785_, lean_object* v_msgData_1786_, uint8_t v_severity_1787_, uint8_t v_isSilent_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
uint8_t v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; uint8_t v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v_toCold_1802_; lean_object* v___y_1803_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; uint8_t v___y_1835_; lean_object* v___y_1836_; uint8_t v___y_1837_; uint8_t v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1859_; uint8_t v___y_1860_; lean_object* v___y_1861_; uint8_t v___y_1862_; uint8_t v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; uint8_t v___y_1869_; uint8_t v___y_1870_; uint8_t v___y_1871_; uint8_t v___x_1882_; uint8_t v___y_1884_; uint8_t v___y_1885_; uint8_t v___y_1886_; uint8_t v___y_1888_; uint8_t v___x_1896_; 
v___x_1882_ = 2;
v___x_1896_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1787_, v___x_1882_);
if (v___x_1896_ == 0)
{
v___y_1888_ = v___x_1896_;
goto v___jp_1887_;
}
else
{
uint8_t v___x_1897_; 
lean_inc_ref(v_msgData_1786_);
v___x_1897_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1786_);
v___y_1888_ = v___x_1897_;
goto v___jp_1887_;
}
v___jp_1794_:
{
lean_object* v_currNamespace_1804_; lean_object* v_openDecls_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_env_1810_; lean_object* v_nextMacroScope_1811_; lean_object* v_ngen_1812_; lean_object* v_auxDeclNGen_1813_; lean_object* v_traceState_1814_; lean_object* v_cache_1815_; lean_object* v_recordedDeps_1816_; lean_object* v_messages_1817_; lean_object* v_infoState_1818_; lean_object* v_snapshotTasks_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1830_; 
v_currNamespace_1804_ = lean_ctor_get(v_toCold_1802_, 4);
v_openDecls_1805_ = lean_ctor_get(v_toCold_1802_, 5);
lean_inc(v_openDecls_1805_);
lean_inc(v_currNamespace_1804_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v_currNamespace_1804_);
lean_ctor_set(v___x_1806_, 1, v_openDecls_1805_);
v___x_1807_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v___y_1796_);
lean_inc_ref(v___y_1800_);
lean_inc_ref(v___y_1797_);
v___x_1808_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1808_, 0, v___y_1797_);
lean_ctor_set(v___x_1808_, 1, v___y_1798_);
lean_ctor_set(v___x_1808_, 2, v___y_1801_);
lean_ctor_set(v___x_1808_, 3, v___y_1800_);
lean_ctor_set(v___x_1808_, 4, v___x_1807_);
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*5, v___y_1799_);
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*5 + 1, v___y_1795_);
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*5 + 2, v_isSilent_1788_);
v___x_1809_ = lean_st_ref_take(v___y_1803_);
v_env_1810_ = lean_ctor_get(v___x_1809_, 0);
v_nextMacroScope_1811_ = lean_ctor_get(v___x_1809_, 1);
v_ngen_1812_ = lean_ctor_get(v___x_1809_, 2);
v_auxDeclNGen_1813_ = lean_ctor_get(v___x_1809_, 3);
v_traceState_1814_ = lean_ctor_get(v___x_1809_, 4);
v_cache_1815_ = lean_ctor_get(v___x_1809_, 5);
v_recordedDeps_1816_ = lean_ctor_get(v___x_1809_, 6);
v_messages_1817_ = lean_ctor_get(v___x_1809_, 7);
v_infoState_1818_ = lean_ctor_get(v___x_1809_, 8);
v_snapshotTasks_1819_ = lean_ctor_get(v___x_1809_, 9);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1821_ = v___x_1809_;
v_isShared_1822_ = v_isSharedCheck_1830_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_snapshotTasks_1819_);
lean_inc(v_infoState_1818_);
lean_inc(v_messages_1817_);
lean_inc(v_recordedDeps_1816_);
lean_inc(v_cache_1815_);
lean_inc(v_traceState_1814_);
lean_inc(v_auxDeclNGen_1813_);
lean_inc(v_ngen_1812_);
lean_inc(v_nextMacroScope_1811_);
lean_inc(v_env_1810_);
lean_dec(v___x_1809_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1830_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1823_ = lean_box(0);
v___x_1824_ = l_Lean_MessageLog_add(v___x_1808_, v_messages_1817_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 7, v___x_1824_);
v___x_1826_ = v___x_1821_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_env_1810_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_nextMacroScope_1811_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_ngen_1812_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_auxDeclNGen_1813_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_traceState_1814_);
lean_ctor_set(v_reuseFailAlloc_1829_, 5, v_cache_1815_);
lean_ctor_set(v_reuseFailAlloc_1829_, 6, v_recordedDeps_1816_);
lean_ctor_set(v_reuseFailAlloc_1829_, 7, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1829_, 8, v_infoState_1818_);
lean_ctor_set(v_reuseFailAlloc_1829_, 9, v_snapshotTasks_1819_);
v___x_1826_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_st_ref_put(v___y_1803_, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1823_);
return v___x_1828_;
}
}
}
v___jp_1831_:
{
lean_object* v_fileName_1840_; lean_object* v_fileMap_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1857_; 
v_fileName_1840_ = lean_ctor_get(v___y_1836_, 0);
v_fileMap_1841_ = lean_ctor_get(v___y_1836_, 1);
v___x_1842_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1786_);
v___x_1843_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v___x_1842_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1857_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1857_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_inc_ref_n(v_fileMap_1841_, 2);
v___x_1848_ = l_Lean_FileMap_toPosition(v_fileMap_1841_, v___y_1834_);
lean_dec(v___y_1834_);
v___x_1849_ = l_Lean_FileMap_toPosition(v_fileMap_1841_, v___y_1839_);
lean_dec(v___y_1839_);
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
v___x_1851_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
if (v___y_1838_ == 0)
{
lean_del_object(v___x_1846_);
lean_dec_ref(v___y_1833_);
v___y_1795_ = v___y_1835_;
v___y_1796_ = v_a_1844_;
v___y_1797_ = v_fileName_1840_;
v___y_1798_ = v___x_1848_;
v___y_1799_ = v___y_1837_;
v___y_1800_ = v___x_1851_;
v___y_1801_ = v___x_1850_;
v_toCold_1802_ = v___y_1832_;
v___y_1803_ = v___y_1792_;
goto v___jp_1794_;
}
else
{
uint8_t v___x_1852_; 
lean_inc(v_a_1844_);
v___x_1852_ = l_Lean_MessageData_hasTag(v___y_1833_, v_a_1844_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_dec_ref_known(v___x_1850_, 1);
lean_dec_ref(v___x_1848_);
lean_dec(v_a_1844_);
v___x_1853_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1853_);
v___x_1855_ = v___x_1846_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
else
{
lean_del_object(v___x_1846_);
v___y_1795_ = v___y_1835_;
v___y_1796_ = v_a_1844_;
v___y_1797_ = v_fileName_1840_;
v___y_1798_ = v___x_1848_;
v___y_1799_ = v___y_1837_;
v___y_1800_ = v___x_1851_;
v___y_1801_ = v___x_1850_;
v_toCold_1802_ = v___y_1832_;
v___y_1803_ = v___y_1792_;
goto v___jp_1794_;
}
}
}
}
v___jp_1858_:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Syntax_getTailPos_x3f(v___y_1864_, v___y_1863_);
lean_dec(v___y_1864_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_inc(v___y_1865_);
v___y_1832_ = v___y_1859_;
v___y_1833_ = v___y_1861_;
v___y_1834_ = v___y_1865_;
v___y_1835_ = v___y_1862_;
v___y_1836_ = v___y_1859_;
v___y_1837_ = v___y_1863_;
v___y_1838_ = v___y_1860_;
v___y_1839_ = v___y_1865_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1867_; 
v_val_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_val_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___y_1832_ = v___y_1859_;
v___y_1833_ = v___y_1861_;
v___y_1834_ = v___y_1865_;
v___y_1835_ = v___y_1862_;
v___y_1836_ = v___y_1859_;
v___y_1837_ = v___y_1863_;
v___y_1838_ = v___y_1860_;
v___y_1839_ = v_val_1867_;
goto v___jp_1831_;
}
}
v___jp_1868_:
{
lean_object* v_toCold_1872_; lean_object* v_ref_1873_; uint8_t v_suppressElabErrors_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___f_1877_; lean_object* v_ref_1878_; lean_object* v___x_1879_; 
v_toCold_1872_ = lean_ctor_get(v___y_1791_, 0);
v_ref_1873_ = lean_ctor_get(v___y_1791_, 2);
v_suppressElabErrors_1874_ = lean_ctor_get_uint8(v___y_1791_, sizeof(void*)*3 + 2);
v___x_1875_ = lean_box(v_suppressElabErrors_1874_);
v___x_1876_ = lean_box(v___y_1869_);
v___f_1877_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1877_, 0, v___x_1875_);
lean_closure_set(v___f_1877_, 1, v___x_1876_);
v_ref_1878_ = l_Lean_replaceRef(v_ref_1785_, v_ref_1873_);
v___x_1879_ = l_Lean_Syntax_getPos_x3f(v_ref_1878_, v___y_1870_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___y_1859_ = v_toCold_1872_;
v___y_1860_ = v_suppressElabErrors_1874_;
v___y_1861_ = v___f_1877_;
v___y_1862_ = v___y_1871_;
v___y_1863_ = v___y_1870_;
v___y_1864_ = v_ref_1878_;
v___y_1865_ = v___x_1880_;
goto v___jp_1858_;
}
else
{
lean_object* v_val_1881_; 
v_val_1881_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_val_1881_);
lean_dec_ref_known(v___x_1879_, 1);
v___y_1859_ = v_toCold_1872_;
v___y_1860_ = v_suppressElabErrors_1874_;
v___y_1861_ = v___f_1877_;
v___y_1862_ = v___y_1871_;
v___y_1863_ = v___y_1870_;
v___y_1864_ = v_ref_1878_;
v___y_1865_ = v_val_1881_;
goto v___jp_1858_;
}
}
v___jp_1883_:
{
if (v___y_1886_ == 0)
{
v___y_1869_ = v___y_1884_;
v___y_1870_ = v___y_1885_;
v___y_1871_ = v_severity_1787_;
goto v___jp_1868_;
}
else
{
v___y_1869_ = v___y_1884_;
v___y_1870_ = v___y_1885_;
v___y_1871_ = v___x_1882_;
goto v___jp_1868_;
}
}
v___jp_1887_:
{
if (v___y_1888_ == 0)
{
uint8_t v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = 1;
v___x_1890_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1787_, v___x_1889_);
if (v___x_1890_ == 0)
{
v___y_1884_ = v___y_1888_;
v___y_1885_ = v___y_1888_;
v___y_1886_ = v___x_1890_;
goto v___jp_1883_;
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1891_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1791_);
v___x_1892_ = l_Lean_warningAsError;
v___x_1893_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v___x_1891_, v___x_1892_);
lean_dec_ref(v___x_1891_);
v___y_1884_ = v___y_1888_;
v___y_1885_ = v___y_1888_;
v___y_1886_ = v___x_1893_;
goto v___jp_1883_;
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec_ref(v_msgData_1786_);
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1785_ = stack[0].m_obj;
lean_object* v_msgData_1786_ = stack[1].m_obj;
uint8_t v_severity_1787_ = stack[2].m_num;
uint8_t v_isSilent_1788_ = stack[3].m_num;
lean_object* v___y_1789_ = stack[4].m_obj;
lean_object* v___y_1790_ = stack[5].m_obj;
lean_object* v___y_1791_ = stack[6].m_obj;
lean_object* v___y_1792_ = stack[7].m_obj;
lean_object* v_res_1898_;
v_res_1898_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1785_, v_msgData_1786_, v_severity_1787_, v_isSilent_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
stack->m_obj
 = v_res_1898_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___boxed(lean_object* v_ref_1899_, lean_object* v_msgData_1900_, lean_object* v_severity_1901_, lean_object* v_isSilent_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
uint8_t v_severity_boxed_1908_; uint8_t v_isSilent_boxed_1909_; lean_object* v_res_1910_; 
v_severity_boxed_1908_ = lean_unbox(v_severity_1901_);
v_isSilent_boxed_1909_ = lean_unbox(v_isSilent_1902_);
v_res_1910_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1899_, v_msgData_1900_, v_severity_boxed_1908_, v_isSilent_boxed_1909_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v_ref_1899_);
return v_res_1910_;
}
}
lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(lean_object* v_ref_1911_, lean_object* v_msgData_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
uint8_t v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = 2;
v___x_1919_ = 0;
v___x_1920_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1911_, v_msgData_1912_, v___x_1918_, v___x_1919_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v___x_1920_;
}
}
LEAN_EXPORT void l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1911_ = stack[0].m_obj;
lean_object* v_msgData_1912_ = stack[1].m_obj;
lean_object* v___y_1913_ = stack[2].m_obj;
lean_object* v___y_1914_ = stack[3].m_obj;
lean_object* v___y_1915_ = stack[4].m_obj;
lean_object* v___y_1916_ = stack[5].m_obj;
lean_object* v_res_1921_;
v_res_1921_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_ref_1911_, v_msgData_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
stack->m_obj
 = v_res_1921_;
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1___boxed(lean_object* v_ref_1922_, lean_object* v_msgData_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_ref_1922_, v_msgData_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v_ref_1922_);
return v_res_1929_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1));
v___x_1934_ = l_Lean_MessageData_ofFormat(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2);
v___x_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4));
v___x_1939_ = l_Lean_stringToMessageData(v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6));
v___x_1942_ = l_Lean_stringToMessageData(v___x_1941_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1944_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_1945_ = lean_unsigned_to_nat(57u);
v___x_1946_ = lean_unsigned_to_nat(133u);
v___x_1947_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8));
v___x_1948_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_1949_ = l_mkPanicMessageWithDecl(v___x_1948_, v___x_1947_, v___x_1946_, v___x_1945_, v___x_1944_);
return v___x_1949_;
}
}
lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object* v_steps_1950_, lean_object* v_expectedType_1951_, lean_object* v_result_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_Lean_Elab_Term_instInhabitedCalcStepView_default));
lean_inc(v_a_1956_);
lean_inc_ref(v_a_1955_);
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc_ref(v_result_1952_);
v___x_1959_ = lean_infer_type(v_result_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; lean_object* v_a_1962_; lean_object* v___x_1963_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___x_1986_; lean_object* v_a_1987_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1961_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_1960_, v_a_1954_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1961_);
v___x_1963_ = l_Lean_Expr_headBeta(v_a_1962_);
v___x_1986_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_1963_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
if (lean_obj_tag(v_a_1987_) == 1)
{
lean_object* v_val_1988_; lean_object* v_snd_1989_; lean_object* v_fst_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2234_; 
v_val_1988_ = lean_ctor_get(v_a_1987_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v_a_1987_, 1);
v_snd_1989_ = lean_ctor_get(v_val_1988_, 1);
v_fst_1990_ = lean_ctor_get(v_val_1988_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_val_1988_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_1992_ = v_val_1988_;
v_isShared_1993_ = v_isSharedCheck_2234_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_snd_1989_);
lean_inc(v_fst_1990_);
lean_dec(v_val_1988_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2234_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_fst_1994_; lean_object* v_snd_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2233_; 
v_fst_1994_ = lean_ctor_get(v_snd_1989_, 0);
v_snd_1995_ = lean_ctor_get(v_snd_1989_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_snd_1989_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_1997_ = v_snd_1989_;
v_isShared_1998_ = v_isSharedCheck_2233_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_snd_1995_);
lean_inc(v_fst_1994_);
lean_dec(v_snd_1989_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2233_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v_a_2000_; 
v___x_1999_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_expectedType_1951_);
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v___x_1999_);
if (lean_obj_tag(v_a_2000_) == 1)
{
lean_object* v_val_2001_; lean_object* v_snd_2002_; lean_object* v_fst_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2232_; 
v_val_2001_ = lean_ctor_get(v_a_2000_, 0);
lean_inc(v_val_2001_);
lean_dec_ref_known(v_a_2000_, 1);
v_snd_2002_ = lean_ctor_get(v_val_2001_, 1);
v_fst_2003_ = lean_ctor_get(v_val_2001_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_val_2001_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2005_ = v_val_2001_;
v_isShared_2006_ = v_isSharedCheck_2232_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2002_);
lean_inc(v_fst_2003_);
lean_dec(v_val_2001_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2232_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2231_; 
v_fst_2007_ = lean_ctor_get(v_snd_2002_, 0);
v_snd_2008_ = lean_ctor_get(v_snd_2002_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_snd_2002_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2010_ = v_snd_2002_;
v_isShared_2011_ = v_isSharedCheck_2231_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_snd_2002_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2231_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
uint8_t v_failed_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1990_, v_fst_2003_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; uint8_t v___x_2125_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = lean_unbox(v_a_2124_);
if (v___x_2125_ == 0)
{
lean_dec(v_a_2124_);
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_dec(v_fst_2007_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_dec(v_fst_1994_);
lean_del_object(v___x_1992_);
v___y_1965_ = v_a_1953_;
v___y_1966_ = v_a_1954_;
v___y_1967_ = v_a_1955_;
v___y_1968_ = v_a_1956_;
goto v___jp_1964_;
}
else
{
uint8_t v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = 0;
lean_inc(v_fst_2007_);
lean_inc(v_fst_1994_);
v___x_2127_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1994_, v_fst_2007_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; uint8_t v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = lean_unbox(v_a_2128_);
lean_dec(v_a_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_1994_, v_fst_2007_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v_fst_2132_; lean_object* v_snd_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2206_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v_fst_2132_ = lean_ctor_get(v_a_2131_, 0);
v_snd_2133_ = lean_ctor_get(v_a_2131_, 1);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_a_2131_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2135_ = v_a_2131_;
v_isShared_2136_ = v_isSharedCheck_2206_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_snd_2133_);
lean_inc(v_fst_2132_);
lean_dec(v_a_2131_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2206_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; 
lean_inc(v_a_1956_);
lean_inc_ref(v_a_1955_);
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc(v_fst_2132_);
v___x_2137_ = lean_infer_type(v_fst_2132_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
lean_inc(v_a_1956_);
lean_inc_ref(v_a_1955_);
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc(v_snd_2133_);
v___x_2139_ = lean_infer_type(v_snd_2133_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2138_, v_a_2140_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v_fst_2143_; lean_object* v_snd_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2181_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v_fst_2143_ = lean_ctor_get(v_a_2142_, 0);
v_snd_2144_ = lean_ctor_get(v_a_2142_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_a_2142_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2146_ = v_a_2142_;
v_isShared_2147_ = v_isSharedCheck_2181_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_snd_2144_);
lean_inc(v_fst_2143_);
lean_dec(v_a_2142_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2181_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v_term_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = lean_array_get_borrowed(v___x_1958_, v_steps_1950_, v___x_2148_);
v_term_2150_ = lean_ctor_get(v___x_2149_, 1);
v___x_2151_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_2152_ = l_Lean_MessageData_ofExpr(v_fst_2132_);
v___x_2153_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 7);
lean_ctor_set(v___x_2146_, 1, v___x_2153_);
lean_ctor_set(v___x_2146_, 0, v___x_2152_);
v___x_2155_ = v___x_2146_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = l_Lean_MessageData_ofExpr(v_fst_2143_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 7);
lean_ctor_set(v___x_2135_, 1, v___x_2156_);
lean_ctor_set(v___x_2135_, 0, v___x_2155_);
v___x_2158_ = v___x_2135_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2159_ = l_Lean_indentD(v___x_2158_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2151_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_MessageData_ofExpr(v_snd_2133_);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set(v___x_2164_, 1, v___x_2153_);
v___x_2165_ = l_Lean_MessageData_ofExpr(v_snd_2144_);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = l_Lean_indentD(v___x_2166_);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2162_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2150_, v___x_2168_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_2169_) == 0)
{
uint8_t v___x_2170_; 
lean_dec_ref_known(v___x_2169_, 1);
v___x_2170_ = lean_unbox(v_a_2124_);
lean_dec(v_a_2124_);
v_failed_2013_ = v___x_2170_;
v___y_2014_ = v_a_1953_;
v___y_2015_ = v_a_1954_;
v___y_2016_ = v_a_1955_;
v___y_2017_ = v_a_1956_;
goto v___jp_2012_;
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_a_2124_);
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v_a_2171_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2169_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2169_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_del_object(v___x_2135_);
lean_dec(v_snd_2133_);
lean_dec(v_fst_2132_);
lean_dec(v_a_2124_);
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v_a_2182_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2141_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2141_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_a_2138_);
lean_del_object(v___x_2135_);
lean_dec(v_snd_2133_);
lean_dec(v_fst_2132_);
lean_dec(v_a_2124_);
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v_a_2190_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2139_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2139_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_del_object(v___x_2135_);
lean_dec(v_snd_2133_);
lean_dec(v_fst_2132_);
lean_dec(v_a_2124_);
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v_a_2198_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2137_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2137_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_a_2124_);
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v_a_2207_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2130_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2130_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
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
lean_dec(v_a_2124_);
lean_dec(v_fst_2007_);
lean_dec(v_fst_1994_);
v_failed_2013_ = v___x_2126_;
v___y_2014_ = v_a_1953_;
v___y_2015_ = v_a_1954_;
v___y_2016_ = v_a_1955_;
v___y_2017_ = v_a_1956_;
goto v___jp_2012_;
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2124_);
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_dec(v_fst_2007_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_dec(v_fst_1994_);
lean_del_object(v___x_1992_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v_a_2215_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2127_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2127_);
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
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_dec(v_fst_2007_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_dec(v_fst_1994_);
lean_del_object(v___x_1992_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v_a_2223_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2123_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2123_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
v___jp_2012_:
{
lean_object* v___x_2018_; 
lean_inc(v_snd_2008_);
lean_inc(v_snd_1995_);
v___x_2018_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_1995_, v_snd_2008_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; uint8_t v___x_2020_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = lean_unbox(v_a_2019_);
lean_dec(v_a_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v___x_2021_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_snd_1995_, v_snd_2008_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v_fst_2023_; lean_object* v_snd_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2106_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v_fst_2023_ = lean_ctor_get(v_a_2022_, 0);
v_snd_2024_ = lean_ctor_get(v_a_2022_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_a_2022_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2026_ = v_a_2022_;
v_isShared_2027_ = v_isSharedCheck_2106_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_snd_2024_);
lean_inc(v_fst_2023_);
lean_dec(v_a_2022_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2106_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; 
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
lean_inc(v_fst_2023_);
v___x_2028_ = lean_infer_type(v_fst_2023_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
lean_inc(v_snd_2024_);
v___x_2030_ = lean_infer_type(v_snd_2024_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2029_, v_a_2031_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v_fst_2034_; lean_object* v_snd_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2081_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v_fst_2034_ = lean_ctor_get(v_a_2033_, 0);
v_snd_2035_ = lean_ctor_get(v_a_2033_, 1);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_a_2033_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2037_ = v_a_2033_;
v_isShared_2038_ = v_isSharedCheck_2081_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_snd_2035_);
lean_inc(v_fst_2034_);
lean_dec(v_a_2033_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2081_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v_term_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2039_ = lean_array_get_size(v_steps_1950_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_sub(v___x_2039_, v___x_2040_);
v___x_2042_ = lean_array_get_borrowed(v___x_1958_, v_steps_1950_, v___x_2041_);
lean_dec(v___x_2041_);
v_term_2043_ = lean_ctor_get(v___x_2042_, 1);
v___x_2044_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5);
v___x_2045_ = l_Lean_MessageData_ofExpr(v_fst_2023_);
v___x_2046_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2038_ == 0)
{
lean_ctor_set_tag(v___x_2037_, 7);
lean_ctor_set(v___x_2037_, 1, v___x_2046_);
lean_ctor_set(v___x_2037_, 0, v___x_2045_);
v___x_2048_ = v___x_2037_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2049_ = l_Lean_MessageData_ofExpr(v_fst_2034_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set_tag(v___x_2026_, 7);
lean_ctor_set(v___x_2026_, 1, v___x_2049_);
lean_ctor_set(v___x_2026_, 0, v___x_2048_);
v___x_2051_ = v___x_2026_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = l_Lean_indentD(v___x_2051_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 7);
lean_ctor_set(v___x_2010_, 1, v___x_2052_);
lean_ctor_set(v___x_2010_, 0, v___x_2044_);
v___x_2054_ = v___x_2010_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 7);
lean_ctor_set(v___x_2005_, 1, v___x_2055_);
lean_ctor_set(v___x_2005_, 0, v___x_2054_);
v___x_2057_ = v___x_2005_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = l_Lean_MessageData_ofExpr(v_snd_2024_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 7);
lean_ctor_set(v___x_1997_, 1, v___x_2046_);
lean_ctor_set(v___x_1997_, 0, v___x_2058_);
v___x_2060_ = v___x_1997_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2046_);
v___x_2060_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2061_ = l_Lean_MessageData_ofExpr(v_snd_2035_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 7);
lean_ctor_set(v___x_1992_, 1, v___x_2061_);
lean_ctor_set(v___x_1992_, 0, v___x_2060_);
v___x_2063_ = v___x_1992_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = l_Lean_indentD(v___x_2063_);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2057_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2043_, v___x_2065_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_dec_ref_known(v___x_2066_, 1);
v___y_1973_ = v___y_2014_;
v___y_1974_ = v___y_2015_;
v___y_1975_ = v___y_2016_;
v___y_1976_ = v___y_2017_;
goto v___jp_1972_;
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
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
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_del_object(v___x_2026_);
lean_dec(v_snd_2024_);
lean_dec(v_fst_2023_);
lean_del_object(v___x_2010_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_del_object(v___x_1992_);
v_a_2082_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2032_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2032_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v_a_2029_);
lean_del_object(v___x_2026_);
lean_dec(v_snd_2024_);
lean_dec(v_fst_2023_);
lean_del_object(v___x_2010_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_del_object(v___x_1992_);
v_a_2090_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2030_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2030_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_del_object(v___x_2026_);
lean_dec(v_snd_2024_);
lean_dec(v_fst_2023_);
lean_del_object(v___x_2010_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_del_object(v___x_1992_);
v_a_2098_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2028_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2028_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_del_object(v___x_2010_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_del_object(v___x_1992_);
v_a_2107_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2021_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2021_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_del_object(v___x_1992_);
if (v_failed_2013_ == 0)
{
v___y_1965_ = v___y_2014_;
v___y_1966_ = v___y_2015_;
v___y_1967_ = v___y_2016_;
v___y_1968_ = v___y_2017_;
goto v___jp_1964_;
}
else
{
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v___y_1973_ = v___y_2014_;
v___y_1974_ = v___y_2015_;
v___y_1975_ = v___y_2016_;
v___y_1976_ = v___y_2017_;
goto v___jp_1972_;
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v_a_2115_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2018_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2018_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2000_);
lean_del_object(v___x_1997_);
lean_dec(v_snd_1995_);
lean_dec(v_fst_1994_);
lean_del_object(v___x_1992_);
lean_dec(v_fst_1990_);
v___y_1965_ = v_a_1953_;
v___y_1966_ = v_a_1954_;
v___y_1967_ = v_a_1955_;
v___y_1968_ = v_a_1956_;
goto v___jp_1964_;
}
}
}
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec(v_a_1987_);
lean_dec_ref(v___x_1963_);
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v___x_2235_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9);
v___x_2236_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v___x_2235_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
return v___x_2236_;
}
v___jp_1964_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3);
v___x_1970_ = lean_box(0);
v___x_1971_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1969_, v_expectedType_1951_, v___x_1963_, v_result_1952_, v___x_1970_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
return v___x_1971_;
}
v___jp_1972_:
{
lean_object* v___x_1977_; lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v___x_1977_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref(v_result_1952_);
lean_dec_ref(v_expectedType_1951_);
v_a_2237_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_1959_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_1959_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
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
}
LEAN_EXPORT void l_Lean_Elab_Term_throwCalcFailure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_steps_1950_ = stack[0].m_obj;
lean_object* v_expectedType_1951_ = stack[1].m_obj;
lean_object* v_result_1952_ = stack[2].m_obj;
lean_object* v_a_1953_ = stack[3].m_obj;
lean_object* v_a_1954_ = stack[4].m_obj;
lean_object* v_a_1955_ = stack[5].m_obj;
lean_object* v_a_1956_ = stack[6].m_obj;
lean_object* v_res_2245_;
v_res_2245_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_1950_, v_expectedType_1951_, v_result_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
stack->m_obj
 = v_res_2245_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(lean_object* v_steps_2246_, lean_object* v_expectedType_2247_, lean_object* v_result_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2246_, v_expectedType_2247_, v_result_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec_ref(v_steps_2246_);
return v_res_2254_;
}
}
lean_object* l_Lean_Elab_Term_throwCalcFailure(lean_object* v_00_u03b1_2255_, lean_object* v_steps_2256_, lean_object* v_expectedType_2257_, lean_object* v_result_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2256_, v_expectedType_2257_, v_result_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2264_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_throwCalcFailure_0interp(lean_interpreter_value* stack)
{
lean_object* v_steps_2256_ = stack[1].m_obj;
lean_object* v_expectedType_2257_ = stack[2].m_obj;
lean_object* v_result_2258_ = stack[3].m_obj;
lean_object* v_a_2259_ = stack[4].m_obj;
lean_object* v_a_2260_ = stack[5].m_obj;
lean_object* v_a_2261_ = stack[6].m_obj;
lean_object* v_a_2262_ = stack[7].m_obj;
lean_object* v_res_2265_;
v_res_2265_ = l_Lean_Elab_Term_throwCalcFailure(lean_box(0), v_steps_2256_, v_expectedType_2257_, v_result_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
stack->m_obj
 = v_res_2265_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___boxed(lean_object* v_00_u03b1_2266_, lean_object* v_steps_2267_, lean_object* v_expectedType_2268_, lean_object* v_result_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Elab_Term_throwCalcFailure(v_00_u03b1_2266_, v_steps_2267_, v_expectedType_2268_, v_result_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec_ref(v_steps_2267_);
return v_res_2275_;
}
}
lean_object* l_Lean_Elab_Term_elabCalc___lam__0(lean_object* v_a_2276_, lean_object* v_x_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2276_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_elabCalc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2276_ = stack[0].m_obj;
lean_object* v_x_2277_ = stack[1].m_obj;
lean_object* v___y_2278_ = stack[2].m_obj;
lean_object* v___y_2279_ = stack[3].m_obj;
lean_object* v___y_2280_ = stack[4].m_obj;
lean_object* v___y_2281_ = stack[5].m_obj;
lean_object* v___y_2282_ = stack[6].m_obj;
lean_object* v___y_2283_ = stack[7].m_obj;
lean_object* v_res_2286_;
v_res_2286_ = l_Lean_Elab_Term_elabCalc___lam__0(v_a_2276_, v_x_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
stack->m_obj
 = v_res_2286_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0___boxed(lean_object* v_a_2287_, lean_object* v_x_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Elab_Term_elabCalc___lam__0(v_a_2287_, v_x_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v_x_2288_);
lean_dec_ref(v_a_2287_);
return v_res_2296_;
}
}
lean_object* l_Lean_Elab_Term_elabCalc___lam__1(lean_object* v_a_2297_, lean_object* v_x_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2297_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_elabCalc___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2297_ = stack[0].m_obj;
lean_object* v_x_2298_ = stack[1].m_obj;
lean_object* v___y_2299_ = stack[2].m_obj;
lean_object* v___y_2300_ = stack[3].m_obj;
lean_object* v___y_2301_ = stack[4].m_obj;
lean_object* v___y_2302_ = stack[5].m_obj;
lean_object* v___y_2303_ = stack[6].m_obj;
lean_object* v___y_2304_ = stack[7].m_obj;
lean_object* v_res_2307_;
v_res_2307_ = l_Lean_Elab_Term_elabCalc___lam__1(v_a_2297_, v_x_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
stack->m_obj
 = v_res_2307_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1___boxed(lean_object* v_a_2308_, lean_object* v_x_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_Elab_Term_elabCalc___lam__1(v_a_2308_, v_x_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v_x_2309_);
lean_dec_ref(v_a_2308_);
return v_res_2317_;
}
}
lean_object* l_Lean_Elab_Term_elabCalc(lean_object* v_x_2322_, lean_object* v_x_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
lean_inc(v_x_2322_);
v___x_2332_ = l_Lean_Syntax_isOfKind(v_x_2322_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
lean_dec(v_x_2323_);
lean_dec(v_x_2322_);
v___x_2333_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2333_;
}
else
{
lean_object* v___x_2334_; lean_object* v_steps_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2334_ = lean_unsigned_to_nat(1u);
v_steps_2335_ = l_Lean_Syntax_getArg(v_x_2322_, v___x_2334_);
v___x_2336_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_2335_);
v___x_2337_ = l_Lean_Syntax_isOfKind(v_steps_2335_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
lean_dec(v_steps_2335_);
lean_dec(v_x_2323_);
lean_dec(v_x_2322_);
v___x_2338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2338_;
}
else
{
lean_object* v_toCold_2339_; lean_object* v_currRecDepth_2340_; lean_object* v_ref_2341_; uint16_t v_optionFlags_2342_; uint8_t v_suppressElabErrors_2343_; uint8_t v_isRecordingDeps_2344_; lean_object* v___x_2345_; lean_object* v_tk_2346_; lean_object* v_ref_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_toCold_2339_ = lean_ctor_get(v_a_2328_, 0);
v_currRecDepth_2340_ = lean_ctor_get(v_a_2328_, 1);
v_ref_2341_ = lean_ctor_get(v_a_2328_, 2);
v_optionFlags_2342_ = lean_ctor_get_uint16(v_a_2328_, sizeof(void*)*3);
v_suppressElabErrors_2343_ = lean_ctor_get_uint8(v_a_2328_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2344_ = lean_ctor_get_uint8(v_a_2328_, sizeof(void*)*3 + 3);
v___x_2345_ = lean_unsigned_to_nat(0u);
v_tk_2346_ = l_Lean_Syntax_getArg(v_x_2322_, v___x_2345_);
lean_dec(v_x_2322_);
v_ref_2347_ = l_Lean_replaceRef(v_tk_2346_, v_ref_2341_);
lean_dec(v_tk_2346_);
lean_inc(v_currRecDepth_2340_);
lean_inc_ref(v_toCold_2339_);
v___x_2348_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2348_, 0, v_toCold_2339_);
lean_ctor_set(v___x_2348_, 1, v_currRecDepth_2340_);
lean_ctor_set(v___x_2348_, 2, v_ref_2347_);
lean_ctor_set_uint16(v___x_2348_, sizeof(void*)*3, v_optionFlags_2342_);
lean_ctor_set_uint8(v___x_2348_, sizeof(void*)*3 + 2, v_suppressElabErrors_2343_);
lean_ctor_set_uint8(v___x_2348_, sizeof(void*)*3 + 3, v_isRecordingDeps_2344_);
v___x_2349_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_2335_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v___x_2348_, v_a_2329_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___f_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc_n(v_a_2350_, 3);
lean_dec_ref_known(v___x_2349_, 1);
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2351_, 0, v_a_2350_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__1___boxed), 9, 1);
lean_closure_set(v___f_2352_, 0, v_a_2350_);
v___x_2353_ = l_Lean_Elab_Term_elabCalcSteps(v_a_2350_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v___x_2348_, v_a_2329_);
lean_dec(v_a_2350_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v_fst_2355_; lean_object* v___x_2356_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v_fst_2355_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_fst_2355_);
lean_dec(v_a_2354_);
v___x_2356_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(v_x_2323_, v_fst_2355_, v___f_2351_, v___f_2352_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v___x_2348_, v_a_2329_);
lean_dec_ref_known(v___x_2348_, 3);
return v___x_2356_;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v___f_2352_);
lean_dec_ref(v___f_2351_);
lean_dec_ref_known(v___x_2348_, 3);
lean_dec(v_x_2323_);
v_a_2357_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2353_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2353_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref_known(v___x_2348_, 3);
lean_dec(v_x_2323_);
v_a_2365_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2349_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2349_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_elabCalc_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2322_ = stack[0].m_obj;
lean_object* v_x_2323_ = stack[1].m_obj;
lean_object* v_a_2324_ = stack[2].m_obj;
lean_object* v_a_2325_ = stack[3].m_obj;
lean_object* v_a_2326_ = stack[4].m_obj;
lean_object* v_a_2327_ = stack[5].m_obj;
lean_object* v_a_2328_ = stack[6].m_obj;
lean_object* v_a_2329_ = stack[7].m_obj;
lean_object* v_res_2373_;
v_res_2373_ = l_Lean_Elab_Term_elabCalc(v_x_2322_, v_x_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
stack->m_obj
 = v_res_2373_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Elab_Term_elabCalc(v_x_2374_, v_x_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2383_;
}
}
lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1(){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2391_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2392_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
v___x_2393_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2394_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___boxed), 9, 0);
v___x_2395_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2391_, v___x_2392_, v___x_2393_, v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2396_;
v_res_2396_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
stack->m_obj
 = v_res_2396_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___boxed(lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
return v_res_2398_;
}
}
lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3(){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2402_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0));
v___x_2403_ = l_Lean_addBuiltinDocString(v___x_2401_, v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2404_;
v_res_2404_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
stack->m_obj
 = v_res_2404_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___boxed(lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
return v_res_2406_;
}
}
lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5(){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2434_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6));
v___x_2435_ = l_Lean_addBuiltinDeclarationRanges(v___x_2433_, v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2436_;
v_res_2436_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
stack->m_obj
 = v_res_2436_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___boxed(lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
return v_res_2438_;
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
