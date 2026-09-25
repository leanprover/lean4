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
lean_object* v___x_120_; lean_object* v_env_121_; lean_object* v___x_122_; lean_object* v_toCold_123_; lean_object* v_mctx_124_; lean_object* v_lctx_125_; lean_object* v_options_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_120_ = lean_st_ref_get(v___y_118_);
v_env_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc_ref(v_env_121_);
lean_dec(v___x_120_);
v___x_122_ = lean_st_ref_get(v___y_116_);
v_toCold_123_ = lean_ctor_get(v___y_117_, 0);
v_mctx_124_ = lean_ctor_get(v___x_122_, 0);
lean_inc_ref(v_mctx_124_);
lean_dec(v___x_122_);
v_lctx_125_ = lean_ctor_get(v___y_115_, 2);
v_options_126_ = lean_ctor_get(v_toCold_123_, 2);
lean_inc_ref(v_options_126_);
lean_inc_ref(v_lctx_125_);
v___x_127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_127_, 0, v_env_121_);
lean_ctor_set(v___x_127_, 1, v_mctx_124_);
lean_ctor_set(v___x_127_, 2, v_lctx_125_);
lean_ctor_set(v___x_127_, 3, v_options_126_);
v___x_128_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v_msgData_114_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0___boxed(lean_object* v_msgData_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msgData_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_ref_143_; lean_object* v___x_144_; lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_153_; 
v_ref_143_ = lean_ctor_get(v___y_140_, 2);
v___x_144_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_153_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
lean_inc(v_ref_143_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v_ref_143_);
lean_ctor_set(v___x_149_, 1, v_a_145_);
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 1);
lean_ctor_set(v___x_147_, 0, v___x_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg___boxed(lean_object* v_msg_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_160_;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0));
v___x_163_ = l_Lean_stringToMessageData(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(lean_object* v_a_164_, lean_object* v_x_165_, lean_object* v_sort_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; 
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_172_ = lean_whnf(v_sort_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_185_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
if (lean_obj_tag(v_a_173_) == 3)
{
lean_object* v_u_177_; lean_object* v___x_179_; 
lean_dec_ref(v_a_164_);
v_u_177_ = lean_ctor_get(v_a_173_, 0);
lean_inc(v_u_177_);
lean_dec_ref_known(v_a_173_, 1);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v_u_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_u_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_del_object(v___x_175_);
lean_dec(v_a_173_);
v___x_181_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1);
v___x_182_ = l_Lean_indentExpr(v_a_164_);
v___x_183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_183_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
return v___x_184_;
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec_ref(v_a_164_);
v_a_186_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_172_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_172_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed(lean_object* v_a_194_, lean_object* v_x_195_, lean_object* v_sort_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(v_a_194_, v_x_195_, v_sort_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec_ref(v_x_195_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(lean_object* v_r_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; 
lean_inc(v_a_207_);
lean_inc_ref(v_a_206_);
lean_inc(v_a_205_);
lean_inc_ref(v_a_204_);
v___x_209_ = lean_infer_type(v_r_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___f_211_; uint8_t v___x_212_; lean_object* v___x_213_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc_n(v_a_210_, 2);
lean_dec_ref_known(v___x_209_, 1);
v___f_211_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed), 8, 1);
lean_closure_set(v___f_211_, 0, v_a_210_);
v___x_212_ = 0;
v___x_213_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_a_210_, v___f_211_, v___x_212_, v___x_212_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
return v___x_213_;
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
v_a_214_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_209_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_209_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___boxed(lean_object* v_r_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_r_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(lean_object* v_00_u03b1_229_, lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___boxed(lean_object* v_00_u03b1_237_, lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(v_00_u03b1_237_, v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(lean_object* v_e_245_, lean_object* v___y_246_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = l_Lean_Expr_hasMVar(v_e_245_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v_e_245_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; lean_object* v_mctx_251_; lean_object* v___x_252_; lean_object* v_fst_253_; lean_object* v_snd_254_; lean_object* v___x_255_; lean_object* v_cache_256_; lean_object* v_zetaDeltaFVarIds_257_; lean_object* v_postponed_258_; lean_object* v_diag_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_268_; 
v___x_250_ = lean_st_ref_get(v___y_246_);
v_mctx_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc_ref(v_mctx_251_);
lean_dec(v___x_250_);
v___x_252_ = l_Lean_instantiateMVarsCore(v_mctx_251_, v_e_245_);
v_fst_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_fst_253_);
v_snd_254_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_snd_254_);
lean_dec_ref(v___x_252_);
v___x_255_ = lean_st_ref_take(v___y_246_);
v_cache_256_ = lean_ctor_get(v___x_255_, 1);
v_zetaDeltaFVarIds_257_ = lean_ctor_get(v___x_255_, 2);
v_postponed_258_ = lean_ctor_get(v___x_255_, 3);
v_diag_259_ = lean_ctor_get(v___x_255_, 4);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; 
v_unused_269_ = lean_ctor_get(v___x_255_, 0);
lean_dec(v_unused_269_);
v___x_261_ = v___x_255_;
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_diag_259_);
lean_inc(v_postponed_258_);
lean_inc(v_zetaDeltaFVarIds_257_);
lean_inc(v_cache_256_);
lean_dec(v___x_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v_snd_254_);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_snd_254_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_cache_256_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_zetaDeltaFVarIds_257_);
lean_ctor_set(v_reuseFailAlloc_267_, 3, v_postponed_258_);
lean_ctor_set(v_reuseFailAlloc_267_, 4, v_diag_259_);
v___x_264_ = v_reuseFailAlloc_267_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_st_ref_put(v___y_246_, v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v_fst_253_);
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg___boxed(lean_object* v_e_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_e_270_, v___y_271_);
lean_dec(v___y_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(lean_object* v_e_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_e_274_, v___y_276_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___boxed(lean_object* v_e_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(v_e_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___f_295_; lean_object* v___x_7150__overap_296_; lean_object* v___x_297_; 
v___f_295_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_7150__overap_296_ = lean_panic_fn_borrowed(v___f_295_, v_msg_289_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
v___x_297_ = lean_apply_5(v___x_7150__overap_296_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, lean_box(0));
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___boxed(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__5(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__4));
v___x_314_ = l_Lean_stringToMessageData(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__7(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__6));
v___x_317_ = l_Lean_stringToMessageData(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__11(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_321_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_322_ = lean_unsigned_to_nat(72u);
v___x_323_ = lean_unsigned_to_nat(35u);
v___x_324_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__9));
v___x_325_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_326_ = l_mkPanicMessageWithDecl(v___x_325_, v___x_324_, v___x_323_, v___x_322_, v___x_321_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__12(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_327_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_328_ = lean_unsigned_to_nat(53u);
v___x_329_ = lean_unsigned_to_nat(34u);
v___x_330_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__9));
v___x_331_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_332_ = l_mkPanicMessageWithDecl(v___x_331_, v___x_330_, v___x_329_, v___x_328_, v___x_327_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object* v_result_333_, lean_object* v_resultType_334_, lean_object* v_step_335_, lean_object* v_stepType_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_342_; lean_object* v_a_343_; 
v___x_342_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_resultType_334_);
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref(v___x_342_);
if (lean_obj_tag(v_a_343_) == 1)
{
lean_object* v_val_344_; lean_object* v_snd_345_; lean_object* v_fst_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_602_; 
v_val_344_ = lean_ctor_get(v_a_343_, 0);
lean_inc(v_val_344_);
lean_dec_ref_known(v_a_343_, 1);
v_snd_345_ = lean_ctor_get(v_val_344_, 1);
v_fst_346_ = lean_ctor_get(v_val_344_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v_val_344_);
if (v_isSharedCheck_602_ == 0)
{
v___x_348_ = v_val_344_;
v_isShared_349_ = v_isSharedCheck_602_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snd_345_);
lean_inc(v_fst_346_);
lean_dec(v_val_344_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_602_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_601_; 
v_fst_350_ = lean_ctor_get(v_snd_345_, 0);
v_snd_351_ = lean_ctor_get(v_snd_345_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_snd_345_);
if (v_isSharedCheck_601_ == 0)
{
v___x_353_ = v_snd_345_;
v_isShared_354_ = v_isSharedCheck_601_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_snd_351_);
lean_inc(v_fst_350_);
lean_dec(v_snd_345_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_601_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v_a_358_; 
v___x_355_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_stepType_336_, v_a_338_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref(v___x_355_);
v___x_357_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_356_);
lean_dec(v_a_356_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
if (lean_obj_tag(v_a_358_) == 1)
{
lean_object* v_val_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_598_; 
v_val_359_ = lean_ctor_get(v_a_358_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_a_358_);
if (v_isSharedCheck_598_ == 0)
{
v___x_361_ = v_a_358_;
v_isShared_362_ = v_isSharedCheck_598_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_val_359_);
lean_dec(v_a_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_598_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v_snd_363_; lean_object* v_fst_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_597_; 
v_snd_363_ = lean_ctor_get(v_val_359_, 1);
v_fst_364_ = lean_ctor_get(v_val_359_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_val_359_);
if (v_isSharedCheck_597_ == 0)
{
v___x_366_ = v_val_359_;
v_isShared_367_ = v_isSharedCheck_597_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_snd_363_);
lean_inc(v_fst_364_);
lean_dec(v_val_359_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_597_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_snd_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_595_; 
v_snd_368_ = lean_ctor_get(v_snd_363_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_snd_363_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v_snd_363_, 0);
lean_dec(v_unused_596_);
v___x_370_ = v_snd_363_;
v_isShared_371_ = v_isSharedCheck_595_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_snd_368_);
lean_dec(v_snd_363_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_595_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; 
lean_inc(v_fst_346_);
v___x_372_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_fst_346_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
lean_inc(v_fst_364_);
v___x_374_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_fst_364_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
lean_inc(v_a_338_);
lean_inc_ref(v_a_337_);
lean_inc(v_fst_350_);
v___x_376_ = lean_infer_type(v_fst_350_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
lean_inc(v_a_338_);
lean_inc_ref(v_a_337_);
lean_inc(v_snd_351_);
v___x_378_ = lean_infer_type(v_snd_351_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_378_, 1);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
lean_inc(v_a_338_);
lean_inc_ref(v_a_337_);
lean_inc(v_snd_368_);
v___x_380_ = lean_infer_type(v_snd_368_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
lean_inc(v_a_377_);
v___x_382_ = l_Lean_Meta_getLevel(v_a_377_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
lean_inc(v_a_379_);
v___x_384_ = l_Lean_Meta_getLevel(v_a_379_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
lean_inc(v_a_381_);
v___x_386_ = l_Lean_Meta_getLevel(v_a_381_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v___x_388_ = l_Lean_Meta_mkFreshLevelMVar(v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_n(v_a_389_, 2);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = l_Lean_mkSort(v_a_389_);
lean_inc(v_a_381_);
v___x_391_ = l_Lean_mkArrow(v_a_381_, v___x_390_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
lean_inc(v_a_377_);
v___x_393_ = l_Lean_mkArrow(v_a_377_, v_a_392_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v_a_394_);
v___x_396_ = v___x_361_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_394_);
v___x_396_ = v_reuseFailAlloc_506_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = 0;
v___x_398_ = lean_box(0);
v___x_399_ = l_Lean_Meta_mkFreshExprMVar(v___x_396_, v___x_397_, v___x_398_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v___x_401_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__1));
v___x_402_ = lean_box(0);
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 1);
lean_ctor_set(v___x_366_, 1, v___x_402_);
lean_ctor_set(v___x_366_, 0, v_a_387_);
v___x_404_ = v___x_366_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_387_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_402_);
v___x_404_ = v_reuseFailAlloc_497_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 1);
lean_ctor_set(v___x_353_, 1, v___x_404_);
lean_ctor_set(v___x_353_, 0, v_a_385_);
v___x_406_ = v___x_353_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_385_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_496_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 1);
lean_ctor_set(v___x_348_, 1, v___x_406_);
lean_ctor_set(v___x_348_, 0, v_a_383_);
v___x_408_ = v___x_348_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_383_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_495_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v_a_389_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v_a_375_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v_a_373_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
lean_inc_ref(v___x_411_);
v___x_412_ = l_Lean_mkConst(v___x_401_, v___x_411_);
v___x_413_ = lean_unsigned_to_nat(6u);
v___x_414_ = lean_mk_empty_array_with_capacity(v___x_413_);
lean_inc(v_a_377_);
v___x_415_ = lean_array_push(v___x_414_, v_a_377_);
lean_inc(v_a_379_);
v___x_416_ = lean_array_push(v___x_415_, v_a_379_);
lean_inc(v_a_381_);
v___x_417_ = lean_array_push(v___x_416_, v_a_381_);
lean_inc(v_fst_346_);
v___x_418_ = lean_array_push(v___x_417_, v_fst_346_);
lean_inc(v_fst_364_);
v___x_419_ = lean_array_push(v___x_418_, v_fst_364_);
lean_inc(v_a_400_);
v___x_420_ = lean_array_push(v___x_419_, v_a_400_);
v___x_421_ = l_Lean_mkAppN(v___x_412_, v___x_420_);
lean_dec_ref(v___x_420_);
v___x_422_ = lean_box(0);
lean_inc_ref(v___x_421_);
v___x_423_ = l_Lean_Meta_trySynthInstance(v___x_421_, v___x_422_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
if (lean_obj_tag(v_a_424_) == 1)
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec_ref(v___x_421_);
v_a_425_ = lean_ctor_get(v_a_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v_a_424_, 1);
v___x_426_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__3));
v___x_427_ = l_Lean_mkConst(v___x_426_, v___x_411_);
v___x_428_ = lean_unsigned_to_nat(12u);
v___x_429_ = lean_mk_empty_array_with_capacity(v___x_428_);
v___x_430_ = lean_array_push(v___x_429_, v_a_377_);
v___x_431_ = lean_array_push(v___x_430_, v_a_379_);
v___x_432_ = lean_array_push(v___x_431_, v_a_381_);
v___x_433_ = lean_array_push(v___x_432_, v_fst_346_);
v___x_434_ = lean_array_push(v___x_433_, v_fst_364_);
v___x_435_ = lean_array_push(v___x_434_, v_a_400_);
v___x_436_ = lean_array_push(v___x_435_, v_a_425_);
v___x_437_ = lean_array_push(v___x_436_, v_fst_350_);
v___x_438_ = lean_array_push(v___x_437_, v_snd_351_);
v___x_439_ = lean_array_push(v___x_438_, v_snd_368_);
v___x_440_ = lean_array_push(v___x_439_, v_result_333_);
v___x_441_ = lean_array_push(v___x_440_, v_step_335_);
v___x_442_ = l_Lean_mkAppN(v___x_427_, v___x_441_);
lean_dec_ref(v___x_441_);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
lean_inc(v_a_338_);
lean_inc_ref(v_a_337_);
lean_inc_ref(v___x_442_);
v___x_443_ = lean_infer_type(v___x_442_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_472_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_444_, v_a_338_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_472_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_472_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_472_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_458_; lean_object* v_a_459_; 
v___x_450_ = l_Lean_Expr_headBeta(v_a_446_);
v___x_458_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_450_);
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref(v___x_458_);
if (lean_obj_tag(v_a_459_) == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_del_object(v___x_448_);
lean_dec_ref(v___x_442_);
lean_del_object(v___x_370_);
v___x_460_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__5, &l_Lean_Elab_Term_mkCalcTrans___closed__5_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__5);
v___x_461_ = l_Lean_indentExpr(v___x_450_);
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_462_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
lean_dec_ref_known(v_a_459_, 1);
goto v___jp_451_;
}
v___jp_451_:
{
lean_object* v___x_453_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v___x_450_);
lean_ctor_set(v___x_370_, 0, v___x_442_);
v___x_453_ = v___x_370_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_450_);
v___x_453_ = v_reuseFailAlloc_457_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_455_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_453_);
v___x_455_ = v___x_448_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec_ref(v___x_442_);
lean_del_object(v___x_370_);
v_a_473_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_443_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_443_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_a_424_);
lean_dec_ref_known(v___x_411_, 2);
lean_dec(v_a_400_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_dec(v_fst_364_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v___x_481_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__7, &l_Lean_Elab_Term_mkCalcTrans___closed__7_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__7);
v___x_482_ = l_Lean_indentExpr(v___x_421_);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Lean_useDiagnosticMsg;
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_485_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
return v___x_486_;
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec_ref(v___x_421_);
lean_dec_ref_known(v___x_411_, 2);
lean_dec(v_a_400_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_dec(v_fst_364_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_487_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_423_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_423_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_a_389_);
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_498_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_399_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_399_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v_a_389_);
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_507_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_393_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_393_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec(v_a_389_);
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_515_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_391_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_391_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_523_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_388_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_388_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_385_);
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_531_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_386_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_386_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_a_383_);
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_539_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_384_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_384_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_381_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_547_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_382_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_382_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_555_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_380_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_380_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_a_377_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_563_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_378_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_378_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_571_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_376_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_376_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec(v_a_373_);
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_579_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_374_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_374_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_del_object(v___x_370_);
lean_dec(v_snd_368_);
lean_del_object(v___x_366_);
lean_dec(v_fst_364_);
lean_del_object(v___x_361_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v_a_587_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_372_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_372_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_a_358_);
lean_del_object(v___x_353_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
lean_del_object(v___x_348_);
lean_dec(v_fst_346_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v___x_599_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__11, &l_Lean_Elab_Term_mkCalcTrans___closed__11_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__11);
v___x_600_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v___x_599_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
return v___x_600_;
}
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_a_343_);
lean_dec_ref(v_stepType_336_);
lean_dec_ref(v_step_335_);
lean_dec_ref(v_result_333_);
v___x_603_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__12, &l_Lean_Elab_Term_mkCalcTrans___closed__12_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__12);
v___x_604_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v___x_603_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___boxed(lean_object* v_result_605_, lean_object* v_resultType_606_, lean_object* v_step_607_, lean_object* v_stepType_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Elab_Term_mkCalcTrans(v_result_605_, v_resultType_606_, v_step_607_, v_stepType_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec_ref(v_resultType_606_);
return v_res_614_;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
v___x_637_ = l_String_toRawSubstring_x27(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(lean_object* v_type_662_, lean_object* v_t_663_, uint8_t v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
if (v_a_664_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec_ref(v_type_662_);
v___x_672_ = lean_box(v_a_664_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v_t_663_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
else
{
if (lean_obj_tag(v_t_663_) == 1)
{
lean_object* v_info_675_; lean_object* v_kind_676_; lean_object* v_args_677_; lean_object* v_k_679_; uint8_t v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; 
v_info_675_ = lean_ctor_get(v_t_663_, 0);
v_kind_676_ = lean_ctor_get(v_t_663_, 1);
v_args_677_ = lean_ctor_get(v_t_663_, 2);
if (lean_obj_tag(v_kind_676_) == 1)
{
lean_object* v_pre_716_; 
v_pre_716_ = lean_ctor_get(v_kind_676_, 0);
if (lean_obj_tag(v_pre_716_) == 1)
{
lean_object* v_pre_717_; 
v_pre_717_ = lean_ctor_get(v_pre_716_, 0);
if (lean_obj_tag(v_pre_717_) == 1)
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_pre_717_, 0);
if (lean_obj_tag(v_pre_718_) == 1)
{
lean_object* v_pre_719_; 
v_pre_719_ = lean_ctor_get(v_pre_718_, 0);
if (lean_obj_tag(v_pre_719_) == 0)
{
lean_object* v_str_720_; lean_object* v_str_721_; lean_object* v_str_722_; lean_object* v_str_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_str_720_ = lean_ctor_get(v_kind_676_, 1);
v_str_721_ = lean_ctor_get(v_pre_716_, 1);
v_str_722_ = lean_ctor_get(v_pre_717_, 1);
v_str_723_ = lean_ctor_get(v_pre_718_, 1);
v___x_724_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0));
v___x_725_ = lean_string_dec_eq(v_str_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_inc_ref(v_kind_676_);
lean_inc_ref(v_args_677_);
lean_inc(v_info_675_);
lean_dec_ref_known(v_t_663_, 3);
v_k_679_ = v_kind_676_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
goto v___jp_678_;
}
else
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1));
v___x_727_ = lean_string_dec_eq(v_str_722_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_inc_ref(v_str_722_);
lean_inc_ref(v_str_721_);
lean_inc(v_pre_719_);
lean_inc_ref(v_str_720_);
lean_inc_ref(v_args_677_);
lean_inc(v_info_675_);
lean_dec_ref_known(v_t_663_, 3);
v___x_728_ = l_Lean_Name_str___override(v_pre_719_, v___x_724_);
v___x_729_ = l_Lean_Name_str___override(v___x_728_, v_str_722_);
v___x_730_ = l_Lean_Name_str___override(v___x_729_, v_str_721_);
v___x_731_ = l_Lean_Name_str___override(v___x_730_, v_str_720_);
v_k_679_ = v___x_731_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
goto v___jp_678_;
}
else
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2));
v___x_733_ = lean_string_dec_eq(v_str_721_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_inc_ref(v_str_721_);
lean_inc(v_pre_719_);
lean_inc_ref(v_str_720_);
lean_inc_ref(v_args_677_);
lean_inc(v_info_675_);
lean_dec_ref_known(v_t_663_, 3);
v___x_734_ = l_Lean_Name_str___override(v_pre_719_, v___x_724_);
v___x_735_ = l_Lean_Name_str___override(v___x_734_, v___x_726_);
v___x_736_ = l_Lean_Name_str___override(v___x_735_, v_str_721_);
v___x_737_ = l_Lean_Name_str___override(v___x_736_, v_str_720_);
v_k_679_ = v___x_737_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
goto v___jp_678_;
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3));
v___x_739_ = lean_string_dec_eq(v_str_720_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_inc(v_pre_719_);
lean_inc_ref(v_str_720_);
lean_inc_ref(v_args_677_);
lean_inc(v_info_675_);
lean_dec_ref_known(v_t_663_, 3);
v___x_740_ = l_Lean_Name_str___override(v_pre_719_, v___x_724_);
v___x_741_ = l_Lean_Name_str___override(v___x_740_, v___x_726_);
v___x_742_ = l_Lean_Name_str___override(v___x_741_, v___x_732_);
v___x_743_ = l_Lean_Name_str___override(v___x_742_, v_str_720_);
v_k_679_ = v___x_743_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
goto v___jp_678_;
}
else
{
uint8_t v___x_744_; lean_object* v___x_745_; 
v___x_744_ = 0;
v___x_745_ = l_Lean_Elab_Term_exprToSyntax(v_type_662_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_toCold_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_778_; 
v_toCold_746_ = lean_ctor_get(v_a_669_, 0);
v_a_747_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_778_ == 0)
{
v___x_749_ = v___x_745_;
v_isShared_750_ = v_isSharedCheck_778_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_778_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_ref_751_; lean_object* v_quotContext_752_; lean_object* v_currMacroScope_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v_ref_751_ = lean_ctor_get(v_a_669_, 2);
v_quotContext_752_ = lean_ctor_get(v_toCold_746_, 8);
v_currMacroScope_753_ = lean_ctor_get(v_toCold_746_, 9);
v___x_754_ = l_Lean_SourceInfo_fromRef(v_ref_751_, v___x_744_);
v___x_755_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5));
v___x_756_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7));
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8));
lean_inc_n(v___x_754_, 7);
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_754_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10));
v___x_760_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12);
lean_inc(v_currMacroScope_753_);
lean_inc(v_quotContext_752_);
v___x_761_ = l_Lean_addMacroScope(v_quotContext_752_, v_pre_719_, v_currMacroScope_753_);
v___x_762_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20));
v___x_763_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_763_, 0, v___x_754_);
lean_ctor_set(v___x_763_, 1, v___x_760_);
lean_ctor_set(v___x_763_, 2, v___x_761_);
lean_ctor_set(v___x_763_, 3, v___x_762_);
v___x_764_ = l_Lean_Syntax_node1(v___x_754_, v___x_759_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node2(v___x_754_, v___x_756_, v___x_758_, v___x_764_);
v___x_766_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21));
v___x_767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_754_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23));
v___x_769_ = l_Lean_Syntax_node1(v___x_754_, v___x_768_, v_a_747_);
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24));
v___x_771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_754_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_Syntax_node5(v___x_754_, v___x_755_, v___x_765_, v_t_663_, v___x_767_, v___x_769_, v___x_771_);
v___x_773_ = lean_box(v___x_744_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_774_);
v___x_776_ = v___x_749_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref_known(v_t_663_, 3);
v_a_779_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_745_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_745_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
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
lean_inc_ref(v_kind_676_);
lean_inc_ref(v_args_677_);
lean_inc(v_info_675_);
lean_dec_ref_known(v_t_663_, 3);
v_k_679_ = v_kind_676_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
goto v___jp_678_;
}
}
else
{
lean_inc_ref(v_kind_676_);
lean_inc_ref(v_args_677_);
lean_inc(v_info_675_);
lean_dec_ref_known(v_t_663_, 3);
v_k_679_ = v_kind_676_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
goto v___jp_678_;
}
}
else
{
lean_inc_ref(v_kind_676_);
lean_inc_ref(v_args_677_);
lean_inc(v_info_675_);
lean_dec_ref_known(v_t_663_, 3);
v_k_679_ = v_kind_676_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
goto v___jp_678_;
}
}
else
{
lean_inc_ref(v_kind_676_);
lean_inc_ref(v_args_677_);
lean_inc(v_info_675_);
lean_dec_ref_known(v_t_663_, 3);
v_k_679_ = v_kind_676_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
goto v___jp_678_;
}
}
else
{
lean_inc_ref(v_args_677_);
lean_inc(v_kind_676_);
lean_inc(v_info_675_);
lean_dec_ref_known(v_t_663_, 3);
v_k_679_ = v_kind_676_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
v___y_686_ = v_a_670_;
goto v___jp_678_;
}
v___jp_678_:
{
size_t v_sz_687_; size_t v___x_688_; lean_object* v___x_689_; 
v_sz_687_ = lean_array_size(v_args_677_);
v___x_688_ = ((size_t)0ULL);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_662_, v_sz_687_, v___x_688_, v_args_677_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_707_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_707_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_707_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_707_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_706_; 
v_fst_694_ = lean_ctor_get(v_a_690_, 0);
v_snd_695_ = lean_ctor_get(v_a_690_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_a_690_);
if (v_isSharedCheck_706_ == 0)
{
v___x_697_ = v_a_690_;
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snd_695_);
lean_inc(v_fst_694_);
lean_dec(v_a_690_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_699_, 0, v_info_675_);
lean_ctor_set(v___x_699_, 1, v_k_679_);
lean_ctor_set(v___x_699_, 2, v_fst_694_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_699_);
v___x_701_ = v___x_697_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_snd_695_);
v___x_701_ = v_reuseFailAlloc_705_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_703_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_701_);
v___x_703_ = v___x_692_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_k_679_);
lean_dec(v_info_675_);
v_a_708_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_689_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_689_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
else
{
uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref(v_type_662_);
v___x_787_ = 0;
v___x_788_ = lean_box(v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_t_663_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(lean_object* v_type_791_, size_t v_sz_792_, size_t v_i_793_, lean_object* v_bs_794_, uint8_t v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_usize_dec_lt(v_i_793_, v_sz_792_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_type_791_);
v___x_804_ = lean_box(v___y_795_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_bs_794_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
else
{
lean_object* v_v_807_; lean_object* v___x_808_; lean_object* v_bs_x27_809_; lean_object* v___x_810_; 
v_v_807_ = lean_array_uget(v_bs_794_, v_i_793_);
v___x_808_ = lean_unsigned_to_nat(0u);
v_bs_x27_809_ = lean_array_uset(v_bs_794_, v_i_793_, v___x_808_);
lean_inc_ref(v_type_791_);
v___x_810_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_791_, v_v_807_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v_fst_812_; lean_object* v_snd_813_; size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v_fst_812_ = lean_ctor_get(v_a_811_, 0);
lean_inc(v_fst_812_);
v_snd_813_ = lean_ctor_get(v_a_811_, 1);
lean_inc(v_snd_813_);
lean_dec(v_a_811_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_i_793_, v___x_814_);
v___x_816_ = lean_array_uset(v_bs_x27_809_, v_i_793_, v_fst_812_);
v___x_817_ = lean_unbox(v_snd_813_);
lean_dec(v_snd_813_);
v_i_793_ = v___x_815_;
v_bs_794_ = v___x_816_;
v___y_795_ = v___x_817_;
goto _start;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_bs_x27_809_);
lean_dec_ref(v_type_791_);
v_a_819_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_810_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_810_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0___boxed(lean_object* v_type_827_, lean_object* v_sz_828_, lean_object* v_i_829_, lean_object* v_bs_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
size_t v_sz_boxed_839_; size_t v_i_boxed_840_; uint8_t v___y_7635__boxed_841_; lean_object* v_res_842_; 
v_sz_boxed_839_ = lean_unbox_usize(v_sz_828_);
lean_dec(v_sz_828_);
v_i_boxed_840_ = lean_unbox_usize(v_i_829_);
lean_dec(v_i_829_);
v___y_7635__boxed_841_ = lean_unbox(v___y_831_);
v_res_842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_827_, v_sz_boxed_839_, v_i_boxed_840_, v_bs_830_, v___y_7635__boxed_841_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object* v_type_843_, lean_object* v_t_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
uint8_t v_a_7704__boxed_853_; lean_object* v_res_854_; 
v_a_7704__boxed_853_ = lean_unbox(v_a_845_);
v_res_854_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_843_, v_t_844_, v_a_7704__boxed_853_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object* v_t_855_, lean_object* v_type_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
uint8_t v___x_864_; lean_object* v___x_865_; 
v___x_864_ = 1;
v___x_865_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_856_, v_t_855_, v___x_864_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_874_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_874_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_fst_870_; lean_object* v___x_872_; 
v_fst_870_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_fst_870_);
lean_dec(v_a_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v_fst_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_fst_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_865_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_865_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType___boxed(lean_object* v_t_883_, lean_object* v_type_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_t_883_, v_type_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
return v_res_892_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_box(0);
v___x_898_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___x_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg(){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___boxed(lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(lean_object* v_00_u03b1_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___boxed(lean_object* v_00_u03b1_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(v_00_u03b1_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_922_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__7));
v___x_939_ = l_String_toRawSubstring_x27(v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView(lean_object* v_step0_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_toCold_956_; lean_object* v_ref_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_toCold_956_ = lean_ctor_get(v_a_953_, 0);
v_ref_957_ = lean_ctor_get(v_a_953_, 2);
v___x_958_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_948_);
v___x_959_ = l_Lean_Syntax_isOfKind(v_step0_948_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec(v_step0_948_);
v___x_960_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v_term_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v_term_962_ = l_Lean_Syntax_getArg(v_step0_948_, v___x_961_);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = l_Lean_Syntax_getArg(v_step0_948_, v___x_963_);
lean_inc(v___x_964_);
v___x_965_ = l_Lean_Syntax_matchesNull(v___x_964_, v___x_961_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_964_);
v___x_967_ = l_Lean_Syntax_matchesNull(v___x_964_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_dec(v___x_964_);
lean_dec(v_term_962_);
lean_dec(v_step0_948_);
v___x_968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_968_;
}
else
{
lean_object* v_proof_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_proof_969_ = l_Lean_Syntax_getArg(v___x_964_, v___x_963_);
lean_dec(v___x_964_);
v___x_970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_970_, 0, v_step0_948_);
lean_ctor_set(v___x_970_, 1, v_term_962_);
lean_ctor_set(v___x_970_, 2, v_proof_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
else
{
lean_object* v_ref_972_; uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v_quotContext_979_; lean_object* v_currMacroScope_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v___x_964_);
v_ref_972_ = l_Lean_replaceRef(v_step0_948_, v_ref_957_);
v___x_973_ = 0;
v___x_974_ = l_Lean_SourceInfo_fromRef(v_ref_972_, v___x_973_);
lean_dec(v_ref_972_);
v___x_975_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__2));
lean_inc_n(v___x_974_, 4);
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__3));
v___x_978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_974_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v_quotContext_979_ = lean_ctor_get(v_toCold_956_, 8);
v_currMacroScope_980_ = lean_ctor_get(v_toCold_956_, 9);
v___x_981_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__4));
v___x_982_ = l_Lean_Syntax_node1(v___x_974_, v___x_981_, v___x_978_);
v___x_983_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__6));
v___x_984_ = l_Lean_Syntax_node3(v___x_974_, v___x_983_, v_term_962_, v___x_976_, v___x_982_);
v___x_985_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcFirstStepView___closed__8, &l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once, _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__9));
lean_inc(v_currMacroScope_980_);
lean_inc(v_quotContext_979_);
v___x_987_ = l_Lean_addMacroScope(v_quotContext_979_, v___x_986_, v_currMacroScope_980_);
v___x_988_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__11));
v___x_989_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_989_, 0, v___x_974_);
lean_ctor_set(v___x_989_, 1, v___x_985_);
lean_ctor_set(v___x_989_, 2, v___x_987_);
lean_ctor_set(v___x_989_, 3, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_990_, 0, v_step0_948_);
lean_ctor_set(v___x_990_, 1, v___x_984_);
lean_ctor_set(v___x_990_, 2, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___boxed(lean_object* v_step0_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(lean_object* v_as_1005_, size_t v_sz_1006_, size_t v_i_1007_, lean_object* v_b_1008_){
_start:
{
lean_object* v_a_1011_; uint8_t v___x_1015_; 
v___x_1015_ = lean_usize_dec_lt(v_i_1007_, v_sz_1006_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_b_1008_);
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; lean_object* v_a_1018_; uint8_t v___x_1019_; 
v___x_1017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1));
v_a_1018_ = lean_array_uget_borrowed(v_as_1005_, v_i_1007_);
lean_inc(v_a_1018_);
v___x_1019_ = l_Lean_Syntax_isOfKind(v_a_1018_, v___x_1017_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_dec_ref_known(v___x_1020_, 1);
v_a_1011_ = v_b_1008_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v_b_1008_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = l_Lean_Syntax_getArg(v_a_1018_, v___x_1029_);
v___x_1031_ = lean_unsigned_to_nat(2u);
v___x_1032_ = l_Lean_Syntax_getArg(v_a_1018_, v___x_1031_);
lean_inc(v_a_1018_);
v___x_1033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1033_, 0, v_a_1018_);
lean_ctor_set(v___x_1033_, 1, v___x_1030_);
lean_ctor_set(v___x_1033_, 2, v___x_1032_);
v___x_1034_ = lean_array_push(v_b_1008_, v___x_1033_);
v_a_1011_ = v___x_1034_;
goto v___jp_1010_;
}
}
v___jp_1010_:
{
size_t v___x_1012_; size_t v___x_1013_; 
v___x_1012_ = ((size_t)1ULL);
v___x_1013_ = lean_usize_add(v_i_1007_, v___x_1012_);
v_i_1007_ = v___x_1013_;
v_b_1008_ = v_a_1011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___boxed(lean_object* v_as_1035_, lean_object* v_sz_1036_, lean_object* v_i_1037_, lean_object* v_b_1038_, lean_object* v___y_1039_){
_start:
{
size_t v_sz_boxed_1040_; size_t v_i_boxed_1041_; lean_object* v_res_1042_; 
v_sz_boxed_1040_ = lean_unbox_usize(v_sz_1036_);
lean_dec(v_sz_1036_);
v_i_boxed_1041_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_res_1042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1035_, v_sz_boxed_1040_, v_i_boxed_1041_, v_b_1038_);
lean_dec_ref(v_as_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object* v_steps_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_1047_);
v___x_1056_ = l_Lean_Syntax_isOfKind(v_steps_1047_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec(v_steps_1047_);
v___x_1057_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v_step0_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
v_step0_1059_ = l_Lean_Syntax_getArg(v_steps_1047_, v___x_1058_);
v___x_1060_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_1059_);
v___x_1061_ = l_Lean_Syntax_isOfKind(v_step0_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
lean_dec(v_step0_1059_);
lean_dec(v_steps_1047_);
v___x_1062_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_rest_1065_; lean_object* v___x_1066_; 
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = l_Lean_Syntax_getArg(v_steps_1047_, v___x_1063_);
lean_dec(v_steps_1047_);
v_rest_1065_ = l_Lean_Syntax_getArgs(v___x_1064_);
lean_dec(v___x_1064_);
v___x_1066_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_1059_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; size_t v_sz_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = lean_mk_empty_array_with_capacity(v___x_1063_);
v___x_1069_ = lean_array_push(v___x_1068_, v_a_1067_);
v_sz_1070_ = lean_array_size(v_rest_1065_);
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_rest_1065_, v_sz_1070_, v___x_1071_, v___x_1069_);
lean_dec_ref(v_rest_1065_);
return v___x_1072_;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_rest_1065_);
v_a_1073_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1066_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1066_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews___boxed(lean_object* v_steps_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(lean_object* v_as_1090_, size_t v_sz_1091_, size_t v_i_1092_, lean_object* v_b_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1090_, v_sz_1091_, v_i_1092_, v_b_1093_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(lean_object* v_as_1102_, lean_object* v_sz_1103_, lean_object* v_i_1104_, lean_object* v_b_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
size_t v_sz_boxed_1113_; size_t v_i_boxed_1114_; lean_object* v_res_1115_; 
v_sz_boxed_1113_ = lean_unbox_usize(v_sz_1103_);
lean_dec(v_sz_1103_);
v_i_boxed_1114_ = lean_unbox_usize(v_i_1104_);
lean_dec(v_i_1104_);
v_res_1115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(v_as_1102_, v_sz_boxed_1113_, v_i_boxed_1114_, v_b_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v_as_1102_);
return v_res_1115_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = l_Lean_instInhabitedExpr;
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(lean_object* v_msg_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_obj_once(&l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0, &l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0);
v___x_1120_ = lean_panic_fn_borrowed(v___x_1119_, v_msg_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(lean_object* v_opts_1121_, lean_object* v_opt_1122_){
_start:
{
lean_object* v_name_1123_; lean_object* v_defValue_1124_; lean_object* v_map_1125_; lean_object* v___x_1126_; 
v_name_1123_ = lean_ctor_get(v_opt_1122_, 0);
v_defValue_1124_ = lean_ctor_get(v_opt_1122_, 1);
v_map_1125_ = lean_ctor_get(v_opts_1121_, 0);
v___x_1126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1125_, v_name_1123_);
if (lean_obj_tag(v___x_1126_) == 0)
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_unbox(v_defValue_1124_);
return v___x_1127_;
}
else
{
lean_object* v_val_1128_; 
v_val_1128_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v___x_1126_, 1);
if (lean_obj_tag(v_val_1128_) == 1)
{
uint8_t v_v_1129_; 
v_v_1129_ = lean_ctor_get_uint8(v_val_1128_, 0);
lean_dec_ref_known(v_val_1128_, 0);
return v_v_1129_;
}
else
{
uint8_t v___x_1130_; 
lean_dec(v_val_1128_);
v___x_1130_ = lean_unbox(v_defValue_1124_);
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_opts_1131_, lean_object* v_opt_1132_){
_start:
{
uint8_t v_res_1133_; lean_object* v_r_1134_; 
v_res_1133_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_opts_1131_, v_opt_1132_);
lean_dec_ref(v_opt_1132_);
lean_dec_ref(v_opts_1131_);
v_r_1134_ = lean_box(v_res_1133_);
return v_r_1134_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_box(1);
v___x_1136_ = l_Lean_MessageData_ofFormat(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2));
v___x_1141_ = l_Lean_MessageData_ofFormat(v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
if (lean_obj_tag(v_x_1143_) == 0)
{
return v_x_1142_;
}
else
{
lean_object* v_head_1144_; lean_object* v_tail_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1167_; 
v_head_1144_ = lean_ctor_get(v_x_1143_, 0);
v_tail_1145_ = lean_ctor_get(v_x_1143_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1143_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1147_ = v_x_1143_;
v_isShared_1148_ = v_isSharedCheck_1167_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_tail_1145_);
lean_inc(v_head_1144_);
lean_dec(v_x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1167_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_before_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1165_; 
v_before_1149_ = lean_ctor_get(v_head_1144_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_head_1144_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v_head_1144_, 1);
lean_dec(v_unused_1166_);
v___x_1151_ = v_head_1144_;
v_isShared_1152_ = v_isSharedCheck_1165_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_before_1149_);
lean_dec(v_head_1144_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1165_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 7);
lean_ctor_set(v___x_1151_, 1, v___x_1153_);
lean_ctor_set(v___x_1151_, 0, v_x_1142_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_x_1142_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3);
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 7);
lean_ctor_set(v___x_1147_, 1, v___x_1156_);
lean_ctor_set(v___x_1147_, 0, v___x_1155_);
v___x_1158_ = v___x_1147_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = l_Lean_MessageData_ofSyntax(v_before_1149_);
v___x_1160_ = l_Lean_indentD(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1158_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v_x_1142_ = v___x_1161_;
v_x_1143_ = v_tail_1145_;
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
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_1172_ = l_Lean_MessageData_ofFormat(v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_1173_, lean_object* v_macroStack_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1177_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1175_);
v___x_1178_ = l_Lean_Elab_pp_macroStack;
v___x_1179_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v___x_1177_, v___x_1178_);
lean_dec_ref(v___x_1177_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
lean_dec(v_macroStack_1174_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_msgData_1173_);
return v___x_1180_;
}
else
{
if (lean_obj_tag(v_macroStack_1174_) == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_msgData_1173_);
return v___x_1181_;
}
else
{
lean_object* v_head_1182_; lean_object* v_after_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1198_; 
v_head_1182_ = lean_ctor_get(v_macroStack_1174_, 0);
lean_inc(v_head_1182_);
v_after_1183_ = lean_ctor_get(v_head_1182_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_head_1182_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v_head_1182_, 0);
lean_dec(v_unused_1199_);
v___x_1185_ = v_head_1182_;
v_isShared_1186_ = v_isSharedCheck_1198_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_after_1183_);
lean_dec(v_head_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1198_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1186_ == 0)
{
lean_ctor_set_tag(v___x_1185_, 7);
lean_ctor_set(v___x_1185_, 1, v___x_1187_);
lean_ctor_set(v___x_1185_, 0, v_msgData_1173_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_msgData_1173_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_msgData_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1190_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Lean_MessageData_ofSyntax(v_after_1183_);
v___x_1193_ = l_Lean_indentD(v___x_1192_);
v_msgData_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1194_, 0, v___x_1191_);
lean_ctor_set(v_msgData_1194_, 1, v___x_1193_);
v___x_1195_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(v_msgData_1194_, v_macroStack_1174_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1200_, lean_object* v_macroStack_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1200_, v_macroStack_1201_, v___y_1202_);
lean_dec_ref(v___y_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(lean_object* v_msg_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_ref_1213_; lean_object* v_macroStack_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
v_ref_1213_ = lean_ctor_get(v___y_1210_, 2);
v_macroStack_1214_ = lean_ctor_get(v___y_1206_, 1);
v___x_1215_ = l_Lean_Elab_getBetterRef(v_ref_1213_, v_macroStack_1214_);
v___x_1216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_1205_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref(v___x_1216_);
lean_inc(v_macroStack_1214_);
v___x_1218_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_a_1217_, v_macroStack_1214_, v___y_1210_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1215_);
lean_ctor_set(v___x_1223_, 1, v_a_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 1);
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(lean_object* v_ref_1237_, lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_toCold_1246_; lean_object* v_currRecDepth_1247_; lean_object* v_ref_1248_; uint16_t v_optionFlags_1249_; uint8_t v_suppressElabErrors_1250_; uint8_t v_isRecordingDeps_1251_; lean_object* v_ref_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_toCold_1246_ = lean_ctor_get(v___y_1243_, 0);
v_currRecDepth_1247_ = lean_ctor_get(v___y_1243_, 1);
v_ref_1248_ = lean_ctor_get(v___y_1243_, 2);
v_optionFlags_1249_ = lean_ctor_get_uint16(v___y_1243_, sizeof(void*)*3);
v_suppressElabErrors_1250_ = lean_ctor_get_uint8(v___y_1243_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1251_ = lean_ctor_get_uint8(v___y_1243_, sizeof(void*)*3 + 3);
v_ref_1252_ = l_Lean_replaceRef(v_ref_1237_, v_ref_1248_);
lean_inc(v_currRecDepth_1247_);
lean_inc_ref(v_toCold_1246_);
v___x_1253_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1253_, 0, v_toCold_1246_);
lean_ctor_set(v___x_1253_, 1, v_currRecDepth_1247_);
lean_ctor_set(v___x_1253_, 2, v_ref_1252_);
lean_ctor_set_uint16(v___x_1253_, sizeof(void*)*3, v_optionFlags_1249_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*3 + 2, v_suppressElabErrors_1250_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*3 + 3, v_isRecordingDeps_1251_);
v___x_1254_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___x_1253_, v___y_1244_);
lean_dec_ref_known(v___x_1253_, 3);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg___boxed(lean_object* v_ref_1255_, lean_object* v_msg_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1255_, v_msg_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v_ref_1255_);
return v_res_1264_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6));
v___x_1276_ = l_Lean_stringToMessageData(v___x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(lean_object* v_as_1277_, size_t v_sz_1278_, size_t v_i_1279_, lean_object* v_b_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_a_1289_; lean_object* v___y_1294_; lean_object* v_____do__lift_1295_; uint8_t v___x_1299_; 
v___x_1299_ = lean_usize_dec_lt(v_i_1279_, v_sz_1278_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v_b_1280_);
return v___x_1300_;
}
else
{
lean_object* v_fst_1301_; lean_object* v_snd_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1508_; 
v_fst_1301_ = lean_ctor_get(v_b_1280_, 0);
v_snd_1302_ = lean_ctor_get(v_b_1280_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_b_1280_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1304_ = v_b_1280_;
v_isShared_1305_ = v_isSharedCheck_1508_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_snd_1302_);
lean_inc(v_fst_1301_);
lean_dec(v_b_1280_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1508_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v_a_1306_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v_____do__lift_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; 
v_a_1306_ = lean_array_uget_borrowed(v_as_1277_, v_i_1279_);
if (lean_obj_tag(v_snd_1302_) == 1)
{
lean_object* v_val_1485_; lean_object* v___x_1486_; 
v_val_1485_ = lean_ctor_get(v_snd_1302_, 0);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v_val_1485_);
v___x_1486_ = lean_infer_type(v_val_1485_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v_term_1488_; lean_object* v___x_1489_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v_term_1488_ = lean_ctor_get(v_a_1306_, 1);
lean_inc(v_term_1488_);
v___x_1489_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_term_1488_, v_a_1487_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v_____do__lift_1368_ = v_a_1490_;
v___y_1369_ = v___y_1281_;
v___y_1370_ = v___y_1282_;
v___y_1371_ = v___y_1283_;
v___y_1372_ = v___y_1284_;
v___y_1373_ = v___y_1285_;
v___y_1374_ = v___y_1286_;
goto v___jp_1367_;
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref_known(v_snd_1302_, 1);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1491_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1489_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1489_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref_known(v_snd_1302_, 1);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1499_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1486_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1486_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_term_1507_; 
v_term_1507_ = lean_ctor_get(v_a_1306_, 1);
lean_inc(v_term_1507_);
v_____do__lift_1368_ = v_term_1507_;
v___y_1369_ = v___y_1281_;
v___y_1370_ = v___y_1282_;
v___y_1371_ = v___y_1283_;
v___y_1372_ = v___y_1284_;
v___y_1373_ = v___y_1285_;
v___y_1374_ = v___y_1286_;
goto v___jp_1367_;
}
v___jp_1307_:
{
lean_object* v_term_1316_; lean_object* v_proof_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_term_1316_ = lean_ctor_get(v_a_1306_, 1);
v_proof_1317_ = lean_ctor_get(v_a_1306_, 2);
lean_inc_ref(v___y_1309_);
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___y_1309_);
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_box(v___x_1299_);
v___x_1321_ = lean_box(v___x_1299_);
lean_inc(v___y_1313_);
lean_inc_ref(v___y_1312_);
lean_inc(v___y_1311_);
lean_inc_ref(v___y_1310_);
lean_inc(v_proof_1317_);
v___x_1322_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 9);
lean_closure_set(v___x_1322_, 0, v_proof_1317_);
lean_closure_set(v___x_1322_, 1, v___x_1318_);
lean_closure_set(v___x_1322_, 2, v___x_1320_);
lean_closure_set(v___x_1322_, 3, v___x_1321_);
lean_closure_set(v___x_1322_, 4, v___x_1319_);
lean_closure_set(v___x_1322_, 5, v___y_1310_);
lean_closure_set(v___x_1322_, 6, v___y_1311_);
lean_closure_set(v___x_1322_, 7, v___y_1312_);
lean_closure_set(v___x_1322_, 8, v___y_1313_);
v___x_1323_ = l_Lean_Core_withFreshMacroScope___redArg(v___x_1322_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1323_) == 0)
{
if (lean_obj_tag(v_fst_1301_) == 1)
{
lean_object* v_val_1324_; lean_object* v_a_1325_; lean_object* v_fst_1326_; lean_object* v_snd_1327_; lean_object* v___x_1328_; 
lean_del_object(v___x_1304_);
v_val_1324_ = lean_ctor_get(v_fst_1301_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v_fst_1301_, 1);
v_a_1325_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1323_, 1);
v_fst_1326_ = lean_ctor_get(v_val_1324_, 0);
lean_inc(v_fst_1326_);
v_snd_1327_ = lean_ctor_get(v_val_1324_, 1);
lean_inc(v_snd_1327_);
lean_dec(v_val_1324_);
v___x_1328_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_toCold_1329_; lean_object* v_currRecDepth_1330_; lean_object* v_ref_1331_; uint16_t v_optionFlags_1332_; uint8_t v_suppressElabErrors_1333_; uint8_t v_isRecordingDeps_1334_; lean_object* v_ref_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref_known(v___x_1328_, 1);
v_toCold_1329_ = lean_ctor_get(v___y_1314_, 0);
v_currRecDepth_1330_ = lean_ctor_get(v___y_1314_, 1);
v_ref_1331_ = lean_ctor_get(v___y_1314_, 2);
v_optionFlags_1332_ = lean_ctor_get_uint16(v___y_1314_, sizeof(void*)*3);
v_suppressElabErrors_1333_ = lean_ctor_get_uint8(v___y_1314_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1334_ = lean_ctor_get_uint8(v___y_1314_, sizeof(void*)*3 + 3);
v_ref_1335_ = l_Lean_replaceRef(v_term_1316_, v_ref_1331_);
lean_inc(v_currRecDepth_1330_);
lean_inc_ref(v_toCold_1329_);
v___x_1336_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1336_, 0, v_toCold_1329_);
lean_ctor_set(v___x_1336_, 1, v_currRecDepth_1330_);
lean_ctor_set(v___x_1336_, 2, v_ref_1335_);
lean_ctor_set_uint16(v___x_1336_, sizeof(void*)*3, v_optionFlags_1332_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*3 + 2, v_suppressElabErrors_1333_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*3 + 3, v_isRecordingDeps_1334_);
v___x_1337_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_1326_, v_snd_1327_, v_a_1325_, v___y_1309_, v___y_1312_, v___y_1313_, v___x_1336_, v___y_1315_);
lean_dec_ref_known(v___x_1336_, 3);
lean_dec(v_snd_1327_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v___y_1294_ = v___y_1308_;
v_____do__lift_1295_ = v_a_1338_;
goto v___jp_1293_;
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec_ref(v___y_1308_);
v_a_1339_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1337_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1337_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v_snd_1327_);
lean_dec(v_fst_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v___y_1308_);
v_a_1347_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1328_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1328_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; 
lean_dec(v_fst_1301_);
v_a_1355_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1323_, 1);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v___y_1309_);
lean_ctor_set(v___x_1304_, 0, v_a_1355_);
v___x_1357_ = v___x_1304_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1355_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___y_1309_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
v___y_1294_ = v___y_1308_;
v_____do__lift_1295_ = v___x_1357_;
goto v___jp_1293_;
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec_ref(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1359_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1323_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1323_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
v___jp_1367_:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_Elab_Term_elabType(v_____do__lift_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
if (lean_obj_tag(v_a_1378_) == 1)
{
lean_object* v_val_1379_; lean_object* v_snd_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1453_; 
v_val_1379_ = lean_ctor_get(v_a_1378_, 0);
lean_inc(v_val_1379_);
lean_dec_ref_known(v_a_1378_, 1);
v_snd_1380_ = lean_ctor_get(v_val_1379_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_val_1379_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_val_1379_, 0);
lean_dec(v_unused_1454_);
v___x_1382_ = v_val_1379_;
v_isShared_1383_ = v_isSharedCheck_1453_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_snd_1380_);
lean_dec(v_val_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1453_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
if (lean_obj_tag(v_snd_1302_) == 1)
{
lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1451_; 
v_fst_1384_ = lean_ctor_get(v_snd_1380_, 0);
v_snd_1385_ = lean_ctor_get(v_snd_1380_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_snd_1380_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1387_ = v_snd_1380_;
v_isShared_1388_ = v_isSharedCheck_1451_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_snd_1385_);
lean_inc(v_fst_1384_);
lean_dec(v_snd_1380_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1451_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v_val_1389_; lean_object* v___x_1390_; 
v_val_1389_ = lean_ctor_get(v_snd_1302_, 0);
lean_inc_n(v_val_1389_, 2);
lean_dec_ref_known(v_snd_1302_, 1);
lean_inc(v_fst_1384_);
v___x_1390_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1384_, v_val_1389_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; uint8_t v___x_1392_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = lean_unbox(v_a_1391_);
lean_dec(v_a_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1373_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v_fst_1384_);
v___x_1393_ = lean_infer_type(v_fst_1384_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1373_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v_val_1389_);
v___x_1395_ = lean_infer_type(v_val_1389_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v_term_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v_term_1397_ = lean_ctor_get(v_a_1306_, 1);
v___x_1398_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_1399_ = l_Lean_MessageData_ofExpr(v_fst_1384_);
v___x_1400_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 7);
lean_ctor_set(v___x_1387_, 1, v___x_1400_);
lean_ctor_set(v___x_1387_, 0, v___x_1399_);
v___x_1402_ = v___x_1387_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = l_Lean_MessageData_ofExpr(v_a_1394_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 7);
lean_ctor_set(v___x_1382_, 1, v___x_1403_);
lean_ctor_set(v___x_1382_, 0, v___x_1402_);
v___x_1405_ = v___x_1382_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1406_ = l_Lean_indentD(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1398_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5);
v___x_1409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l_Lean_MessageData_ofExpr(v_val_1389_);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___x_1400_);
v___x_1412_ = l_Lean_MessageData_ofExpr(v_a_1396_);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_indentD(v___x_1413_);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1409_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1397_, v___x_1415_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_dec_ref_known(v___x_1416_, 1);
v___y_1308_ = v_snd_1385_;
v___y_1309_ = v_a_1376_;
v___y_1310_ = v___y_1369_;
v___y_1311_ = v___y_1370_;
v___y_1312_ = v___y_1371_;
v___y_1313_ = v___y_1372_;
v___y_1314_ = v___y_1373_;
v___y_1315_ = v___y_1374_;
goto v___jp_1307_;
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_snd_1385_);
lean_dec(v_a_1376_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v_a_1394_);
lean_dec(v_val_1389_);
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1376_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1427_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1395_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1395_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_val_1389_);
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1376_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1435_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1393_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1393_);
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
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_dec(v_val_1389_);
lean_del_object(v___x_1387_);
lean_dec(v_fst_1384_);
lean_del_object(v___x_1382_);
v___y_1308_ = v_snd_1385_;
v___y_1309_ = v_a_1376_;
v___y_1310_ = v___y_1369_;
v___y_1311_ = v___y_1370_;
v___y_1312_ = v___y_1371_;
v___y_1313_ = v___y_1372_;
v___y_1314_ = v___y_1373_;
v___y_1315_ = v___y_1374_;
goto v___jp_1307_;
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_val_1389_);
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_del_object(v___x_1382_);
lean_dec(v_a_1376_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1443_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1390_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1390_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
else
{
lean_object* v_snd_1452_; 
lean_del_object(v___x_1382_);
lean_dec(v_snd_1302_);
v_snd_1452_ = lean_ctor_get(v_snd_1380_, 1);
lean_inc(v_snd_1452_);
lean_dec(v_snd_1380_);
v___y_1308_ = v_snd_1452_;
v___y_1309_ = v_a_1376_;
v___y_1310_ = v___y_1369_;
v___y_1311_ = v___y_1370_;
v___y_1312_ = v___y_1371_;
v___y_1313_ = v___y_1372_;
v___y_1314_ = v___y_1373_;
v___y_1315_ = v___y_1374_;
goto v___jp_1307_;
}
}
}
else
{
lean_object* v_term_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec(v_a_1378_);
lean_del_object(v___x_1304_);
v_term_1455_ = lean_ctor_get(v_a_1306_, 1);
v___x_1456_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7);
v___x_1457_ = l_Lean_indentExpr(v_a_1376_);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1455_, v___x_1458_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref_known(v___x_1459_, 1);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_fst_1301_);
lean_ctor_set(v___x_1460_, 1, v_snd_1302_);
v_a_1289_ = v___x_1460_;
goto v___jp_1288_;
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_snd_1302_);
lean_dec(v_fst_1301_);
v_a_1461_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1459_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1459_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_a_1376_);
lean_del_object(v___x_1304_);
lean_dec(v_snd_1302_);
lean_dec(v_fst_1301_);
v_a_1469_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1377_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1377_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_del_object(v___x_1304_);
lean_dec(v_snd_1302_);
lean_dec(v_fst_1301_);
v_a_1477_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1375_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1375_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
v___jp_1288_:
{
size_t v___x_1290_; size_t v___x_1291_; 
v___x_1290_ = ((size_t)1ULL);
v___x_1291_ = lean_usize_add(v_i_1279_, v___x_1290_);
v_i_1279_ = v___x_1291_;
v_b_1280_ = v_a_1289_;
goto _start;
}
v___jp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_____do__lift_1295_);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___y_1294_);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v_a_1289_ = v___x_1298_;
goto v___jp_1288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___boxed(lean_object* v_as_1509_, lean_object* v_sz_1510_, lean_object* v_i_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
size_t v_sz_boxed_1520_; size_t v_i_boxed_1521_; lean_object* v_res_1522_; 
v_sz_boxed_1520_ = lean_unbox_usize(v_sz_1510_);
lean_dec(v_sz_1510_);
v_i_boxed_1521_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_as_1509_, v_sz_boxed_1520_, v_i_boxed_1521_, v_b_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v_as_1509_);
return v_res_1522_;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__4(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1528_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__3));
v___x_1529_ = lean_unsigned_to_nat(14u);
v___x_1530_ = lean_unsigned_to_nat(22u);
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__2));
v___x_1532_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__1));
v___x_1533_ = l_mkPanicMessageWithDecl(v___x_1532_, v___x_1531_, v___x_1530_, v___x_1529_, v___x_1528_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object* v_steps_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1542_; size_t v_sz_1543_; size_t v___x_1544_; lean_object* v___x_1545_; 
v___x_1542_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__0));
v_sz_1543_ = lean_array_size(v_steps_1534_);
v___x_1544_ = ((size_t)0ULL);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_steps_1534_, v_sz_1543_, v___x_1544_, v___x_1542_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v_fst_1547_; lean_object* v___x_1548_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v_fst_1547_ = lean_ctor_get(v_a_1546_, 0);
lean_inc(v_fst_1547_);
lean_dec(v_a_1546_);
v___x_1548_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1561_; 
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v___x_1548_, 0);
lean_dec(v_unused_1562_);
v___x_1550_ = v___x_1548_;
v_isShared_1551_ = v_isSharedCheck_1561_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v___x_1548_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1561_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
if (lean_obj_tag(v_fst_1547_) == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1552_ = lean_obj_once(&l_Lean_Elab_Term_elabCalcSteps___closed__4, &l_Lean_Elab_Term_elabCalcSteps___closed__4_once, _init_l_Lean_Elab_Term_elabCalcSteps___closed__4);
v___x_1553_ = l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(v___x_1552_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1553_);
v___x_1555_ = v___x_1550_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
else
{
lean_object* v_val_1557_; lean_object* v___x_1559_; 
v_val_1557_ = lean_ctor_get(v_fst_1547_, 0);
lean_inc(v_val_1557_);
lean_dec_ref_known(v_fst_1547_, 1);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v_val_1557_);
v___x_1559_ = v___x_1550_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_val_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_fst_1547_);
v_a_1563_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1548_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1548_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
v_a_1571_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1545_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1545_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps___boxed(lean_object* v_steps_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Elab_Term_elabCalcSteps(v_steps_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec_ref(v_steps_1579_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(lean_object* v_00_u03b1_1588_, lean_object* v_ref_1589_, lean_object* v_msg_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1589_, v_msg_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___boxed(lean_object* v_00_u03b1_1599_, lean_object* v_ref_1600_, lean_object* v_msg_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(v_00_u03b1_1599_, v_ref_1600_, v_msg_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v_ref_1600_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(lean_object* v_00_u03b1_1610_, lean_object* v_msg_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1620_, lean_object* v_msg_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(v_00_u03b1_1620_, v_msg_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(lean_object* v_msgData_1630_, lean_object* v_macroStack_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1630_, v_macroStack_1631_, v___y_1636_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1640_, lean_object* v_macroStack_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(v_msgData_1640_, v_macroStack_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v_res_1649_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = l_Lean_Elab_abortTermExceptionId;
v___x_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v___x_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg(){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___boxed(lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(lean_object* v_00_u03b1_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___boxed(lean_object* v_00_u03b1_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(v_00_u03b1_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(lean_object* v_msg_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___f_1678_; lean_object* v___x_4885__overap_1679_; lean_object* v___x_1680_; 
v___f_1678_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_4885__overap_1679_ = lean_panic_fn_borrowed(v___f_1678_, v_msg_1672_);
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
lean_inc(v___y_1674_);
lean_inc_ref(v___y_1673_);
v___x_1680_ = lean_apply_5(v___x_4885__overap_1679_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, lean_box(0));
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg___boxed(lean_object* v_msg_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(lean_object* v_00_u03b1_1688_, lean_object* v_msg_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_msg_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(v_00_u03b1_1696_, v_msg_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(uint8_t v_suppressElabErrors_1711_, uint8_t v___y_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1713_) == 1)
{
lean_object* v_pre_1714_; 
v_pre_1714_ = lean_ctor_get(v_x_1713_, 0);
switch(lean_obj_tag(v_pre_1714_))
{
case 1:
{
lean_object* v_pre_1715_; 
v_pre_1715_ = lean_ctor_get(v_pre_1714_, 0);
switch(lean_obj_tag(v_pre_1715_))
{
case 0:
{
lean_object* v_str_1716_; lean_object* v_str_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_str_1716_ = lean_ctor_get(v_x_1713_, 1);
v_str_1717_ = lean_ctor_get(v_pre_1714_, 1);
v___x_1718_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13));
v___x_1719_ = lean_string_dec_eq(v_str_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0));
v___x_1721_ = lean_string_dec_eq(v_str_1717_, v___x_1720_);
if (v___x_1721_ == 0)
{
return v___x_1721_;
}
else
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1));
v___x_1723_ = lean_string_dec_eq(v_str_1716_, v___x_1722_);
if (v___x_1723_ == 0)
{
return v___x_1723_;
}
else
{
return v_suppressElabErrors_1711_;
}
}
}
else
{
lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2));
v___x_1725_ = lean_string_dec_eq(v_str_1716_, v___x_1724_);
if (v___x_1725_ == 0)
{
return v___x_1725_;
}
else
{
return v_suppressElabErrors_1711_;
}
}
}
case 1:
{
lean_object* v_pre_1726_; 
v_pre_1726_ = lean_ctor_get(v_pre_1715_, 0);
if (lean_obj_tag(v_pre_1726_) == 0)
{
lean_object* v_str_1727_; lean_object* v_str_1728_; lean_object* v_str_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_str_1727_ = lean_ctor_get(v_x_1713_, 1);
v_str_1728_ = lean_ctor_get(v_pre_1714_, 1);
v_str_1729_ = lean_ctor_get(v_pre_1715_, 1);
v___x_1730_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3));
v___x_1731_ = lean_string_dec_eq(v_str_1729_, v___x_1730_);
if (v___x_1731_ == 0)
{
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4));
v___x_1733_ = lean_string_dec_eq(v_str_1728_, v___x_1732_);
if (v___x_1733_ == 0)
{
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5));
v___x_1735_ = lean_string_dec_eq(v_str_1727_, v___x_1734_);
if (v___x_1735_ == 0)
{
return v___x_1735_;
}
else
{
return v_suppressElabErrors_1711_;
}
}
}
}
else
{
return v___y_1712_;
}
}
default: 
{
return v___y_1712_;
}
}
}
case 0:
{
lean_object* v_str_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v_str_1736_ = lean_ctor_get(v_x_1713_, 1);
v___x_1737_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6));
v___x_1738_ = lean_string_dec_eq(v_str_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
return v___x_1738_;
}
else
{
return v_suppressElabErrors_1711_;
}
}
default: 
{
return v___y_1712_;
}
}
}
else
{
return v___y_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1739_, lean_object* v___y_1740_, lean_object* v_x_1741_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1742_; uint8_t v___y_7603__boxed_1743_; uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_suppressElabErrors_boxed_1742_ = lean_unbox(v_suppressElabErrors_1739_);
v___y_7603__boxed_1743_ = lean_unbox(v___y_1740_);
v_res_1744_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_1742_, v___y_7603__boxed_1743_, v_x_1741_);
lean_dec(v_x_1741_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(lean_object* v_ref_1746_, lean_object* v_msgData_1747_, uint8_t v_severity_1748_, uint8_t v_isSilent_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
uint8_t v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; uint8_t v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v_toCold_1763_; lean_object* v___y_1764_; lean_object* v___y_1793_; lean_object* v___y_1794_; uint8_t v___y_1795_; lean_object* v___y_1796_; uint8_t v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; uint8_t v___y_1823_; lean_object* v___y_1824_; uint8_t v___y_1825_; lean_object* v___y_1826_; uint8_t v___y_1830_; uint8_t v___y_1831_; uint8_t v___y_1832_; uint8_t v___x_1843_; uint8_t v___y_1845_; uint8_t v___y_1846_; uint8_t v___y_1847_; uint8_t v___y_1849_; uint8_t v___x_1857_; 
v___x_1843_ = 2;
v___x_1857_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1748_, v___x_1843_);
if (v___x_1857_ == 0)
{
v___y_1849_ = v___x_1857_;
goto v___jp_1848_;
}
else
{
uint8_t v___x_1858_; 
lean_inc_ref(v_msgData_1747_);
v___x_1858_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1747_);
v___y_1849_ = v___x_1858_;
goto v___jp_1848_;
}
v___jp_1755_:
{
lean_object* v_currNamespace_1765_; lean_object* v_openDecls_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v_env_1771_; lean_object* v_nextMacroScope_1772_; lean_object* v_ngen_1773_; lean_object* v_auxDeclNGen_1774_; lean_object* v_traceState_1775_; lean_object* v_cache_1776_; lean_object* v_recordedDeps_1777_; lean_object* v_messages_1778_; lean_object* v_infoState_1779_; lean_object* v_snapshotTasks_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1791_; 
v_currNamespace_1765_ = lean_ctor_get(v_toCold_1763_, 4);
v_openDecls_1766_ = lean_ctor_get(v_toCold_1763_, 5);
lean_inc(v_openDecls_1766_);
lean_inc(v_currNamespace_1765_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_currNamespace_1765_);
lean_ctor_set(v___x_1767_, 1, v_openDecls_1766_);
v___x_1768_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___y_1759_);
lean_inc_ref(v___y_1757_);
lean_inc_ref(v___y_1762_);
v___x_1769_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1769_, 0, v___y_1762_);
lean_ctor_set(v___x_1769_, 1, v___y_1761_);
lean_ctor_set(v___x_1769_, 2, v___y_1758_);
lean_ctor_set(v___x_1769_, 3, v___y_1757_);
lean_ctor_set(v___x_1769_, 4, v___x_1768_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*5, v___y_1760_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*5 + 1, v___y_1756_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*5 + 2, v_isSilent_1749_);
v___x_1770_ = lean_st_ref_take(v___y_1764_);
v_env_1771_ = lean_ctor_get(v___x_1770_, 0);
v_nextMacroScope_1772_ = lean_ctor_get(v___x_1770_, 1);
v_ngen_1773_ = lean_ctor_get(v___x_1770_, 2);
v_auxDeclNGen_1774_ = lean_ctor_get(v___x_1770_, 3);
v_traceState_1775_ = lean_ctor_get(v___x_1770_, 4);
v_cache_1776_ = lean_ctor_get(v___x_1770_, 5);
v_recordedDeps_1777_ = lean_ctor_get(v___x_1770_, 6);
v_messages_1778_ = lean_ctor_get(v___x_1770_, 7);
v_infoState_1779_ = lean_ctor_get(v___x_1770_, 8);
v_snapshotTasks_1780_ = lean_ctor_get(v___x_1770_, 9);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1782_ = v___x_1770_;
v_isShared_1783_ = v_isSharedCheck_1791_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_snapshotTasks_1780_);
lean_inc(v_infoState_1779_);
lean_inc(v_messages_1778_);
lean_inc(v_recordedDeps_1777_);
lean_inc(v_cache_1776_);
lean_inc(v_traceState_1775_);
lean_inc(v_auxDeclNGen_1774_);
lean_inc(v_ngen_1773_);
lean_inc(v_nextMacroScope_1772_);
lean_inc(v_env_1771_);
lean_dec(v___x_1770_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1791_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = lean_box(0);
v___x_1785_ = l_Lean_MessageLog_add(v___x_1769_, v_messages_1778_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 7, v___x_1785_);
v___x_1787_ = v___x_1782_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_env_1771_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_nextMacroScope_1772_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_ngen_1773_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_auxDeclNGen_1774_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v_traceState_1775_);
lean_ctor_set(v_reuseFailAlloc_1790_, 5, v_cache_1776_);
lean_ctor_set(v_reuseFailAlloc_1790_, 6, v_recordedDeps_1777_);
lean_ctor_set(v_reuseFailAlloc_1790_, 7, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1790_, 8, v_infoState_1779_);
lean_ctor_set(v_reuseFailAlloc_1790_, 9, v_snapshotTasks_1780_);
v___x_1787_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_st_ref_put(v___y_1764_, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1784_);
return v___x_1789_;
}
}
}
v___jp_1792_:
{
lean_object* v_fileName_1801_; lean_object* v_fileMap_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1818_; 
v_fileName_1801_ = lean_ctor_get(v___y_1796_, 0);
v_fileMap_1802_ = lean_ctor_get(v___y_1796_, 1);
v___x_1803_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1747_);
v___x_1804_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v___x_1803_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_inc_ref_n(v_fileMap_1802_, 2);
v___x_1809_ = l_Lean_FileMap_toPosition(v_fileMap_1802_, v___y_1799_);
lean_dec(v___y_1799_);
v___x_1810_ = l_Lean_FileMap_toPosition(v_fileMap_1802_, v___y_1800_);
lean_dec(v___y_1800_);
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
v___x_1812_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
if (v___y_1797_ == 0)
{
lean_del_object(v___x_1807_);
lean_dec_ref(v___y_1793_);
v___y_1756_ = v___y_1795_;
v___y_1757_ = v___x_1812_;
v___y_1758_ = v___x_1811_;
v___y_1759_ = v_a_1805_;
v___y_1760_ = v___y_1798_;
v___y_1761_ = v___x_1809_;
v___y_1762_ = v_fileName_1801_;
v_toCold_1763_ = v___y_1794_;
v___y_1764_ = v___y_1753_;
goto v___jp_1755_;
}
else
{
uint8_t v___x_1813_; 
lean_inc(v_a_1805_);
v___x_1813_ = l_Lean_MessageData_hasTag(v___y_1793_, v_a_1805_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
lean_dec_ref_known(v___x_1811_, 1);
lean_dec_ref(v___x_1809_);
lean_dec(v_a_1805_);
v___x_1814_ = lean_box(0);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1814_);
v___x_1816_ = v___x_1807_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
else
{
lean_del_object(v___x_1807_);
v___y_1756_ = v___y_1795_;
v___y_1757_ = v___x_1812_;
v___y_1758_ = v___x_1811_;
v___y_1759_ = v_a_1805_;
v___y_1760_ = v___y_1798_;
v___y_1761_ = v___x_1809_;
v___y_1762_ = v_fileName_1801_;
v_toCold_1763_ = v___y_1794_;
v___y_1764_ = v___y_1753_;
goto v___jp_1755_;
}
}
}
}
v___jp_1819_:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Syntax_getTailPos_x3f(v___y_1824_, v___y_1825_);
lean_dec(v___y_1824_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_inc(v___y_1826_);
v___y_1793_ = v___y_1820_;
v___y_1794_ = v___y_1821_;
v___y_1795_ = v___y_1823_;
v___y_1796_ = v___y_1821_;
v___y_1797_ = v___y_1822_;
v___y_1798_ = v___y_1825_;
v___y_1799_ = v___y_1826_;
v___y_1800_ = v___y_1826_;
goto v___jp_1792_;
}
else
{
lean_object* v_val_1828_; 
v_val_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_val_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___y_1793_ = v___y_1820_;
v___y_1794_ = v___y_1821_;
v___y_1795_ = v___y_1823_;
v___y_1796_ = v___y_1821_;
v___y_1797_ = v___y_1822_;
v___y_1798_ = v___y_1825_;
v___y_1799_ = v___y_1826_;
v___y_1800_ = v_val_1828_;
goto v___jp_1792_;
}
}
v___jp_1829_:
{
lean_object* v_toCold_1833_; lean_object* v_ref_1834_; uint8_t v_suppressElabErrors_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___f_1838_; lean_object* v_ref_1839_; lean_object* v___x_1840_; 
v_toCold_1833_ = lean_ctor_get(v___y_1752_, 0);
v_ref_1834_ = lean_ctor_get(v___y_1752_, 2);
v_suppressElabErrors_1835_ = lean_ctor_get_uint8(v___y_1752_, sizeof(void*)*3 + 2);
v___x_1836_ = lean_box(v_suppressElabErrors_1835_);
v___x_1837_ = lean_box(v___y_1830_);
v___f_1838_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1838_, 0, v___x_1836_);
lean_closure_set(v___f_1838_, 1, v___x_1837_);
v_ref_1839_ = l_Lean_replaceRef(v_ref_1746_, v_ref_1834_);
v___x_1840_ = l_Lean_Syntax_getPos_x3f(v_ref_1839_, v___y_1831_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_unsigned_to_nat(0u);
v___y_1820_ = v___f_1838_;
v___y_1821_ = v_toCold_1833_;
v___y_1822_ = v_suppressElabErrors_1835_;
v___y_1823_ = v___y_1832_;
v___y_1824_ = v_ref_1839_;
v___y_1825_ = v___y_1831_;
v___y_1826_ = v___x_1841_;
goto v___jp_1819_;
}
else
{
lean_object* v_val_1842_; 
v_val_1842_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_val_1842_);
lean_dec_ref_known(v___x_1840_, 1);
v___y_1820_ = v___f_1838_;
v___y_1821_ = v_toCold_1833_;
v___y_1822_ = v_suppressElabErrors_1835_;
v___y_1823_ = v___y_1832_;
v___y_1824_ = v_ref_1839_;
v___y_1825_ = v___y_1831_;
v___y_1826_ = v_val_1842_;
goto v___jp_1819_;
}
}
v___jp_1844_:
{
if (v___y_1847_ == 0)
{
v___y_1830_ = v___y_1845_;
v___y_1831_ = v___y_1846_;
v___y_1832_ = v_severity_1748_;
goto v___jp_1829_;
}
else
{
v___y_1830_ = v___y_1845_;
v___y_1831_ = v___y_1846_;
v___y_1832_ = v___x_1843_;
goto v___jp_1829_;
}
}
v___jp_1848_:
{
if (v___y_1849_ == 0)
{
uint8_t v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = 1;
v___x_1851_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1748_, v___x_1850_);
if (v___x_1851_ == 0)
{
v___y_1845_ = v___y_1849_;
v___y_1846_ = v___y_1849_;
v___y_1847_ = v___x_1851_;
goto v___jp_1844_;
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1752_);
v___x_1853_ = l_Lean_warningAsError;
v___x_1854_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v___x_1852_, v___x_1853_);
lean_dec_ref(v___x_1852_);
v___y_1845_ = v___y_1849_;
v___y_1846_ = v___y_1849_;
v___y_1847_ = v___x_1854_;
goto v___jp_1844_;
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec_ref(v_msgData_1747_);
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___boxed(lean_object* v_ref_1859_, lean_object* v_msgData_1860_, lean_object* v_severity_1861_, lean_object* v_isSilent_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v_severity_boxed_1868_; uint8_t v_isSilent_boxed_1869_; lean_object* v_res_1870_; 
v_severity_boxed_1868_ = lean_unbox(v_severity_1861_);
v_isSilent_boxed_1869_ = lean_unbox(v_isSilent_1862_);
v_res_1870_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1859_, v_msgData_1860_, v_severity_boxed_1868_, v_isSilent_boxed_1869_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v_ref_1859_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(lean_object* v_ref_1871_, lean_object* v_msgData_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
uint8_t v___x_1878_; uint8_t v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = 2;
v___x_1879_ = 0;
v___x_1880_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1871_, v_msgData_1872_, v___x_1878_, v___x_1879_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1___boxed(lean_object* v_ref_1881_, lean_object* v_msgData_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_ref_1881_, v_msgData_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v_ref_1881_);
return v_res_1888_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1));
v___x_1893_ = l_Lean_MessageData_ofFormat(v___x_1892_);
return v___x_1893_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2);
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4));
v___x_1898_ = l_Lean_stringToMessageData(v___x_1897_);
return v___x_1898_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6));
v___x_1901_ = l_Lean_stringToMessageData(v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1903_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_1904_ = lean_unsigned_to_nat(57u);
v___x_1905_ = lean_unsigned_to_nat(133u);
v___x_1906_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8));
v___x_1907_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_1908_ = l_mkPanicMessageWithDecl(v___x_1907_, v___x_1906_, v___x_1905_, v___x_1904_, v___x_1903_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object* v_steps_1909_, lean_object* v_expectedType_1910_, lean_object* v_result_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = ((lean_object*)(l_Lean_Elab_Term_instInhabitedCalcStepView_default));
lean_inc(v_a_1915_);
lean_inc_ref(v_a_1914_);
lean_inc(v_a_1913_);
lean_inc_ref(v_a_1912_);
lean_inc_ref(v_result_1911_);
v___x_1918_ = lean_infer_type(v_result_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___x_1945_; lean_object* v_a_1946_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v___x_1920_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_1919_, v_a_1913_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
v___x_1922_ = l_Lean_Expr_headBeta(v_a_1921_);
v___x_1945_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_1922_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
if (lean_obj_tag(v_a_1946_) == 1)
{
lean_object* v_val_1947_; lean_object* v_snd_1948_; lean_object* v_fst_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_2193_; 
v_val_1947_ = lean_ctor_get(v_a_1946_, 0);
lean_inc(v_val_1947_);
lean_dec_ref_known(v_a_1946_, 1);
v_snd_1948_ = lean_ctor_get(v_val_1947_, 1);
v_fst_1949_ = lean_ctor_get(v_val_1947_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_val_1947_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_1951_ = v_val_1947_;
v_isShared_1952_ = v_isSharedCheck_2193_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snd_1948_);
lean_inc(v_fst_1949_);
lean_dec(v_val_1947_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_2193_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_fst_1953_; lean_object* v_snd_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2192_; 
v_fst_1953_ = lean_ctor_get(v_snd_1948_, 0);
v_snd_1954_ = lean_ctor_get(v_snd_1948_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_snd_1948_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_1956_ = v_snd_1948_;
v_isShared_1957_ = v_isSharedCheck_2192_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_snd_1954_);
lean_inc(v_fst_1953_);
lean_dec(v_snd_1948_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2192_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v_a_1959_; 
v___x_1958_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_expectedType_1910_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref(v___x_1958_);
if (lean_obj_tag(v_a_1959_) == 1)
{
lean_object* v_val_1960_; lean_object* v_snd_1961_; lean_object* v_fst_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2191_; 
v_val_1960_ = lean_ctor_get(v_a_1959_, 0);
lean_inc(v_val_1960_);
lean_dec_ref_known(v_a_1959_, 1);
v_snd_1961_ = lean_ctor_get(v_val_1960_, 1);
v_fst_1962_ = lean_ctor_get(v_val_1960_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_val_1960_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_1964_ = v_val_1960_;
v_isShared_1965_ = v_isSharedCheck_2191_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_snd_1961_);
lean_inc(v_fst_1962_);
lean_dec(v_val_1960_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2191_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_fst_1966_; lean_object* v_snd_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2190_; 
v_fst_1966_ = lean_ctor_get(v_snd_1961_, 0);
v_snd_1967_ = lean_ctor_get(v_snd_1961_, 1);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_snd_1961_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_1969_ = v_snd_1961_;
v_isShared_1970_ = v_isSharedCheck_2190_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_snd_1967_);
lean_inc(v_fst_1966_);
lean_dec(v_snd_1961_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2190_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
uint8_t v_failed_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1949_, v_fst_1962_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; uint8_t v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = lean_unbox(v_a_2083_);
if (v___x_2084_ == 0)
{
lean_dec(v_a_2083_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_dec(v_fst_1966_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_dec(v_fst_1953_);
lean_del_object(v___x_1951_);
v___y_1924_ = v_a_1912_;
v___y_1925_ = v_a_1913_;
v___y_1926_ = v_a_1914_;
v___y_1927_ = v_a_1915_;
goto v___jp_1923_;
}
else
{
uint8_t v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = 0;
lean_inc(v_fst_1966_);
lean_inc(v_fst_1953_);
v___x_2086_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1953_, v_fst_1966_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; uint8_t v___x_2088_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = lean_unbox(v_a_2087_);
lean_dec(v_a_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_1953_, v_fst_1966_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v_fst_2091_; lean_object* v_snd_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2165_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v_fst_2091_ = lean_ctor_get(v_a_2090_, 0);
v_snd_2092_ = lean_ctor_get(v_a_2090_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_a_2090_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2094_ = v_a_2090_;
v_isShared_2095_ = v_isSharedCheck_2165_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_snd_2092_);
lean_inc(v_fst_2091_);
lean_dec(v_a_2090_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2165_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; 
lean_inc(v_a_1915_);
lean_inc_ref(v_a_1914_);
lean_inc(v_a_1913_);
lean_inc_ref(v_a_1912_);
lean_inc(v_fst_2091_);
v___x_2096_ = lean_infer_type(v_fst_2091_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
lean_inc(v_a_1915_);
lean_inc_ref(v_a_1914_);
lean_inc(v_a_1913_);
lean_inc_ref(v_a_1912_);
lean_inc(v_snd_2092_);
v___x_2098_ = lean_infer_type(v_snd_2092_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v___x_2100_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2097_, v_a_2099_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v_fst_2102_; lean_object* v_snd_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2140_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v_fst_2102_ = lean_ctor_get(v_a_2101_, 0);
v_snd_2103_ = lean_ctor_get(v_a_2101_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2101_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2105_ = v_a_2101_;
v_isShared_2106_ = v_isSharedCheck_2140_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_snd_2103_);
lean_inc(v_fst_2102_);
lean_dec(v_a_2101_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2140_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v_term_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2107_ = lean_unsigned_to_nat(0u);
v___x_2108_ = lean_array_get_borrowed(v___x_1917_, v_steps_1909_, v___x_2107_);
v_term_2109_ = lean_ctor_get(v___x_2108_, 1);
v___x_2110_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_2111_ = l_Lean_MessageData_ofExpr(v_fst_2091_);
v___x_2112_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 7);
lean_ctor_set(v___x_2105_, 1, v___x_2112_);
lean_ctor_set(v___x_2105_, 0, v___x_2111_);
v___x_2114_ = v___x_2105_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = l_Lean_MessageData_ofExpr(v_fst_2102_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 7);
lean_ctor_set(v___x_2094_, 1, v___x_2115_);
lean_ctor_set(v___x_2094_, 0, v___x_2114_);
v___x_2117_ = v___x_2094_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2118_ = l_Lean_indentD(v___x_2117_);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2110_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
v___x_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = l_Lean_MessageData_ofExpr(v_snd_2092_);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2112_);
v___x_2124_ = l_Lean_MessageData_ofExpr(v_snd_2103_);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_Lean_indentD(v___x_2125_);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2121_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2109_, v___x_2127_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_2128_) == 0)
{
uint8_t v___x_2129_; 
lean_dec_ref_known(v___x_2128_, 1);
v___x_2129_ = lean_unbox(v_a_2083_);
lean_dec(v_a_2083_);
v_failed_1972_ = v___x_2129_;
v___y_1973_ = v_a_1912_;
v___y_1974_ = v_a_1913_;
v___y_1975_ = v_a_1914_;
v___y_1976_ = v_a_1915_;
goto v___jp_1971_;
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_a_2083_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_del_object(v___x_1951_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v_a_2130_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2128_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_del_object(v___x_2094_);
lean_dec(v_snd_2092_);
lean_dec(v_fst_2091_);
lean_dec(v_a_2083_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_del_object(v___x_1951_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v_a_2141_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2100_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2100_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_a_2097_);
lean_del_object(v___x_2094_);
lean_dec(v_snd_2092_);
lean_dec(v_fst_2091_);
lean_dec(v_a_2083_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_del_object(v___x_1951_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v_a_2149_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2098_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2098_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_del_object(v___x_2094_);
lean_dec(v_snd_2092_);
lean_dec(v_fst_2091_);
lean_dec(v_a_2083_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_del_object(v___x_1951_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v_a_2157_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2096_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2096_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_a_2083_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_del_object(v___x_1951_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v_a_2166_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2089_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2089_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_dec(v_a_2083_);
lean_dec(v_fst_1966_);
lean_dec(v_fst_1953_);
v_failed_1972_ = v___x_2085_;
v___y_1973_ = v_a_1912_;
v___y_1974_ = v_a_1913_;
v___y_1975_ = v_a_1914_;
v___y_1976_ = v_a_1915_;
goto v___jp_1971_;
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2083_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_dec(v_fst_1966_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_dec(v_fst_1953_);
lean_del_object(v___x_1951_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v_a_2174_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2086_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2086_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_dec(v_fst_1966_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_dec(v_fst_1953_);
lean_del_object(v___x_1951_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v_a_2182_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2082_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2082_);
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
v___jp_1971_:
{
lean_object* v___x_1977_; 
lean_inc(v_snd_1967_);
lean_inc(v_snd_1954_);
v___x_1977_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_1954_, v_snd_1967_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; uint8_t v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = lean_unbox(v_a_1978_);
lean_dec(v_a_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v___x_1980_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_snd_1954_, v_snd_1967_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v_fst_1982_; lean_object* v_snd_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2065_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v_fst_1982_ = lean_ctor_get(v_a_1981_, 0);
v_snd_1983_ = lean_ctor_get(v_a_1981_, 1);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_a_1981_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_1985_ = v_a_1981_;
v_isShared_1986_ = v_isSharedCheck_2065_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snd_1983_);
lean_inc(v_fst_1982_);
lean_dec(v_a_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2065_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; 
lean_inc(v___y_1976_);
lean_inc_ref(v___y_1975_);
lean_inc(v___y_1974_);
lean_inc_ref(v___y_1973_);
lean_inc(v_fst_1982_);
v___x_1987_ = lean_infer_type(v_fst_1982_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1989_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
lean_inc(v___y_1976_);
lean_inc_ref(v___y_1975_);
lean_inc(v___y_1974_);
lean_inc_ref(v___y_1973_);
lean_inc(v_snd_1983_);
v___x_1989_ = lean_infer_type(v_snd_1983_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1991_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
v___x_1991_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_1988_, v_a_1990_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v_fst_1993_; lean_object* v_snd_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2040_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v_fst_1993_ = lean_ctor_get(v_a_1992_, 0);
v_snd_1994_ = lean_ctor_get(v_a_1992_, 1);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_a_1992_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_1996_ = v_a_1992_;
v_isShared_1997_ = v_isSharedCheck_2040_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_snd_1994_);
lean_inc(v_fst_1993_);
lean_dec(v_a_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2040_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v_term_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_1998_ = lean_array_get_size(v_steps_1909_);
v___x_1999_ = lean_unsigned_to_nat(1u);
v___x_2000_ = lean_nat_sub(v___x_1998_, v___x_1999_);
v___x_2001_ = lean_array_get_borrowed(v___x_1917_, v_steps_1909_, v___x_2000_);
lean_dec(v___x_2000_);
v_term_2002_ = lean_ctor_get(v___x_2001_, 1);
v___x_2003_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5);
v___x_2004_ = l_Lean_MessageData_ofExpr(v_fst_1982_);
v___x_2005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 7);
lean_ctor_set(v___x_1996_, 1, v___x_2005_);
lean_ctor_set(v___x_1996_, 0, v___x_2004_);
v___x_2007_ = v___x_1996_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = l_Lean_MessageData_ofExpr(v_fst_1993_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 7);
lean_ctor_set(v___x_1985_, 1, v___x_2008_);
lean_ctor_set(v___x_1985_, 0, v___x_2007_);
v___x_2010_ = v___x_1985_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = l_Lean_indentD(v___x_2010_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set_tag(v___x_1969_, 7);
lean_ctor_set(v___x_1969_, 1, v___x_2011_);
lean_ctor_set(v___x_1969_, 0, v___x_2003_);
v___x_2013_ = v___x_1969_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
if (v_isShared_1965_ == 0)
{
lean_ctor_set_tag(v___x_1964_, 7);
lean_ctor_set(v___x_1964_, 1, v___x_2014_);
lean_ctor_set(v___x_1964_, 0, v___x_2013_);
v___x_2016_ = v___x_1964_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = l_Lean_MessageData_ofExpr(v_snd_1983_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 7);
lean_ctor_set(v___x_1956_, 1, v___x_2005_);
lean_ctor_set(v___x_1956_, 0, v___x_2017_);
v___x_2019_ = v___x_1956_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2005_);
v___x_2019_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = l_Lean_MessageData_ofExpr(v_snd_1994_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set_tag(v___x_1951_, 7);
lean_ctor_set(v___x_1951_, 1, v___x_2020_);
lean_ctor_set(v___x_1951_, 0, v___x_2019_);
v___x_2022_ = v___x_1951_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2023_ = l_Lean_indentD(v___x_2022_);
v___x_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2016_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2002_, v___x_2024_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_dec_ref_known(v___x_2025_, 1);
v___y_1932_ = v___y_1973_;
v___y_1933_ = v___y_1974_;
v___y_1934_ = v___y_1975_;
v___y_1935_ = v___y_1976_;
goto v___jp_1931_;
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
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
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_dec(v_fst_1982_);
lean_del_object(v___x_1969_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_del_object(v___x_1951_);
v_a_2041_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_1991_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_1991_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_a_1988_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_dec(v_fst_1982_);
lean_del_object(v___x_1969_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_del_object(v___x_1951_);
v_a_2049_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_1989_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_1989_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_dec(v_fst_1982_);
lean_del_object(v___x_1969_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_del_object(v___x_1951_);
v_a_2057_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_1987_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_1987_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_1969_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_del_object(v___x_1951_);
v_a_2066_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_1980_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_1980_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_del_object(v___x_1951_);
if (v_failed_1972_ == 0)
{
v___y_1924_ = v___y_1973_;
v___y_1925_ = v___y_1974_;
v___y_1926_ = v___y_1975_;
v___y_1927_ = v___y_1976_;
goto v___jp_1923_;
}
else
{
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v___y_1932_ = v___y_1973_;
v___y_1933_ = v___y_1974_;
v___y_1934_ = v___y_1975_;
v___y_1935_ = v___y_1976_;
goto v___jp_1931_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_del_object(v___x_1951_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v_a_2074_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_1977_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_1977_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1959_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_dec(v_fst_1953_);
lean_del_object(v___x_1951_);
lean_dec(v_fst_1949_);
v___y_1924_ = v_a_1912_;
v___y_1925_ = v_a_1913_;
v___y_1926_ = v_a_1914_;
v___y_1927_ = v_a_1915_;
goto v___jp_1923_;
}
}
}
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec(v_a_1946_);
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v___x_2194_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9);
v___x_2195_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v___x_2194_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
return v___x_2195_;
}
v___jp_1923_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3);
v___x_1929_ = lean_box(0);
v___x_1930_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1928_, v_expectedType_1910_, v___x_1922_, v_result_1911_, v___x_1929_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1930_;
}
v___jp_1931_:
{
lean_object* v___x_1936_; lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v___x_1936_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref(v_result_1911_);
lean_dec_ref(v_expectedType_1910_);
v_a_2196_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_1918_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_1918_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(lean_object* v_steps_2204_, lean_object* v_expectedType_2205_, lean_object* v_result_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2204_, v_expectedType_2205_, v_result_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec_ref(v_steps_2204_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure(lean_object* v_00_u03b1_2213_, lean_object* v_steps_2214_, lean_object* v_expectedType_2215_, lean_object* v_result_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2214_, v_expectedType_2215_, v_result_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___boxed(lean_object* v_00_u03b1_2223_, lean_object* v_steps_2224_, lean_object* v_expectedType_2225_, lean_object* v_result_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Elab_Term_throwCalcFailure(v_00_u03b1_2223_, v_steps_2224_, v_expectedType_2225_, v_result_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec_ref(v_steps_2224_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0(lean_object* v_a_2233_, lean_object* v_x_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2233_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0___boxed(lean_object* v_a_2243_, lean_object* v_x_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Elab_Term_elabCalc___lam__0(v_a_2243_, v_x_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v_x_2244_);
lean_dec_ref(v_a_2243_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1(lean_object* v_a_2253_, lean_object* v_x_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2253_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1___boxed(lean_object* v_a_2263_, lean_object* v_x_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Elab_Term_elabCalc___lam__1(v_a_2263_, v_x_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v_x_2264_);
lean_dec_ref(v_a_2263_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object* v_x_2277_, lean_object* v_x_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
lean_inc(v_x_2277_);
v___x_2287_ = l_Lean_Syntax_isOfKind(v_x_2277_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; 
lean_dec(v_x_2278_);
lean_dec(v_x_2277_);
v___x_2288_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2288_;
}
else
{
lean_object* v___x_2289_; lean_object* v_steps_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2289_ = lean_unsigned_to_nat(1u);
v_steps_2290_ = l_Lean_Syntax_getArg(v_x_2277_, v___x_2289_);
v___x_2291_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_2290_);
v___x_2292_ = l_Lean_Syntax_isOfKind(v_steps_2290_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; 
lean_dec(v_steps_2290_);
lean_dec(v_x_2278_);
lean_dec(v_x_2277_);
v___x_2293_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2293_;
}
else
{
lean_object* v_toCold_2294_; lean_object* v_currRecDepth_2295_; lean_object* v_ref_2296_; uint16_t v_optionFlags_2297_; uint8_t v_suppressElabErrors_2298_; uint8_t v_isRecordingDeps_2299_; lean_object* v___x_2300_; lean_object* v_tk_2301_; lean_object* v_ref_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_toCold_2294_ = lean_ctor_get(v_a_2283_, 0);
v_currRecDepth_2295_ = lean_ctor_get(v_a_2283_, 1);
v_ref_2296_ = lean_ctor_get(v_a_2283_, 2);
v_optionFlags_2297_ = lean_ctor_get_uint16(v_a_2283_, sizeof(void*)*3);
v_suppressElabErrors_2298_ = lean_ctor_get_uint8(v_a_2283_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2299_ = lean_ctor_get_uint8(v_a_2283_, sizeof(void*)*3 + 3);
v___x_2300_ = lean_unsigned_to_nat(0u);
v_tk_2301_ = l_Lean_Syntax_getArg(v_x_2277_, v___x_2300_);
lean_dec(v_x_2277_);
v_ref_2302_ = l_Lean_replaceRef(v_tk_2301_, v_ref_2296_);
lean_dec(v_tk_2301_);
lean_inc(v_currRecDepth_2295_);
lean_inc_ref(v_toCold_2294_);
v___x_2303_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2303_, 0, v_toCold_2294_);
lean_ctor_set(v___x_2303_, 1, v_currRecDepth_2295_);
lean_ctor_set(v___x_2303_, 2, v_ref_2302_);
lean_ctor_set_uint16(v___x_2303_, sizeof(void*)*3, v_optionFlags_2297_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*3 + 2, v_suppressElabErrors_2298_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*3 + 3, v_isRecordingDeps_2299_);
v___x_2304_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_2290_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v___x_2303_, v_a_2284_);
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
v___x_2308_ = l_Lean_Elab_Term_elabCalcSteps(v_a_2305_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v___x_2303_, v_a_2284_);
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
v___x_2311_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(v_x_2278_, v_fst_2310_, v___f_2306_, v___f_2307_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v___x_2303_, v_a_2284_);
lean_dec_ref_known(v___x_2303_, 3);
return v___x_2311_;
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v___f_2307_);
lean_dec_ref(v___f_2306_);
lean_dec_ref_known(v___x_2303_, 3);
lean_dec(v_x_2278_);
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
lean_dec(v_x_2278_);
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
