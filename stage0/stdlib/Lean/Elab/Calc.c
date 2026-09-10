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
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Elaborator for the `calc` term mode variant. "};
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
lean_inc_ref(v_str_720_);
lean_inc(v_pre_719_);
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
lean_inc_ref(v_str_720_);
lean_inc(v_pre_719_);
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
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Elab_Term_exprToSyntax(v_type_662_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_toCold_745_; lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_778_; 
v_toCold_745_ = lean_ctor_get(v_a_669_, 0);
v_a_746_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_778_ == 0)
{
v___x_748_ = v___x_744_;
v_isShared_749_ = v_isSharedCheck_778_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_778_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_ref_750_; lean_object* v_quotContext_751_; lean_object* v_currMacroScope_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v_ref_750_ = lean_ctor_get(v_a_669_, 2);
v_quotContext_751_ = lean_ctor_get(v_toCold_745_, 8);
v_currMacroScope_752_ = lean_ctor_get(v_toCold_745_, 9);
v___x_753_ = 0;
v___x_754_ = l_Lean_SourceInfo_fromRef(v_ref_750_, v___x_753_);
v___x_755_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5));
v___x_756_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7));
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8));
lean_inc_n(v___x_754_, 7);
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_754_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10));
v___x_760_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12);
lean_inc(v_currMacroScope_752_);
lean_inc(v_quotContext_751_);
v___x_761_ = l_Lean_addMacroScope(v_quotContext_751_, v_pre_719_, v_currMacroScope_752_);
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
v___x_769_ = l_Lean_Syntax_node1(v___x_754_, v___x_768_, v_a_746_);
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24));
v___x_771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_754_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_Syntax_node5(v___x_754_, v___x_755_, v___x_765_, v_t_663_, v___x_767_, v___x_769_, v___x_771_);
v___x_773_ = lean_box(v___x_753_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_774_);
v___x_776_ = v___x_748_;
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
v_a_779_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_744_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_744_);
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
lean_object* v_v_807_; lean_object* v___x_808_; 
v_v_807_ = lean_array_uget_borrowed(v_bs_794_, v_i_793_);
lean_inc(v_v_807_);
lean_inc_ref(v_type_791_);
v___x_808_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_791_, v_v_807_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_fst_810_; lean_object* v_snd_811_; lean_object* v___x_812_; lean_object* v_bs_x27_813_; size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v_fst_810_ = lean_ctor_get(v_a_809_, 0);
lean_inc(v_fst_810_);
v_snd_811_ = lean_ctor_get(v_a_809_, 1);
lean_inc(v_snd_811_);
lean_dec(v_a_809_);
v___x_812_ = lean_unsigned_to_nat(0u);
v_bs_x27_813_ = lean_array_uset(v_bs_794_, v_i_793_, v___x_812_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_i_793_, v___x_814_);
v___x_816_ = lean_array_uset(v_bs_x27_813_, v_i_793_, v_fst_810_);
v___x_817_ = lean_unbox(v_snd_811_);
lean_dec(v_snd_811_);
v_i_793_ = v___x_815_;
v_bs_794_ = v___x_816_;
v___y_795_ = v___x_817_;
goto _start;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_bs_794_);
lean_dec_ref(v_type_791_);
v_a_819_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_808_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_808_);
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
size_t v_sz_boxed_839_; size_t v_i_boxed_840_; uint8_t v___y_7631__boxed_841_; lean_object* v_res_842_; 
v_sz_boxed_839_ = lean_unbox_usize(v_sz_828_);
lean_dec(v_sz_828_);
v_i_boxed_840_ = lean_unbox_usize(v_i_829_);
lean_dec(v_i_829_);
v___y_7631__boxed_841_ = lean_unbox(v___y_831_);
v_res_842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_827_, v_sz_boxed_839_, v_i_boxed_840_, v_bs_830_, v___y_7631__boxed_841_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
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
uint8_t v_a_7700__boxed_853_; lean_object* v_res_854_; 
v_a_7700__boxed_853_ = lean_unbox(v_a_845_);
v_res_854_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_843_, v_t_844_, v_a_7700__boxed_853_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
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
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_1059_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_rest_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; size_t v_sz_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = lean_unsigned_to_nat(1u);
v___x_1066_ = l_Lean_Syntax_getArg(v_steps_1047_, v___x_1065_);
lean_dec(v_steps_1047_);
v_rest_1067_ = l_Lean_Syntax_getArgs(v___x_1066_);
lean_dec(v___x_1066_);
v___x_1068_ = lean_mk_empty_array_with_capacity(v___x_1065_);
v___x_1069_ = lean_array_push(v___x_1068_, v_a_1064_);
v_sz_1070_ = lean_array_size(v_rest_1067_);
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_rest_1067_, v_sz_1070_, v___x_1071_, v___x_1069_);
lean_dec_ref(v_rest_1067_);
return v___x_1072_;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_steps_1047_);
v_a_1073_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1063_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1063_);
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
lean_object* v_toCold_1177_; lean_object* v_options_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v_toCold_1177_ = lean_ctor_get(v___y_1175_, 0);
v_options_1178_ = lean_ctor_get(v_toCold_1177_, 2);
v___x_1179_ = l_Lean_Elab_pp_macroStack;
v___x_1180_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_options_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_dec(v_macroStack_1174_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_msgData_1173_);
return v___x_1181_;
}
else
{
if (lean_obj_tag(v_macroStack_1174_) == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_msgData_1173_);
return v___x_1182_;
}
else
{
lean_object* v_head_1183_; lean_object* v_after_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1199_; 
v_head_1183_ = lean_ctor_get(v_macroStack_1174_, 0);
lean_inc(v_head_1183_);
v_after_1184_ = lean_ctor_get(v_head_1183_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_head_1183_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v_head_1183_, 0);
lean_dec(v_unused_1200_);
v___x_1186_ = v_head_1183_;
v_isShared_1187_ = v_isSharedCheck_1199_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_after_1184_);
lean_dec(v_head_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1199_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 7);
lean_ctor_set(v___x_1186_, 1, v___x_1188_);
lean_ctor_set(v___x_1186_, 0, v_msgData_1173_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_msgData_1173_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v_msgData_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1191_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_MessageData_ofSyntax(v_after_1184_);
v___x_1194_ = l_Lean_indentD(v___x_1193_);
v_msgData_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1195_, 0, v___x_1192_);
lean_ctor_set(v_msgData_1195_, 1, v___x_1194_);
v___x_1196_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(v_msgData_1195_, v_macroStack_1174_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1201_, lean_object* v_macroStack_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1201_, v_macroStack_1202_, v___y_1203_);
lean_dec_ref(v___y_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(lean_object* v_msg_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_ref_1214_; lean_object* v___x_1215_; lean_object* v_a_1216_; lean_object* v_macroStack_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1228_; 
v_ref_1214_ = lean_ctor_get(v___y_1211_, 2);
v___x_1215_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_1206_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v___x_1215_);
v_macroStack_1217_ = lean_ctor_get(v___y_1207_, 1);
v___x_1218_ = l_Lean_Elab_getBetterRef(v_ref_1214_, v_macroStack_1217_);
lean_inc(v_macroStack_1217_);
v___x_1219_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_a_1216_, v_macroStack_1217_, v___y_1211_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1228_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1228_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1218_);
lean_ctor_set(v___x_1224_, 1, v_a_1220_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set_tag(v___x_1222_, 1);
lean_ctor_set(v___x_1222_, 0, v___x_1224_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(lean_object* v_ref_1238_, lean_object* v_msg_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_toCold_1247_; lean_object* v_currRecDepth_1248_; lean_object* v_ref_1249_; uint8_t v_diag_1250_; uint8_t v_suppressElabErrors_1251_; lean_object* v_ref_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_toCold_1247_ = lean_ctor_get(v___y_1244_, 0);
v_currRecDepth_1248_ = lean_ctor_get(v___y_1244_, 1);
v_ref_1249_ = lean_ctor_get(v___y_1244_, 2);
v_diag_1250_ = lean_ctor_get_uint8(v___y_1244_, sizeof(void*)*3);
v_suppressElabErrors_1251_ = lean_ctor_get_uint8(v___y_1244_, sizeof(void*)*3 + 1);
v_ref_1252_ = l_Lean_replaceRef(v_ref_1238_, v_ref_1249_);
lean_inc(v_currRecDepth_1248_);
lean_inc_ref(v_toCold_1247_);
v___x_1253_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1253_, 0, v_toCold_1247_);
lean_ctor_set(v___x_1253_, 1, v_currRecDepth_1248_);
lean_ctor_set(v___x_1253_, 2, v_ref_1252_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*3, v_diag_1250_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*3 + 1, v_suppressElabErrors_1251_);
v___x_1254_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___x_1253_, v___y_1245_);
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
lean_object* v_fst_1301_; lean_object* v_snd_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1507_; 
v_fst_1301_ = lean_ctor_get(v_b_1280_, 0);
v_snd_1302_ = lean_ctor_get(v_b_1280_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_b_1280_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1304_ = v_b_1280_;
v_isShared_1305_ = v_isSharedCheck_1507_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_snd_1302_);
lean_inc(v_fst_1301_);
lean_dec(v_b_1280_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1507_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v_a_1306_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v_____do__lift_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; 
v_a_1306_ = lean_array_uget_borrowed(v_as_1277_, v_i_1279_);
if (lean_obj_tag(v_snd_1302_) == 1)
{
lean_object* v_val_1484_; lean_object* v___x_1485_; 
v_val_1484_ = lean_ctor_get(v_snd_1302_, 0);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v_val_1484_);
v___x_1485_ = lean_infer_type(v_val_1484_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v_term_1487_; lean_object* v___x_1488_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v_term_1487_ = lean_ctor_get(v_a_1306_, 1);
lean_inc(v_term_1487_);
v___x_1488_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_term_1487_, v_a_1486_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v_____do__lift_1367_ = v_a_1489_;
v___y_1368_ = v___y_1281_;
v___y_1369_ = v___y_1282_;
v___y_1370_ = v___y_1283_;
v___y_1371_ = v___y_1284_;
v___y_1372_ = v___y_1285_;
v___y_1373_ = v___y_1286_;
goto v___jp_1366_;
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref_known(v_snd_1302_, 1);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
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
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref_known(v_snd_1302_, 1);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1498_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1485_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1485_);
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
lean_object* v_term_1506_; 
v_term_1506_ = lean_ctor_get(v_a_1306_, 1);
lean_inc(v_term_1506_);
v_____do__lift_1367_ = v_term_1506_;
v___y_1368_ = v___y_1281_;
v___y_1369_ = v___y_1282_;
v___y_1370_ = v___y_1283_;
v___y_1371_ = v___y_1284_;
v___y_1372_ = v___y_1285_;
v___y_1373_ = v___y_1286_;
goto v___jp_1366_;
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
lean_object* v_toCold_1329_; lean_object* v_currRecDepth_1330_; lean_object* v_ref_1331_; uint8_t v_diag_1332_; uint8_t v_suppressElabErrors_1333_; lean_object* v_ref_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref_known(v___x_1328_, 1);
v_toCold_1329_ = lean_ctor_get(v___y_1314_, 0);
v_currRecDepth_1330_ = lean_ctor_get(v___y_1314_, 1);
v_ref_1331_ = lean_ctor_get(v___y_1314_, 2);
v_diag_1332_ = lean_ctor_get_uint8(v___y_1314_, sizeof(void*)*3);
v_suppressElabErrors_1333_ = lean_ctor_get_uint8(v___y_1314_, sizeof(void*)*3 + 1);
v_ref_1334_ = l_Lean_replaceRef(v_term_1316_, v_ref_1331_);
lean_inc(v_currRecDepth_1330_);
lean_inc_ref(v_toCold_1329_);
v___x_1335_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1335_, 0, v_toCold_1329_);
lean_ctor_set(v___x_1335_, 1, v_currRecDepth_1330_);
lean_ctor_set(v___x_1335_, 2, v_ref_1334_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3, v_diag_1332_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3 + 1, v_suppressElabErrors_1333_);
v___x_1336_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_1326_, v_snd_1327_, v_a_1325_, v___y_1309_, v___y_1312_, v___y_1313_, v___x_1335_, v___y_1315_);
lean_dec_ref_known(v___x_1335_, 3);
lean_dec(v_snd_1327_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v___y_1294_ = v___y_1308_;
v_____do__lift_1295_ = v_a_1337_;
goto v___jp_1293_;
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v___y_1308_);
v_a_1338_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1336_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1336_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_snd_1327_);
lean_dec(v_fst_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v___y_1308_);
v_a_1346_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1328_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1328_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; 
lean_dec(v_fst_1301_);
v_a_1354_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1323_, 1);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v___y_1309_);
lean_ctor_set(v___x_1304_, 0, v_a_1354_);
v___x_1356_ = v___x_1304_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1354_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___y_1309_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
v___y_1294_ = v___y_1308_;
v_____do__lift_1295_ = v___x_1356_;
goto v___jp_1293_;
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1358_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1323_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1323_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
v___jp_1366_:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_Elab_Term_elabType(v_____do__lift_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_1375_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
if (lean_obj_tag(v_a_1377_) == 1)
{
lean_object* v_val_1378_; lean_object* v_snd_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1452_; 
v_val_1378_ = lean_ctor_get(v_a_1377_, 0);
lean_inc(v_val_1378_);
lean_dec_ref_known(v_a_1377_, 1);
v_snd_1379_ = lean_ctor_get(v_val_1378_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_val_1378_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_val_1378_, 0);
lean_dec(v_unused_1453_);
v___x_1381_ = v_val_1378_;
v_isShared_1382_ = v_isSharedCheck_1452_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_snd_1379_);
lean_dec(v_val_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1452_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
if (lean_obj_tag(v_snd_1302_) == 1)
{
lean_object* v_fst_1383_; lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1450_; 
v_fst_1383_ = lean_ctor_get(v_snd_1379_, 0);
v_snd_1384_ = lean_ctor_get(v_snd_1379_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_snd_1379_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1386_ = v_snd_1379_;
v_isShared_1387_ = v_isSharedCheck_1450_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_inc(v_fst_1383_);
lean_dec(v_snd_1379_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1450_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_val_1388_; lean_object* v___x_1389_; 
v_val_1388_ = lean_ctor_get(v_snd_1302_, 0);
lean_inc_n(v_val_1388_, 2);
lean_dec_ref_known(v_snd_1302_, 1);
lean_inc(v_fst_1383_);
v___x_1389_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1383_, v_val_1388_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; uint8_t v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = lean_unbox(v_a_1390_);
lean_dec(v_a_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc_ref(v___y_1370_);
lean_inc(v_fst_1383_);
v___x_1392_ = lean_infer_type(v_fst_1383_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc_ref(v___y_1370_);
lean_inc(v_val_1388_);
v___x_1394_ = lean_infer_type(v_val_1388_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v_term_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v_term_1396_ = lean_ctor_get(v_a_1306_, 1);
v___x_1397_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_1398_ = l_Lean_MessageData_ofExpr(v_fst_1383_);
v___x_1399_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 7);
lean_ctor_set(v___x_1386_, 1, v___x_1399_);
lean_ctor_set(v___x_1386_, 0, v___x_1398_);
v___x_1401_ = v___x_1386_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = l_Lean_MessageData_ofExpr(v_a_1393_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 7);
lean_ctor_set(v___x_1381_, 1, v___x_1402_);
lean_ctor_set(v___x_1381_, 0, v___x_1401_);
v___x_1404_ = v___x_1381_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1405_ = l_Lean_indentD(v___x_1404_);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1397_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = l_Lean_MessageData_ofExpr(v_val_1388_);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v___x_1399_);
v___x_1411_ = l_Lean_MessageData_ofExpr(v_a_1395_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = l_Lean_indentD(v___x_1412_);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1408_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1396_, v___x_1414_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec_ref_known(v___x_1415_, 1);
v___y_1308_ = v_snd_1384_;
v___y_1309_ = v_a_1375_;
v___y_1310_ = v___y_1368_;
v___y_1311_ = v___y_1369_;
v___y_1312_ = v___y_1370_;
v___y_1313_ = v___y_1371_;
v___y_1314_ = v___y_1372_;
v___y_1315_ = v___y_1373_;
goto v___jp_1307_;
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_snd_1384_);
lean_dec(v_a_1375_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_a_1393_);
lean_dec(v_val_1388_);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_fst_1383_);
lean_del_object(v___x_1381_);
lean_dec(v_a_1375_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1426_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1394_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1394_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_val_1388_);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_fst_1383_);
lean_del_object(v___x_1381_);
lean_dec(v_a_1375_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1434_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1392_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1392_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_dec(v_val_1388_);
lean_del_object(v___x_1386_);
lean_dec(v_fst_1383_);
lean_del_object(v___x_1381_);
v___y_1308_ = v_snd_1384_;
v___y_1309_ = v_a_1375_;
v___y_1310_ = v___y_1368_;
v___y_1311_ = v___y_1369_;
v___y_1312_ = v___y_1370_;
v___y_1313_ = v___y_1371_;
v___y_1314_ = v___y_1372_;
v___y_1315_ = v___y_1373_;
goto v___jp_1307_;
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_val_1388_);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_fst_1383_);
lean_del_object(v___x_1381_);
lean_dec(v_a_1375_);
lean_del_object(v___x_1304_);
lean_dec(v_fst_1301_);
v_a_1442_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1389_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1389_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
else
{
lean_object* v_snd_1451_; 
lean_del_object(v___x_1381_);
lean_dec(v_snd_1302_);
v_snd_1451_ = lean_ctor_get(v_snd_1379_, 1);
lean_inc(v_snd_1451_);
lean_dec(v_snd_1379_);
v___y_1308_ = v_snd_1451_;
v___y_1309_ = v_a_1375_;
v___y_1310_ = v___y_1368_;
v___y_1311_ = v___y_1369_;
v___y_1312_ = v___y_1370_;
v___y_1313_ = v___y_1371_;
v___y_1314_ = v___y_1372_;
v___y_1315_ = v___y_1373_;
goto v___jp_1307_;
}
}
}
else
{
lean_object* v_term_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v_a_1377_);
lean_del_object(v___x_1304_);
v_term_1454_ = lean_ctor_get(v_a_1306_, 1);
v___x_1455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7);
v___x_1456_ = l_Lean_indentExpr(v_a_1375_);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1454_, v___x_1457_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v___x_1459_; 
lean_dec_ref_known(v___x_1458_, 1);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_fst_1301_);
lean_ctor_set(v___x_1459_, 1, v_snd_1302_);
v_a_1289_ = v___x_1459_;
goto v___jp_1288_;
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_snd_1302_);
lean_dec(v_fst_1301_);
v_a_1460_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1458_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1458_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_a_1375_);
lean_del_object(v___x_1304_);
lean_dec(v_snd_1302_);
lean_dec(v_fst_1301_);
v_a_1468_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1376_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1376_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_del_object(v___x_1304_);
lean_dec(v_snd_1302_);
lean_dec(v_fst_1301_);
v_a_1476_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1374_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1374_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___boxed(lean_object* v_as_1508_, lean_object* v_sz_1509_, lean_object* v_i_1510_, lean_object* v_b_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
size_t v_sz_boxed_1519_; size_t v_i_boxed_1520_; lean_object* v_res_1521_; 
v_sz_boxed_1519_ = lean_unbox_usize(v_sz_1509_);
lean_dec(v_sz_1509_);
v_i_boxed_1520_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_as_1508_, v_sz_boxed_1519_, v_i_boxed_1520_, v_b_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec_ref(v_as_1508_);
return v_res_1521_;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__4(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1527_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__3));
v___x_1528_ = lean_unsigned_to_nat(14u);
v___x_1529_ = lean_unsigned_to_nat(22u);
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__2));
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__1));
v___x_1532_ = l_mkPanicMessageWithDecl(v___x_1531_, v___x_1530_, v___x_1529_, v___x_1528_, v___x_1527_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object* v_steps_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; size_t v_sz_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
v___x_1541_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__0));
v_sz_1542_ = lean_array_size(v_steps_1533_);
v___x_1543_ = ((size_t)0ULL);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_steps_1533_, v_sz_1542_, v___x_1543_, v___x_1541_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1560_; 
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v___x_1546_, 0);
lean_dec(v_unused_1561_);
v___x_1548_ = v___x_1546_;
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
else
{
lean_dec(v___x_1546_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_fst_1550_; 
v_fst_1550_ = lean_ctor_get(v_a_1545_, 0);
lean_inc(v_fst_1550_);
lean_dec(v_a_1545_);
if (lean_obj_tag(v_fst_1550_) == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1551_ = lean_obj_once(&l_Lean_Elab_Term_elabCalcSteps___closed__4, &l_Lean_Elab_Term_elabCalcSteps___closed__4_once, _init_l_Lean_Elab_Term_elabCalcSteps___closed__4);
v___x_1552_ = l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(v___x_1551_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1552_);
v___x_1554_ = v___x_1548_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
else
{
lean_object* v_val_1556_; lean_object* v___x_1558_; 
v_val_1556_ = lean_ctor_get(v_fst_1550_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v_fst_1550_, 1);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v_val_1556_);
v___x_1558_ = v___x_1548_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_val_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_a_1545_);
v_a_1562_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1546_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1546_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
v_a_1570_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1544_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1544_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps___boxed(lean_object* v_steps_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Elab_Term_elabCalcSteps(v_steps_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec_ref(v_steps_1578_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(lean_object* v_00_u03b1_1587_, lean_object* v_ref_1588_, lean_object* v_msg_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1588_, v_msg_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___boxed(lean_object* v_00_u03b1_1598_, lean_object* v_ref_1599_, lean_object* v_msg_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(v_00_u03b1_1598_, v_ref_1599_, v_msg_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v_ref_1599_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(lean_object* v_00_u03b1_1609_, lean_object* v_msg_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1619_, lean_object* v_msg_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(v_00_u03b1_1619_, v_msg_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(lean_object* v_msgData_1629_, lean_object* v_macroStack_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1629_, v_macroStack_1630_, v___y_1635_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1639_, lean_object* v_macroStack_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(v_msgData_1639_, v_macroStack_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1648_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_box(0);
v___x_1650_ = l_Lean_Elab_abortTermExceptionId;
v___x_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v___x_1649_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg(){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___boxed(lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(lean_object* v_00_u03b1_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___boxed(lean_object* v_00_u03b1_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(v_00_u03b1_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(lean_object* v_msg_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___f_1677_; lean_object* v___x_4885__overap_1678_; lean_object* v___x_1679_; 
v___f_1677_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_4885__overap_1678_ = lean_panic_fn_borrowed(v___f_1677_, v_msg_1671_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
v___x_1679_ = lean_apply_5(v___x_4885__overap_1678_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, lean_box(0));
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg___boxed(lean_object* v_msg_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(lean_object* v_00_u03b1_1687_, lean_object* v_msg_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_msg_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(v_00_u03b1_1695_, v_msg_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(uint8_t v_suppressElabErrors_1710_, uint8_t v___y_1711_, lean_object* v_x_1712_){
_start:
{
if (lean_obj_tag(v_x_1712_) == 1)
{
lean_object* v_pre_1713_; 
v_pre_1713_ = lean_ctor_get(v_x_1712_, 0);
switch(lean_obj_tag(v_pre_1713_))
{
case 1:
{
lean_object* v_pre_1714_; 
v_pre_1714_ = lean_ctor_get(v_pre_1713_, 0);
switch(lean_obj_tag(v_pre_1714_))
{
case 0:
{
lean_object* v_str_1715_; lean_object* v_str_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_str_1715_ = lean_ctor_get(v_x_1712_, 1);
v_str_1716_ = lean_ctor_get(v_pre_1713_, 1);
v___x_1717_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13));
v___x_1718_ = lean_string_dec_eq(v_str_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0));
v___x_1720_ = lean_string_dec_eq(v_str_1716_, v___x_1719_);
if (v___x_1720_ == 0)
{
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1));
v___x_1722_ = lean_string_dec_eq(v_str_1715_, v___x_1721_);
if (v___x_1722_ == 0)
{
return v___x_1722_;
}
else
{
return v_suppressElabErrors_1710_;
}
}
}
else
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2));
v___x_1724_ = lean_string_dec_eq(v_str_1715_, v___x_1723_);
if (v___x_1724_ == 0)
{
return v___x_1724_;
}
else
{
return v_suppressElabErrors_1710_;
}
}
}
case 1:
{
lean_object* v_pre_1725_; 
v_pre_1725_ = lean_ctor_get(v_pre_1714_, 0);
if (lean_obj_tag(v_pre_1725_) == 0)
{
lean_object* v_str_1726_; lean_object* v_str_1727_; lean_object* v_str_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v_str_1726_ = lean_ctor_get(v_x_1712_, 1);
v_str_1727_ = lean_ctor_get(v_pre_1713_, 1);
v_str_1728_ = lean_ctor_get(v_pre_1714_, 1);
v___x_1729_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3));
v___x_1730_ = lean_string_dec_eq(v_str_1728_, v___x_1729_);
if (v___x_1730_ == 0)
{
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4));
v___x_1732_ = lean_string_dec_eq(v_str_1727_, v___x_1731_);
if (v___x_1732_ == 0)
{
return v___x_1732_;
}
else
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5));
v___x_1734_ = lean_string_dec_eq(v_str_1726_, v___x_1733_);
if (v___x_1734_ == 0)
{
return v___x_1734_;
}
else
{
return v_suppressElabErrors_1710_;
}
}
}
}
else
{
return v___y_1711_;
}
}
default: 
{
return v___y_1711_;
}
}
}
case 0:
{
lean_object* v_str_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v_str_1735_ = lean_ctor_get(v_x_1712_, 1);
v___x_1736_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6));
v___x_1737_ = lean_string_dec_eq(v_str_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
return v___x_1737_;
}
else
{
return v_suppressElabErrors_1710_;
}
}
default: 
{
return v___y_1711_;
}
}
}
else
{
return v___y_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1738_, lean_object* v___y_1739_, lean_object* v_x_1740_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1741_; uint8_t v___y_7558__boxed_1742_; uint8_t v_res_1743_; lean_object* v_r_1744_; 
v_suppressElabErrors_boxed_1741_ = lean_unbox(v_suppressElabErrors_1738_);
v___y_7558__boxed_1742_ = lean_unbox(v___y_1739_);
v_res_1743_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_1741_, v___y_7558__boxed_1742_, v_x_1740_);
lean_dec(v_x_1740_);
v_r_1744_ = lean_box(v_res_1743_);
return v_r_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(lean_object* v_ref_1745_, lean_object* v_msgData_1746_, uint8_t v_severity_1747_, uint8_t v_isSilent_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___y_1755_; uint8_t v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; uint8_t v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; uint8_t v___y_1795_; uint8_t v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1817_; lean_object* v___y_1818_; uint8_t v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; uint8_t v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; uint8_t v___y_1831_; lean_object* v___y_1832_; uint8_t v___y_1833_; uint8_t v___y_1834_; uint8_t v___x_1839_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; uint8_t v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; uint8_t v___y_1847_; uint8_t v___y_1849_; uint8_t v___x_1865_; 
v___x_1839_ = 2;
v___x_1865_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1747_, v___x_1839_);
if (v___x_1865_ == 0)
{
v___y_1849_ = v___x_1865_;
goto v___jp_1848_;
}
else
{
uint8_t v___x_1866_; 
lean_inc_ref(v_msgData_1746_);
v___x_1866_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1746_);
v___y_1849_ = v___x_1866_;
goto v___jp_1848_;
}
v___jp_1754_:
{
lean_object* v___x_1764_; lean_object* v_toCold_1765_; lean_object* v_currNamespace_1766_; lean_object* v_openDecls_1767_; lean_object* v_env_1768_; lean_object* v_nextMacroScope_1769_; lean_object* v_ngen_1770_; lean_object* v_auxDeclNGen_1771_; lean_object* v_traceState_1772_; lean_object* v_cache_1773_; lean_object* v_messages_1774_; lean_object* v_infoState_1775_; lean_object* v_snapshotTasks_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1790_; 
v___x_1764_ = lean_st_ref_take(v___y_1763_);
v_toCold_1765_ = lean_ctor_get(v___y_1762_, 0);
v_currNamespace_1766_ = lean_ctor_get(v_toCold_1765_, 4);
v_openDecls_1767_ = lean_ctor_get(v_toCold_1765_, 5);
v_env_1768_ = lean_ctor_get(v___x_1764_, 0);
v_nextMacroScope_1769_ = lean_ctor_get(v___x_1764_, 1);
v_ngen_1770_ = lean_ctor_get(v___x_1764_, 2);
v_auxDeclNGen_1771_ = lean_ctor_get(v___x_1764_, 3);
v_traceState_1772_ = lean_ctor_get(v___x_1764_, 4);
v_cache_1773_ = lean_ctor_get(v___x_1764_, 5);
v_messages_1774_ = lean_ctor_get(v___x_1764_, 6);
v_infoState_1775_ = lean_ctor_get(v___x_1764_, 7);
v_snapshotTasks_1776_ = lean_ctor_get(v___x_1764_, 8);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1778_ = v___x_1764_;
v_isShared_1779_ = v_isSharedCheck_1790_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_snapshotTasks_1776_);
lean_inc(v_infoState_1775_);
lean_inc(v_messages_1774_);
lean_inc(v_cache_1773_);
lean_inc(v_traceState_1772_);
lean_inc(v_auxDeclNGen_1771_);
lean_inc(v_ngen_1770_);
lean_inc(v_nextMacroScope_1769_);
lean_inc(v_env_1768_);
lean_dec(v___x_1764_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1790_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
lean_inc(v_openDecls_1767_);
lean_inc(v_currNamespace_1766_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_currNamespace_1766_);
lean_ctor_set(v___x_1780_, 1, v_openDecls_1767_);
v___x_1781_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v___y_1758_);
lean_inc_ref(v___y_1760_);
lean_inc_ref(v___y_1757_);
v___x_1782_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1782_, 0, v___y_1757_);
lean_ctor_set(v___x_1782_, 1, v___y_1759_);
lean_ctor_set(v___x_1782_, 2, v___y_1755_);
lean_ctor_set(v___x_1782_, 3, v___y_1760_);
lean_ctor_set(v___x_1782_, 4, v___x_1781_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*5, v___y_1761_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*5 + 1, v___y_1756_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*5 + 2, v_isSilent_1748_);
v___x_1783_ = l_Lean_MessageLog_add(v___x_1782_, v_messages_1774_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 6, v___x_1783_);
v___x_1785_ = v___x_1778_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_env_1768_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_nextMacroScope_1769_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_ngen_1770_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_auxDeclNGen_1771_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_traceState_1772_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_cache_1773_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v_infoState_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v_snapshotTasks_1776_);
v___x_1785_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_st_ref_put(v___y_1763_, v___x_1785_);
v___x_1787_ = lean_box(0);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
}
v___jp_1791_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1815_; 
v___x_1800_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1746_);
v___x_1801_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v___x_1800_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1815_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1815_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_inc_ref_n(v___y_1793_, 2);
v___x_1806_ = l_Lean_FileMap_toPosition(v___y_1793_, v___y_1797_);
lean_dec(v___y_1797_);
v___x_1807_ = l_Lean_FileMap_toPosition(v___y_1793_, v___y_1799_);
lean_dec(v___y_1799_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
v___x_1809_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
if (v___y_1796_ == 0)
{
lean_del_object(v___x_1804_);
lean_dec_ref(v___y_1792_);
v___y_1755_ = v___x_1808_;
v___y_1756_ = v___y_1795_;
v___y_1757_ = v___y_1794_;
v___y_1758_ = v_a_1802_;
v___y_1759_ = v___x_1806_;
v___y_1760_ = v___x_1809_;
v___y_1761_ = v___y_1798_;
v___y_1762_ = v___y_1751_;
v___y_1763_ = v___y_1752_;
goto v___jp_1754_;
}
else
{
uint8_t v___x_1810_; 
lean_inc(v_a_1802_);
v___x_1810_ = l_Lean_MessageData_hasTag(v___y_1792_, v_a_1802_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
lean_dec_ref_known(v___x_1808_, 1);
lean_dec_ref(v___x_1806_);
lean_dec(v_a_1802_);
v___x_1811_ = lean_box(0);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1811_);
v___x_1813_ = v___x_1804_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
else
{
lean_del_object(v___x_1804_);
v___y_1755_ = v___x_1808_;
v___y_1756_ = v___y_1795_;
v___y_1757_ = v___y_1794_;
v___y_1758_ = v_a_1802_;
v___y_1759_ = v___x_1806_;
v___y_1760_ = v___x_1809_;
v___y_1761_ = v___y_1798_;
v___y_1762_ = v___y_1751_;
v___y_1763_ = v___y_1752_;
goto v___jp_1754_;
}
}
}
}
v___jp_1816_:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Syntax_getTailPos_x3f(v___y_1821_, v___y_1823_);
lean_dec(v___y_1821_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_inc(v___y_1824_);
v___y_1792_ = v___y_1817_;
v___y_1793_ = v___y_1818_;
v___y_1794_ = v___y_1820_;
v___y_1795_ = v___y_1819_;
v___y_1796_ = v___y_1822_;
v___y_1797_ = v___y_1824_;
v___y_1798_ = v___y_1823_;
v___y_1799_ = v___y_1824_;
goto v___jp_1791_;
}
else
{
lean_object* v_val_1826_; 
v_val_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_val_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___y_1792_ = v___y_1817_;
v___y_1793_ = v___y_1818_;
v___y_1794_ = v___y_1820_;
v___y_1795_ = v___y_1819_;
v___y_1796_ = v___y_1822_;
v___y_1797_ = v___y_1824_;
v___y_1798_ = v___y_1823_;
v___y_1799_ = v_val_1826_;
goto v___jp_1791_;
}
}
v___jp_1827_:
{
lean_object* v_ref_1835_; lean_object* v___x_1836_; 
v_ref_1835_ = l_Lean_replaceRef(v_ref_1745_, v___y_1832_);
v___x_1836_ = l_Lean_Syntax_getPos_x3f(v_ref_1835_, v___y_1833_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___y_1817_ = v___y_1828_;
v___y_1818_ = v___y_1829_;
v___y_1819_ = v___y_1834_;
v___y_1820_ = v___y_1830_;
v___y_1821_ = v_ref_1835_;
v___y_1822_ = v___y_1831_;
v___y_1823_ = v___y_1833_;
v___y_1824_ = v___x_1837_;
goto v___jp_1816_;
}
else
{
lean_object* v_val_1838_; 
v_val_1838_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v___x_1836_, 1);
v___y_1817_ = v___y_1828_;
v___y_1818_ = v___y_1829_;
v___y_1819_ = v___y_1834_;
v___y_1820_ = v___y_1830_;
v___y_1821_ = v_ref_1835_;
v___y_1822_ = v___y_1831_;
v___y_1823_ = v___y_1833_;
v___y_1824_ = v_val_1838_;
goto v___jp_1816_;
}
}
v___jp_1840_:
{
if (v___y_1847_ == 0)
{
v___y_1828_ = v___y_1843_;
v___y_1829_ = v___y_1841_;
v___y_1830_ = v___y_1842_;
v___y_1831_ = v___y_1844_;
v___y_1832_ = v___y_1845_;
v___y_1833_ = v___y_1846_;
v___y_1834_ = v_severity_1747_;
goto v___jp_1827_;
}
else
{
v___y_1828_ = v___y_1843_;
v___y_1829_ = v___y_1841_;
v___y_1830_ = v___y_1842_;
v___y_1831_ = v___y_1844_;
v___y_1832_ = v___y_1845_;
v___y_1833_ = v___y_1846_;
v___y_1834_ = v___x_1839_;
goto v___jp_1827_;
}
}
v___jp_1848_:
{
if (v___y_1849_ == 0)
{
lean_object* v_toCold_1850_; lean_object* v_ref_1851_; uint8_t v_suppressElabErrors_1852_; lean_object* v_fileName_1853_; lean_object* v_fileMap_1854_; lean_object* v_options_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___f_1858_; uint8_t v___x_1859_; uint8_t v___x_1860_; 
v_toCold_1850_ = lean_ctor_get(v___y_1751_, 0);
v_ref_1851_ = lean_ctor_get(v___y_1751_, 2);
v_suppressElabErrors_1852_ = lean_ctor_get_uint8(v___y_1751_, sizeof(void*)*3 + 1);
v_fileName_1853_ = lean_ctor_get(v_toCold_1850_, 0);
v_fileMap_1854_ = lean_ctor_get(v_toCold_1850_, 1);
v_options_1855_ = lean_ctor_get(v_toCold_1850_, 2);
v___x_1856_ = lean_box(v_suppressElabErrors_1852_);
v___x_1857_ = lean_box(v___y_1849_);
v___f_1858_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1858_, 0, v___x_1856_);
lean_closure_set(v___f_1858_, 1, v___x_1857_);
v___x_1859_ = 1;
v___x_1860_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1747_, v___x_1859_);
if (v___x_1860_ == 0)
{
v___y_1841_ = v_fileMap_1854_;
v___y_1842_ = v_fileName_1853_;
v___y_1843_ = v___f_1858_;
v___y_1844_ = v_suppressElabErrors_1852_;
v___y_1845_ = v_ref_1851_;
v___y_1846_ = v___y_1849_;
v___y_1847_ = v___x_1860_;
goto v___jp_1840_;
}
else
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = l_Lean_warningAsError;
v___x_1862_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_options_1855_, v___x_1861_);
v___y_1841_ = v_fileMap_1854_;
v___y_1842_ = v_fileName_1853_;
v___y_1843_ = v___f_1858_;
v___y_1844_ = v_suppressElabErrors_1852_;
v___y_1845_ = v_ref_1851_;
v___y_1846_ = v___y_1849_;
v___y_1847_ = v___x_1862_;
goto v___jp_1840_;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec_ref(v_msgData_1746_);
v___x_1863_ = lean_box(0);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___boxed(lean_object* v_ref_1867_, lean_object* v_msgData_1868_, lean_object* v_severity_1869_, lean_object* v_isSilent_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
uint8_t v_severity_boxed_1876_; uint8_t v_isSilent_boxed_1877_; lean_object* v_res_1878_; 
v_severity_boxed_1876_ = lean_unbox(v_severity_1869_);
v_isSilent_boxed_1877_ = lean_unbox(v_isSilent_1870_);
v_res_1878_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1867_, v_msgData_1868_, v_severity_boxed_1876_, v_isSilent_boxed_1877_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v_ref_1867_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(lean_object* v_ref_1879_, lean_object* v_msgData_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
uint8_t v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = 2;
v___x_1887_ = 0;
v___x_1888_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1879_, v_msgData_1880_, v___x_1886_, v___x_1887_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1___boxed(lean_object* v_ref_1889_, lean_object* v_msgData_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_ref_1889_, v_msgData_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v_ref_1889_);
return v_res_1896_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1));
v___x_1901_ = l_Lean_MessageData_ofFormat(v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2);
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4));
v___x_1906_ = l_Lean_stringToMessageData(v___x_1905_);
return v___x_1906_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6));
v___x_1909_ = l_Lean_stringToMessageData(v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1911_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_1912_ = lean_unsigned_to_nat(57u);
v___x_1913_ = lean_unsigned_to_nat(133u);
v___x_1914_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8));
v___x_1915_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_1916_ = l_mkPanicMessageWithDecl(v___x_1915_, v___x_1914_, v___x_1913_, v___x_1912_, v___x_1911_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object* v_steps_1917_, lean_object* v_expectedType_1918_, lean_object* v_result_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v___x_1925_; 
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
lean_inc(v_a_1921_);
lean_inc_ref(v_a_1920_);
lean_inc_ref(v_result_1919_);
v___x_1925_ = lean_infer_type(v_result_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___x_1952_; lean_object* v_a_1953_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_1926_, v_a_1921_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = l_Lean_Expr_headBeta(v_a_1928_);
v___x_1952_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_1929_);
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
if (lean_obj_tag(v_a_1953_) == 1)
{
lean_object* v_val_1954_; lean_object* v_snd_1955_; lean_object* v_fst_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_2201_; 
v_val_1954_ = lean_ctor_get(v_a_1953_, 0);
lean_inc(v_val_1954_);
lean_dec_ref_known(v_a_1953_, 1);
v_snd_1955_ = lean_ctor_get(v_val_1954_, 1);
v_fst_1956_ = lean_ctor_get(v_val_1954_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_val_1954_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_1958_ = v_val_1954_;
v_isShared_1959_ = v_isSharedCheck_2201_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_snd_1955_);
lean_inc(v_fst_1956_);
lean_dec(v_val_1954_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_2201_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_fst_1960_; lean_object* v_snd_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2200_; 
v_fst_1960_ = lean_ctor_get(v_snd_1955_, 0);
v_snd_1961_ = lean_ctor_get(v_snd_1955_, 1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_snd_1955_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_1963_ = v_snd_1955_;
v_isShared_1964_ = v_isSharedCheck_2200_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_snd_1961_);
lean_inc(v_fst_1960_);
lean_dec(v_snd_1955_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2200_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v_a_1966_; 
v___x_1965_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_expectedType_1918_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
if (lean_obj_tag(v_a_1966_) == 1)
{
lean_object* v_val_1967_; lean_object* v_snd_1968_; lean_object* v_fst_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2199_; 
v_val_1967_ = lean_ctor_get(v_a_1966_, 0);
lean_inc(v_val_1967_);
lean_dec_ref_known(v_a_1966_, 1);
v_snd_1968_ = lean_ctor_get(v_val_1967_, 1);
v_fst_1969_ = lean_ctor_get(v_val_1967_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_val_1967_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_1971_ = v_val_1967_;
v_isShared_1972_ = v_isSharedCheck_2199_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_snd_1968_);
lean_inc(v_fst_1969_);
lean_dec(v_val_1967_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2199_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_fst_1973_; lean_object* v_snd_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2198_; 
v_fst_1973_ = lean_ctor_get(v_snd_1968_, 0);
v_snd_1974_ = lean_ctor_get(v_snd_1968_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_snd_1968_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_1976_ = v_snd_1968_;
v_isShared_1977_ = v_isSharedCheck_2198_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_snd_1974_);
lean_inc(v_fst_1973_);
lean_dec(v_snd_1968_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2198_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1956_, v_fst_1969_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; uint8_t v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = lean_unbox(v_a_1979_);
if (v___x_1980_ == 0)
{
lean_dec(v_a_1979_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_dec(v_fst_1973_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_fst_1960_);
lean_del_object(v___x_1958_);
v___y_1931_ = v_a_1920_;
v___y_1932_ = v_a_1921_;
v___y_1933_ = v_a_1922_;
v___y_1934_ = v_a_1923_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1981_; 
lean_inc(v_fst_1973_);
lean_inc(v_fst_1960_);
v___x_1981_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1960_, v_fst_1973_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1983_; uint8_t v_failed_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; uint8_t v___x_2095_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = ((lean_object*)(l_Lean_Elab_Term_instInhabitedCalcStepView_default));
v___x_2095_ = lean_unbox(v_a_1982_);
lean_dec(v_a_1982_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_1960_, v_fst_1973_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v_fst_2098_; lean_object* v_snd_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2172_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v_fst_2098_ = lean_ctor_get(v_a_2097_, 0);
v_snd_2099_ = lean_ctor_get(v_a_2097_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_a_2097_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2101_ = v_a_2097_;
v_isShared_2102_ = v_isSharedCheck_2172_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snd_2099_);
lean_inc(v_fst_2098_);
lean_dec(v_a_2097_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2172_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; 
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
lean_inc(v_a_1921_);
lean_inc_ref(v_a_1920_);
lean_inc(v_fst_2098_);
v___x_2103_ = lean_infer_type(v_fst_2098_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
lean_inc(v_a_1921_);
lean_inc_ref(v_a_1920_);
lean_inc(v_snd_2099_);
v___x_2105_ = lean_infer_type(v_snd_2099_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2104_, v_a_2106_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2147_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v_fst_2109_ = lean_ctor_get(v_a_2108_, 0);
v_snd_2110_ = lean_ctor_get(v_a_2108_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_a_2108_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2112_ = v_a_2108_;
v_isShared_2113_ = v_isSharedCheck_2147_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snd_2110_);
lean_inc(v_fst_2109_);
lean_dec(v_a_2108_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2147_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v_term_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = lean_array_get_borrowed(v___x_1983_, v_steps_1917_, v___x_2114_);
v_term_2116_ = lean_ctor_get(v___x_2115_, 1);
v___x_2117_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_2118_ = l_Lean_MessageData_ofExpr(v_fst_2098_);
v___x_2119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 7);
lean_ctor_set(v___x_2112_, 1, v___x_2119_);
lean_ctor_set(v___x_2112_, 0, v___x_2118_);
v___x_2121_ = v___x_2112_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = l_Lean_MessageData_ofExpr(v_fst_2109_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 7);
lean_ctor_set(v___x_2101_, 1, v___x_2122_);
lean_ctor_set(v___x_2101_, 0, v___x_2121_);
v___x_2124_ = v___x_2101_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2125_ = l_Lean_indentD(v___x_2124_);
v___x_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2117_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = l_Lean_MessageData_ofExpr(v_snd_2099_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___x_2119_);
v___x_2131_ = l_Lean_MessageData_ofExpr(v_snd_2110_);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_indentD(v___x_2132_);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2128_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2116_, v___x_2134_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_2135_) == 0)
{
uint8_t v___x_2136_; 
lean_dec_ref_known(v___x_2135_, 1);
v___x_2136_ = lean_unbox(v_a_1979_);
lean_dec(v_a_1979_);
v_failed_1985_ = v___x_2136_;
v___y_1986_ = v_a_1920_;
v___y_1987_ = v_a_1921_;
v___y_1988_ = v_a_1922_;
v___y_1989_ = v_a_1923_;
goto v___jp_1984_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_a_1979_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_del_object(v___x_1958_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v_a_2137_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2135_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
lean_dec(v_fst_2098_);
lean_dec(v_a_1979_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_del_object(v___x_1958_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v_a_2148_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2107_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2107_);
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
lean_dec(v_a_2104_);
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
lean_dec(v_fst_2098_);
lean_dec(v_a_1979_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_del_object(v___x_1958_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v_a_2156_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2105_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2105_);
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
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
lean_dec(v_fst_2098_);
lean_dec(v_a_1979_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_del_object(v___x_1958_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v_a_2164_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2103_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2103_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_1979_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_del_object(v___x_1958_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v_a_2173_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2096_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2096_);
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
uint8_t v___x_2181_; 
lean_dec(v_a_1979_);
lean_dec(v_fst_1973_);
lean_dec(v_fst_1960_);
v___x_2181_ = 0;
v_failed_1985_ = v___x_2181_;
v___y_1986_ = v_a_1920_;
v___y_1987_ = v_a_1921_;
v___y_1988_ = v_a_1922_;
v___y_1989_ = v_a_1923_;
goto v___jp_1984_;
}
v___jp_1984_:
{
lean_object* v___x_1990_; 
lean_inc(v_snd_1974_);
lean_inc(v_snd_1961_);
v___x_1990_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_1961_, v_snd_1974_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; uint8_t v___x_1992_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = lean_unbox(v_a_1991_);
lean_dec(v_a_1991_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; 
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v___x_1993_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_snd_1961_, v_snd_1974_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v_fst_1995_; lean_object* v_snd_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2078_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v_fst_1995_ = lean_ctor_get(v_a_1994_, 0);
v_snd_1996_ = lean_ctor_get(v_a_1994_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_a_1994_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_1998_ = v_a_1994_;
v_isShared_1999_ = v_isSharedCheck_2078_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_snd_1996_);
lean_inc(v_fst_1995_);
lean_dec(v_a_1994_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2078_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; 
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v_fst_1995_);
v___x_2000_ = lean_infer_type(v_fst_1995_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v_snd_1996_);
v___x_2002_ = lean_infer_type(v_snd_1996_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2001_, v_a_2003_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2053_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v_fst_2006_ = lean_ctor_get(v_a_2005_, 0);
v_snd_2007_ = lean_ctor_get(v_a_2005_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_2005_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2009_ = v_a_2005_;
v_isShared_2010_ = v_isSharedCheck_2053_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snd_2007_);
lean_inc(v_fst_2006_);
lean_dec(v_a_2005_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2053_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v_term_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2011_ = lean_array_get_size(v_steps_1917_);
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_nat_sub(v___x_2011_, v___x_2012_);
v___x_2014_ = lean_array_get_borrowed(v___x_1983_, v_steps_1917_, v___x_2013_);
lean_dec(v___x_2013_);
v_term_2015_ = lean_ctor_get(v___x_2014_, 1);
v___x_2016_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5);
v___x_2017_ = l_Lean_MessageData_ofExpr(v_fst_1995_);
v___x_2018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 7);
lean_ctor_set(v___x_2009_, 1, v___x_2018_);
lean_ctor_set(v___x_2009_, 0, v___x_2017_);
v___x_2020_ = v___x_2009_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = l_Lean_MessageData_ofExpr(v_fst_2006_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 7);
lean_ctor_set(v___x_1998_, 1, v___x_2021_);
lean_ctor_set(v___x_1998_, 0, v___x_2020_);
v___x_2023_ = v___x_1998_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = l_Lean_indentD(v___x_2023_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set_tag(v___x_1976_, 7);
lean_ctor_set(v___x_1976_, 1, v___x_2024_);
lean_ctor_set(v___x_1976_, 0, v___x_2016_);
v___x_2026_ = v___x_1976_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 7);
lean_ctor_set(v___x_1971_, 1, v___x_2027_);
lean_ctor_set(v___x_1971_, 0, v___x_2026_);
v___x_2029_ = v___x_1971_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2030_ = l_Lean_MessageData_ofExpr(v_snd_1996_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set_tag(v___x_1963_, 7);
lean_ctor_set(v___x_1963_, 1, v___x_2018_);
lean_ctor_set(v___x_1963_, 0, v___x_2030_);
v___x_2032_ = v___x_1963_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2018_);
v___x_2032_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = l_Lean_MessageData_ofExpr(v_snd_2007_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 7);
lean_ctor_set(v___x_1958_, 1, v___x_2033_);
lean_ctor_set(v___x_1958_, 0, v___x_2032_);
v___x_2035_ = v___x_1958_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = l_Lean_indentD(v___x_2035_);
v___x_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2029_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2015_, v___x_2037_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_dec_ref_known(v___x_2038_, 1);
v___y_1939_ = v___y_1986_;
v___y_1940_ = v___y_1987_;
v___y_1941_ = v___y_1988_;
v___y_1942_ = v___y_1989_;
goto v___jp_1938_;
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
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
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_dec(v_fst_1995_);
lean_del_object(v___x_1976_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1958_);
v_a_2054_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2004_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2004_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_a_2001_);
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_dec(v_fst_1995_);
lean_del_object(v___x_1976_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1958_);
v_a_2062_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2002_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2002_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_dec(v_fst_1995_);
lean_del_object(v___x_1976_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1958_);
v_a_2070_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2000_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2000_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_del_object(v___x_1976_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1958_);
v_a_2079_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_1993_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_1993_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_del_object(v___x_1958_);
if (v_failed_1985_ == 0)
{
v___y_1931_ = v___y_1986_;
v___y_1932_ = v___y_1987_;
v___y_1933_ = v___y_1988_;
v___y_1934_ = v___y_1989_;
goto v___jp_1930_;
}
else
{
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v___y_1939_ = v___y_1986_;
v___y_1940_ = v___y_1987_;
v___y_1941_ = v___y_1988_;
v___y_1942_ = v___y_1989_;
goto v___jp_1938_;
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_del_object(v___x_1958_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v_a_2087_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_1990_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_1990_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_1979_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_dec(v_fst_1973_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_fst_1960_);
lean_del_object(v___x_1958_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v_a_2182_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_1981_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_1981_);
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
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_dec(v_fst_1973_);
lean_del_object(v___x_1971_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_fst_1960_);
lean_del_object(v___x_1958_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v_a_2190_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_1978_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_1978_);
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
}
}
else
{
lean_dec(v_a_1966_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_fst_1960_);
lean_del_object(v___x_1958_);
lean_dec(v_fst_1956_);
v___y_1931_ = v_a_1920_;
v___y_1932_ = v_a_1921_;
v___y_1933_ = v_a_1922_;
v___y_1934_ = v_a_1923_;
goto v___jp_1930_;
}
}
}
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec(v_a_1953_);
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v___x_2202_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9);
v___x_2203_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v___x_2202_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
return v___x_2203_;
}
v___jp_1930_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3);
v___x_1936_ = lean_box(0);
v___x_1937_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1935_, v_expectedType_1918_, v___x_1929_, v_result_1919_, v___x_1936_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
return v___x_1937_;
}
v___jp_1938_:
{
lean_object* v___x_1943_; lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v___x_1943_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref(v_result_1919_);
lean_dec_ref(v_expectedType_1918_);
v_a_2204_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_1925_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_1925_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(lean_object* v_steps_2212_, lean_object* v_expectedType_2213_, lean_object* v_result_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2212_, v_expectedType_2213_, v_result_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec_ref(v_steps_2212_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure(lean_object* v_00_u03b1_2221_, lean_object* v_steps_2222_, lean_object* v_expectedType_2223_, lean_object* v_result_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2222_, v_expectedType_2223_, v_result_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_steps_2232_, lean_object* v_expectedType_2233_, lean_object* v_result_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Elab_Term_throwCalcFailure(v_00_u03b1_2231_, v_steps_2232_, v_expectedType_2233_, v_result_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec_ref(v_steps_2232_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0(lean_object* v_a_2241_, lean_object* v_x_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2241_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0___boxed(lean_object* v_a_2251_, lean_object* v_x_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Elab_Term_elabCalc___lam__0(v_a_2251_, v_x_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v_x_2252_);
lean_dec_ref(v_a_2251_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1(lean_object* v_a_2261_, lean_object* v_x_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2261_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1___boxed(lean_object* v_a_2271_, lean_object* v_x_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Elab_Term_elabCalc___lam__1(v_a_2271_, v_x_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_x_2272_);
lean_dec_ref(v_a_2271_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object* v_x_2285_, lean_object* v_x_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
lean_inc(v_x_2285_);
v___x_2295_ = l_Lean_Syntax_isOfKind(v_x_2285_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
lean_dec(v_x_2286_);
lean_dec(v_x_2285_);
v___x_2296_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2296_;
}
else
{
lean_object* v___x_2297_; lean_object* v_steps_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2297_ = lean_unsigned_to_nat(1u);
v_steps_2298_ = l_Lean_Syntax_getArg(v_x_2285_, v___x_2297_);
v___x_2299_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_2298_);
v___x_2300_ = l_Lean_Syntax_isOfKind(v_steps_2298_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; 
lean_dec(v_steps_2298_);
lean_dec(v_x_2286_);
lean_dec(v_x_2285_);
v___x_2301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2301_;
}
else
{
lean_object* v_toCold_2302_; lean_object* v_currRecDepth_2303_; lean_object* v_ref_2304_; uint8_t v_diag_2305_; uint8_t v_suppressElabErrors_2306_; lean_object* v___x_2307_; lean_object* v_tk_2308_; lean_object* v_ref_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_toCold_2302_ = lean_ctor_get(v_a_2291_, 0);
v_currRecDepth_2303_ = lean_ctor_get(v_a_2291_, 1);
v_ref_2304_ = lean_ctor_get(v_a_2291_, 2);
v_diag_2305_ = lean_ctor_get_uint8(v_a_2291_, sizeof(void*)*3);
v_suppressElabErrors_2306_ = lean_ctor_get_uint8(v_a_2291_, sizeof(void*)*3 + 1);
v___x_2307_ = lean_unsigned_to_nat(0u);
v_tk_2308_ = l_Lean_Syntax_getArg(v_x_2285_, v___x_2307_);
lean_dec(v_x_2285_);
v_ref_2309_ = l_Lean_replaceRef(v_tk_2308_, v_ref_2304_);
lean_dec(v_tk_2308_);
lean_inc(v_currRecDepth_2303_);
lean_inc_ref(v_toCold_2302_);
v___x_2310_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2310_, 0, v_toCold_2302_);
lean_ctor_set(v___x_2310_, 1, v_currRecDepth_2303_);
lean_ctor_set(v___x_2310_, 2, v_ref_2309_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*3, v_diag_2305_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*3 + 1, v_suppressElabErrors_2306_);
v___x_2311_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_2298_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v___x_2310_, v_a_2292_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = l_Lean_Elab_Term_elabCalcSteps(v_a_2312_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v___x_2310_, v_a_2292_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v_fst_2315_; lean_object* v___f_2316_; lean_object* v___f_2317_; lean_object* v___x_2318_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v_fst_2315_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_fst_2315_);
lean_dec(v_a_2314_);
lean_inc(v_a_2312_);
v___f_2316_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2316_, 0, v_a_2312_);
v___f_2317_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__1___boxed), 9, 1);
lean_closure_set(v___f_2317_, 0, v_a_2312_);
v___x_2318_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(v_x_2286_, v_fst_2315_, v___f_2316_, v___f_2317_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v___x_2310_, v_a_2292_);
lean_dec_ref_known(v___x_2310_, 3);
return v___x_2318_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_a_2312_);
lean_dec_ref_known(v___x_2310_, 3);
lean_dec(v_x_2286_);
v_a_2319_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2313_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2313_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref_known(v___x_2310_, 3);
lean_dec(v_x_2286_);
v_a_2327_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2311_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2311_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_Elab_Term_elabCalc(v_x_2335_, v_x_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1(){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2352_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2353_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
v___x_2354_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2355_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___boxed), 9, 0);
v___x_2356_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___boxed(lean_object* v_a_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3(){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2362_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0));
v___x_2363_ = l_Lean_addBuiltinDocString(v___x_2361_, v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___boxed(lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5(){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2393_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6));
v___x_2394_ = l_Lean_addBuiltinDeclarationRanges(v___x_2392_, v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___boxed(lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
return v_res_2396_;
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
