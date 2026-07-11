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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__3 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__3_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__4 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___closed__5 = (const lean_object*)&l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value;
static const lean_string_object l_Lean_Elab_Term_mkCalcFirstStepView___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
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
lean_object* v___x_120_; lean_object* v_env_121_; lean_object* v___x_122_; lean_object* v_mctx_123_; lean_object* v_lctx_124_; lean_object* v_options_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_120_ = lean_st_ref_get(v___y_118_);
v_env_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc_ref(v_env_121_);
lean_dec(v___x_120_);
v___x_122_ = lean_st_ref_get(v___y_116_);
v_mctx_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc_ref(v_mctx_123_);
lean_dec(v___x_122_);
v_lctx_124_ = lean_ctor_get(v___y_115_, 2);
v_options_125_ = lean_ctor_get(v___y_117_, 2);
lean_inc_ref(v_options_125_);
lean_inc_ref(v_lctx_124_);
v___x_126_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_126_, 0, v_env_121_);
lean_ctor_set(v___x_126_, 1, v_mctx_123_);
lean_ctor_set(v___x_126_, 2, v_lctx_124_);
lean_ctor_set(v___x_126_, 3, v_options_125_);
v___x_127_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v_msgData_114_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0___boxed(lean_object* v_msgData_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msgData_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(lean_object* v_msg_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_ref_142_; lean_object* v___x_143_; lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_152_; 
v_ref_142_ = lean_ctor_get(v___y_139_, 5);
v___x_143_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_152_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
lean_inc(v_ref_142_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v_ref_142_);
lean_ctor_set(v___x_148_, 1, v_a_144_);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 1);
lean_ctor_set(v___x_146_, 0, v___x_148_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg___boxed(lean_object* v_msg_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_159_;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0));
v___x_162_ = l_Lean_stringToMessageData(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(lean_object* v_a_163_, lean_object* v_x_164_, lean_object* v_sort_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; 
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
v___x_171_ = lean_whnf(v_sort_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_184_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_184_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_184_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_184_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
if (lean_obj_tag(v_a_172_) == 3)
{
lean_object* v_u_176_; lean_object* v___x_178_; 
lean_dec_ref(v_a_163_);
v_u_176_ = lean_ctor_get(v_a_172_, 0);
lean_inc(v_u_176_);
lean_dec_ref_known(v_a_172_, 1);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v_u_176_);
v___x_178_ = v___x_174_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_u_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_del_object(v___x_174_);
lean_dec(v_a_172_);
v___x_180_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1);
v___x_181_ = l_Lean_indentExpr(v_a_163_);
v___x_182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_182_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
return v___x_183_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_a_163_);
v_a_185_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_171_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_171_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed(lean_object* v_a_193_, lean_object* v_x_194_, lean_object* v_sort_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(v_a_193_, v_x_194_, v_sort_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec_ref(v_x_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(lean_object* v_r_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; 
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
v___x_208_ = lean_infer_type(v_r_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___f_210_; uint8_t v___x_211_; lean_object* v___x_212_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc_n(v_a_209_, 2);
lean_dec_ref_known(v___x_208_, 1);
v___f_210_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed), 8, 1);
lean_closure_set(v___f_210_, 0, v_a_209_);
v___x_211_ = 0;
v___x_212_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_a_209_, v___f_210_, v___x_211_, v___x_211_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_212_;
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
v_a_213_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_208_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_208_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___boxed(lean_object* v_r_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_r_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(lean_object* v_00_u03b1_228_, lean_object* v_msg_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___boxed(lean_object* v_00_u03b1_236_, lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(v_00_u03b1_236_, v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(lean_object* v_e_244_, lean_object* v___y_245_){
_start:
{
uint8_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = l_Lean_Expr_hasMVar(v_e_244_);
v___x_248_ = lean_bool_not(v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v_mctx_250_; lean_object* v___x_251_; lean_object* v_fst_252_; lean_object* v_snd_253_; lean_object* v___x_254_; lean_object* v_cache_255_; lean_object* v_zetaDeltaFVarIds_256_; lean_object* v_postponed_257_; lean_object* v_diag_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_267_; 
v___x_249_ = lean_st_ref_get(v___y_245_);
v_mctx_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_mctx_250_);
lean_dec(v___x_249_);
v___x_251_ = l_Lean_instantiateMVarsCore(v_mctx_250_, v_e_244_);
v_fst_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_fst_252_);
v_snd_253_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_snd_253_);
lean_dec_ref(v___x_251_);
v___x_254_ = lean_st_ref_take(v___y_245_);
v_cache_255_ = lean_ctor_get(v___x_254_, 1);
v_zetaDeltaFVarIds_256_ = lean_ctor_get(v___x_254_, 2);
v_postponed_257_ = lean_ctor_get(v___x_254_, 3);
v_diag_258_ = lean_ctor_get(v___x_254_, 4);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_254_, 0);
lean_dec(v_unused_268_);
v___x_260_ = v___x_254_;
v_isShared_261_ = v_isSharedCheck_267_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_diag_258_);
lean_inc(v_postponed_257_);
lean_inc(v_zetaDeltaFVarIds_256_);
lean_inc(v_cache_255_);
lean_dec(v___x_254_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_267_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v_snd_253_);
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_snd_253_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_cache_255_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_zetaDeltaFVarIds_256_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_postponed_257_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v_diag_258_);
v___x_263_ = v_reuseFailAlloc_266_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_st_ref_set(v___y_245_, v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v_fst_252_);
return v___x_265_;
}
}
}
else
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v_e_244_);
return v___x_269_;
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
lean_object* v___f_295_; lean_object* v___x_7426__overap_296_; lean_object* v___x_297_; 
v___f_295_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_7426__overap_296_ = lean_panic_fn_borrowed(v___f_295_, v_msg_289_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
v___x_297_ = lean_apply_5(v___x_7426__overap_296_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, lean_box(0));
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
lean_inc_ref(v_str_720_);
lean_inc(v_pre_719_);
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
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Elab_Term_exprToSyntax(v_type_662_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_777_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_777_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_777_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_777_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_ref_749_; lean_object* v_quotContext_750_; lean_object* v_currMacroScope_751_; uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v_ref_749_ = lean_ctor_get(v_a_669_, 5);
v_quotContext_750_ = lean_ctor_get(v_a_669_, 10);
v_currMacroScope_751_ = lean_ctor_get(v_a_669_, 11);
v___x_752_ = 0;
v___x_753_ = l_Lean_SourceInfo_fromRef(v_ref_749_, v___x_752_);
v___x_754_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5));
v___x_755_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7));
v___x_756_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8));
lean_inc_n(v___x_753_, 7);
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_753_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10));
v___x_759_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12);
lean_inc(v_currMacroScope_751_);
lean_inc(v_quotContext_750_);
v___x_760_ = l_Lean_addMacroScope(v_quotContext_750_, v_pre_719_, v_currMacroScope_751_);
v___x_761_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20));
v___x_762_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_762_, 0, v___x_753_);
lean_ctor_set(v___x_762_, 1, v___x_759_);
lean_ctor_set(v___x_762_, 2, v___x_760_);
lean_ctor_set(v___x_762_, 3, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v___x_753_, v___x_758_, v___x_762_);
v___x_764_ = l_Lean_Syntax_node2(v___x_753_, v___x_755_, v___x_757_, v___x_763_);
v___x_765_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21));
v___x_766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_753_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23));
v___x_768_ = l_Lean_Syntax_node1(v___x_753_, v___x_767_, v_a_745_);
v___x_769_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24));
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_753_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = l_Lean_Syntax_node5(v___x_753_, v___x_754_, v___x_764_, v_t_663_, v___x_766_, v___x_768_, v___x_770_);
v___x_772_ = lean_box(v___x_752_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_773_);
v___x_775_ = v___x_747_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref_known(v_t_663_, 3);
v_a_778_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_744_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_744_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
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
uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref(v_type_662_);
v___x_786_ = 0;
v___x_787_ = lean_box(v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_t_663_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(lean_object* v_type_790_, size_t v_sz_791_, size_t v_i_792_, lean_object* v_bs_793_, uint8_t v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
uint8_t v___x_802_; 
v___x_802_ = lean_usize_dec_lt(v_i_792_, v_sz_791_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v_type_790_);
v___x_803_ = lean_box(v___y_794_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_bs_793_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
else
{
lean_object* v_v_806_; lean_object* v___x_807_; 
v_v_806_ = lean_array_uget_borrowed(v_bs_793_, v_i_792_);
lean_inc(v_v_806_);
lean_inc_ref(v_type_790_);
v___x_807_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_790_, v_v_806_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v_fst_809_; lean_object* v_snd_810_; lean_object* v___x_811_; lean_object* v_bs_x27_812_; size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v_fst_809_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_fst_809_);
v_snd_810_ = lean_ctor_get(v_a_808_, 1);
lean_inc(v_snd_810_);
lean_dec(v_a_808_);
v___x_811_ = lean_unsigned_to_nat(0u);
v_bs_x27_812_ = lean_array_uset(v_bs_793_, v_i_792_, v___x_811_);
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_add(v_i_792_, v___x_813_);
v___x_815_ = lean_array_uset(v_bs_x27_812_, v_i_792_, v_fst_809_);
v___x_816_ = lean_unbox(v_snd_810_);
lean_dec(v_snd_810_);
v_i_792_ = v___x_814_;
v_bs_793_ = v___x_815_;
v___y_794_ = v___x_816_;
goto _start;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref(v_bs_793_);
lean_dec_ref(v_type_790_);
v_a_818_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_807_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_807_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0___boxed(lean_object* v_type_826_, lean_object* v_sz_827_, lean_object* v_i_828_, lean_object* v_bs_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
size_t v_sz_boxed_838_; size_t v_i_boxed_839_; uint8_t v___y_7883__boxed_840_; lean_object* v_res_841_; 
v_sz_boxed_838_ = lean_unbox_usize(v_sz_827_);
lean_dec(v_sz_827_);
v_i_boxed_839_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v___y_7883__boxed_840_ = lean_unbox(v___y_830_);
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_826_, v_sz_boxed_838_, v_i_boxed_839_, v_bs_829_, v___y_7883__boxed_840_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object* v_type_842_, lean_object* v_t_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
uint8_t v_a_7952__boxed_852_; lean_object* v_res_853_; 
v_a_7952__boxed_852_ = lean_unbox(v_a_844_);
v_res_853_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_842_, v_t_843_, v_a_7952__boxed_852_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object* v_t_854_, lean_object* v_type_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
uint8_t v___x_863_; lean_object* v___x_864_; 
v___x_863_ = 1;
v___x_864_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_855_, v_t_854_, v___x_863_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_873_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_fst_869_; lean_object* v___x_871_; 
v_fst_869_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_fst_869_);
lean_dec(v_a_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v_fst_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_fst_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_864_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_864_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType___boxed(lean_object* v_t_882_, lean_object* v_type_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_t_882_, v_type_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
return v_res_891_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_box(0);
v___x_897_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg(){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0);
v___x_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___boxed(lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(lean_object* v_00_u03b1_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___boxed(lean_object* v_00_u03b1_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(v_00_u03b1_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__7));
v___x_938_ = l_String_toRawSubstring_x27(v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView(lean_object* v_step0_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_ref_955_; lean_object* v_quotContext_956_; lean_object* v_currMacroScope_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_ref_955_ = lean_ctor_get(v_a_952_, 5);
v_quotContext_956_ = lean_ctor_get(v_a_952_, 10);
v_currMacroScope_957_ = lean_ctor_get(v_a_952_, 11);
v___x_958_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_947_);
v___x_959_ = l_Lean_Syntax_isOfKind(v_step0_947_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec(v_step0_947_);
v___x_960_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v_term_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v_term_962_ = l_Lean_Syntax_getArg(v_step0_947_, v___x_961_);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = l_Lean_Syntax_getArg(v_step0_947_, v___x_963_);
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
lean_dec(v_step0_947_);
v___x_968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_968_;
}
else
{
lean_object* v_proof_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_proof_969_ = l_Lean_Syntax_getArg(v___x_964_, v___x_963_);
lean_dec(v___x_964_);
v___x_970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_970_, 0, v_step0_947_);
lean_ctor_set(v___x_970_, 1, v_term_962_);
lean_ctor_set(v___x_970_, 2, v_proof_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
else
{
lean_object* v_ref_972_; uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v___x_964_);
v_ref_972_ = l_Lean_replaceRef(v_step0_947_, v_ref_955_);
v___x_973_ = 0;
v___x_974_ = l_Lean_SourceInfo_fromRef(v_ref_972_, v___x_973_);
lean_dec(v_ref_972_);
v___x_975_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__3));
v___x_976_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__4));
lean_inc_n(v___x_974_, 4);
v___x_977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_974_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5));
v___x_979_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__6));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_974_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Lean_Syntax_node1(v___x_974_, v___x_978_, v___x_980_);
v___x_982_ = l_Lean_Syntax_node3(v___x_974_, v___x_975_, v_term_962_, v___x_977_, v___x_981_);
v___x_983_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcFirstStepView___closed__8, &l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once, _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8);
v___x_984_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__9));
lean_inc(v_currMacroScope_957_);
lean_inc(v_quotContext_956_);
v___x_985_ = l_Lean_addMacroScope(v_quotContext_956_, v___x_984_, v_currMacroScope_957_);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__11));
v___x_987_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_987_, 0, v___x_974_);
lean_ctor_set(v___x_987_, 1, v___x_983_);
lean_ctor_set(v___x_987_, 2, v___x_985_);
lean_ctor_set(v___x_987_, 3, v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_988_, 0, v_step0_947_);
lean_ctor_set(v___x_988_, 1, v___x_982_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___boxed(lean_object* v_step0_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(lean_object* v_as_1003_, size_t v_sz_1004_, size_t v_i_1005_, lean_object* v_b_1006_){
_start:
{
lean_object* v_a_1009_; uint8_t v___x_1013_; 
v___x_1013_ = lean_usize_dec_lt(v_i_1005_, v_sz_1004_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_b_1006_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v_a_1016_; uint8_t v___x_1017_; 
v___x_1015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1));
v_a_1016_ = lean_array_uget_borrowed(v_as_1003_, v_i_1005_);
lean_inc(v_a_1016_);
v___x_1017_ = l_Lean_Syntax_isOfKind(v_a_1016_, v___x_1015_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_dec_ref_known(v___x_1018_, 1);
v_a_1009_ = v_b_1006_;
goto v___jp_1008_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v_b_1006_);
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = l_Lean_Syntax_getArg(v_a_1016_, v___x_1027_);
v___x_1029_ = lean_unsigned_to_nat(2u);
v___x_1030_ = l_Lean_Syntax_getArg(v_a_1016_, v___x_1029_);
lean_inc(v_a_1016_);
v___x_1031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1031_, 0, v_a_1016_);
lean_ctor_set(v___x_1031_, 1, v___x_1028_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
v___x_1032_ = lean_array_push(v_b_1006_, v___x_1031_);
v_a_1009_ = v___x_1032_;
goto v___jp_1008_;
}
}
v___jp_1008_:
{
size_t v___x_1010_; size_t v___x_1011_; 
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_add(v_i_1005_, v___x_1010_);
v_i_1005_ = v___x_1011_;
v_b_1006_ = v_a_1009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___boxed(lean_object* v_as_1033_, lean_object* v_sz_1034_, lean_object* v_i_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_){
_start:
{
size_t v_sz_boxed_1038_; size_t v_i_boxed_1039_; lean_object* v_res_1040_; 
v_sz_boxed_1038_ = lean_unbox_usize(v_sz_1034_);
lean_dec(v_sz_1034_);
v_i_boxed_1039_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_res_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1033_, v_sz_boxed_1038_, v_i_boxed_1039_, v_b_1036_);
lean_dec_ref(v_as_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object* v_steps_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_1045_);
v___x_1054_ = l_Lean_Syntax_isOfKind(v_steps_1045_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec(v_steps_1045_);
v___x_1055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; lean_object* v_step0_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1056_ = lean_unsigned_to_nat(0u);
v_step0_1057_ = l_Lean_Syntax_getArg(v_steps_1045_, v___x_1056_);
v___x_1058_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_1057_);
v___x_1059_ = l_Lean_Syntax_isOfKind(v_step0_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_dec(v_step0_1057_);
lean_dec(v_steps_1045_);
v___x_1060_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_1057_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_rest_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; size_t v_sz_1068_; size_t v___x_1069_; lean_object* v___x_1070_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = l_Lean_Syntax_getArg(v_steps_1045_, v___x_1063_);
lean_dec(v_steps_1045_);
v_rest_1065_ = l_Lean_Syntax_getArgs(v___x_1064_);
lean_dec(v___x_1064_);
v___x_1066_ = lean_mk_empty_array_with_capacity(v___x_1063_);
v___x_1067_ = lean_array_push(v___x_1066_, v_a_1062_);
v_sz_1068_ = lean_array_size(v_rest_1065_);
v___x_1069_ = ((size_t)0ULL);
v___x_1070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_rest_1065_, v_sz_1068_, v___x_1069_, v___x_1067_);
lean_dec_ref(v_rest_1065_);
return v___x_1070_;
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v_steps_1045_);
v_a_1071_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1061_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1061_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews___boxed(lean_object* v_steps_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(lean_object* v_as_1088_, size_t v_sz_1089_, size_t v_i_1090_, lean_object* v_b_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1088_, v_sz_1089_, v_i_1090_, v_b_1091_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(lean_object* v_as_1100_, lean_object* v_sz_1101_, lean_object* v_i_1102_, lean_object* v_b_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
size_t v_sz_boxed_1111_; size_t v_i_boxed_1112_; lean_object* v_res_1113_; 
v_sz_boxed_1111_ = lean_unbox_usize(v_sz_1101_);
lean_dec(v_sz_1101_);
v_i_boxed_1112_ = lean_unbox_usize(v_i_1102_);
lean_dec(v_i_1102_);
v_res_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(v_as_1100_, v_sz_boxed_1111_, v_i_boxed_1112_, v_b_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec_ref(v_as_1100_);
return v_res_1113_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = l_Lean_instInhabitedExpr;
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(lean_object* v_msg_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_obj_once(&l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0, &l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0);
v___x_1118_ = lean_panic_fn_borrowed(v___x_1117_, v_msg_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(lean_object* v_opts_1119_, lean_object* v_opt_1120_){
_start:
{
lean_object* v_name_1121_; lean_object* v_defValue_1122_; lean_object* v_map_1123_; lean_object* v___x_1124_; 
v_name_1121_ = lean_ctor_get(v_opt_1120_, 0);
v_defValue_1122_ = lean_ctor_get(v_opt_1120_, 1);
v_map_1123_ = lean_ctor_get(v_opts_1119_, 0);
v___x_1124_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1123_, v_name_1121_);
if (lean_obj_tag(v___x_1124_) == 0)
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_unbox(v_defValue_1122_);
return v___x_1125_;
}
else
{
lean_object* v_val_1126_; 
v_val_1126_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v___x_1124_, 1);
if (lean_obj_tag(v_val_1126_) == 1)
{
uint8_t v_v_1127_; 
v_v_1127_ = lean_ctor_get_uint8(v_val_1126_, 0);
lean_dec_ref_known(v_val_1126_, 0);
return v_v_1127_;
}
else
{
uint8_t v___x_1128_; 
lean_dec(v_val_1126_);
v___x_1128_ = lean_unbox(v_defValue_1122_);
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_opts_1129_, lean_object* v_opt_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_opts_1129_, v_opt_1130_);
lean_dec_ref(v_opt_1130_);
lean_dec_ref(v_opts_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_box(1);
v___x_1134_ = l_Lean_MessageData_ofFormat(v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2));
v___x_1139_ = l_Lean_MessageData_ofFormat(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 0)
{
return v_x_1140_;
}
else
{
lean_object* v_head_1142_; lean_object* v_tail_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1165_; 
v_head_1142_ = lean_ctor_get(v_x_1141_, 0);
v_tail_1143_ = lean_ctor_get(v_x_1141_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1141_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1145_ = v_x_1141_;
v_isShared_1146_ = v_isSharedCheck_1165_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_tail_1143_);
lean_inc(v_head_1142_);
lean_dec(v_x_1141_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1165_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_before_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1163_; 
v_before_1147_ = lean_ctor_get(v_head_1142_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_head_1142_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v_head_1142_, 1);
lean_dec(v_unused_1164_);
v___x_1149_ = v_head_1142_;
v_isShared_1150_ = v_isSharedCheck_1163_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_before_1147_);
lean_dec(v_head_1142_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1163_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 7);
lean_ctor_set(v___x_1149_, 1, v___x_1151_);
lean_ctor_set(v___x_1149_, 0, v_x_1140_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_x_1140_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 7);
lean_ctor_set(v___x_1145_, 1, v___x_1154_);
lean_ctor_set(v___x_1145_, 0, v___x_1153_);
v___x_1156_ = v___x_1145_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = l_Lean_MessageData_ofSyntax(v_before_1147_);
v___x_1158_ = l_Lean_indentD(v___x_1157_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1156_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v_x_1140_ = v___x_1159_;
v_x_1141_ = v_tail_1143_;
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
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_1170_ = l_Lean_MessageData_ofFormat(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_1171_, lean_object* v_macroStack_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_options_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; uint8_t v___x_1178_; 
v_options_1175_ = lean_ctor_get(v___y_1173_, 2);
v___x_1176_ = l_Lean_Elab_pp_macroStack;
v___x_1177_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_options_1175_, v___x_1176_);
v___x_1178_ = lean_bool_not(v___x_1177_);
if (v___x_1178_ == 0)
{
if (lean_obj_tag(v_macroStack_1172_) == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_msgData_1171_);
return v___x_1179_;
}
else
{
lean_object* v_head_1180_; lean_object* v_after_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1196_; 
v_head_1180_ = lean_ctor_get(v_macroStack_1172_, 0);
lean_inc(v_head_1180_);
v_after_1181_ = lean_ctor_get(v_head_1180_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_head_1180_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v_head_1180_, 0);
lean_dec(v_unused_1197_);
v___x_1183_ = v_head_1180_;
v_isShared_1184_ = v_isSharedCheck_1196_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_after_1181_);
lean_dec(v_head_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1196_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 7);
lean_ctor_set(v___x_1183_, 1, v___x_1185_);
lean_ctor_set(v___x_1183_, 0, v_msgData_1171_);
v___x_1187_ = v___x_1183_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_msgData_1171_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_msgData_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1188_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_MessageData_ofSyntax(v_after_1181_);
v___x_1191_ = l_Lean_indentD(v___x_1190_);
v_msgData_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1192_, 0, v___x_1189_);
lean_ctor_set(v_msgData_1192_, 1, v___x_1191_);
v___x_1193_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(v_msgData_1192_, v_macroStack_1172_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
}
}
else
{
lean_object* v___x_1198_; 
lean_dec(v_macroStack_1172_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_msgData_1171_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1199_, lean_object* v_macroStack_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1199_, v_macroStack_1200_, v___y_1201_);
lean_dec_ref(v___y_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(lean_object* v_msg_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_ref_1212_; lean_object* v___x_1213_; lean_object* v_a_1214_; lean_object* v_macroStack_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
v_ref_1212_ = lean_ctor_get(v___y_1209_, 5);
v___x_1213_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_1204_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___x_1213_);
v_macroStack_1215_ = lean_ctor_get(v___y_1205_, 1);
v___x_1216_ = l_Lean_Elab_getBetterRef(v_ref_1212_, v_macroStack_1215_);
lean_inc(v_macroStack_1215_);
v___x_1217_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_a_1214_, v_macroStack_1215_, v___y_1209_);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1216_);
lean_ctor_set(v___x_1222_, 1, v_a_1218_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(lean_object* v_ref_1236_, lean_object* v_msg_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_fileName_1245_; lean_object* v_fileMap_1246_; lean_object* v_options_1247_; lean_object* v_currRecDepth_1248_; lean_object* v_maxRecDepth_1249_; lean_object* v_ref_1250_; lean_object* v_currNamespace_1251_; lean_object* v_openDecls_1252_; lean_object* v_initHeartbeats_1253_; lean_object* v_maxHeartbeats_1254_; lean_object* v_quotContext_1255_; lean_object* v_currMacroScope_1256_; uint8_t v_diag_1257_; lean_object* v_cancelTk_x3f_1258_; uint8_t v_suppressElabErrors_1259_; lean_object* v_inheritedTraceOptions_1260_; lean_object* v_ref_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_fileName_1245_ = lean_ctor_get(v___y_1242_, 0);
v_fileMap_1246_ = lean_ctor_get(v___y_1242_, 1);
v_options_1247_ = lean_ctor_get(v___y_1242_, 2);
v_currRecDepth_1248_ = lean_ctor_get(v___y_1242_, 3);
v_maxRecDepth_1249_ = lean_ctor_get(v___y_1242_, 4);
v_ref_1250_ = lean_ctor_get(v___y_1242_, 5);
v_currNamespace_1251_ = lean_ctor_get(v___y_1242_, 6);
v_openDecls_1252_ = lean_ctor_get(v___y_1242_, 7);
v_initHeartbeats_1253_ = lean_ctor_get(v___y_1242_, 8);
v_maxHeartbeats_1254_ = lean_ctor_get(v___y_1242_, 9);
v_quotContext_1255_ = lean_ctor_get(v___y_1242_, 10);
v_currMacroScope_1256_ = lean_ctor_get(v___y_1242_, 11);
v_diag_1257_ = lean_ctor_get_uint8(v___y_1242_, sizeof(void*)*14);
v_cancelTk_x3f_1258_ = lean_ctor_get(v___y_1242_, 12);
v_suppressElabErrors_1259_ = lean_ctor_get_uint8(v___y_1242_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1260_ = lean_ctor_get(v___y_1242_, 13);
v_ref_1261_ = l_Lean_replaceRef(v_ref_1236_, v_ref_1250_);
lean_inc_ref(v_inheritedTraceOptions_1260_);
lean_inc(v_cancelTk_x3f_1258_);
lean_inc(v_currMacroScope_1256_);
lean_inc(v_quotContext_1255_);
lean_inc(v_maxHeartbeats_1254_);
lean_inc(v_initHeartbeats_1253_);
lean_inc(v_openDecls_1252_);
lean_inc(v_currNamespace_1251_);
lean_inc(v_maxRecDepth_1249_);
lean_inc(v_currRecDepth_1248_);
lean_inc_ref(v_options_1247_);
lean_inc_ref(v_fileMap_1246_);
lean_inc_ref(v_fileName_1245_);
v___x_1262_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1262_, 0, v_fileName_1245_);
lean_ctor_set(v___x_1262_, 1, v_fileMap_1246_);
lean_ctor_set(v___x_1262_, 2, v_options_1247_);
lean_ctor_set(v___x_1262_, 3, v_currRecDepth_1248_);
lean_ctor_set(v___x_1262_, 4, v_maxRecDepth_1249_);
lean_ctor_set(v___x_1262_, 5, v_ref_1261_);
lean_ctor_set(v___x_1262_, 6, v_currNamespace_1251_);
lean_ctor_set(v___x_1262_, 7, v_openDecls_1252_);
lean_ctor_set(v___x_1262_, 8, v_initHeartbeats_1253_);
lean_ctor_set(v___x_1262_, 9, v_maxHeartbeats_1254_);
lean_ctor_set(v___x_1262_, 10, v_quotContext_1255_);
lean_ctor_set(v___x_1262_, 11, v_currMacroScope_1256_);
lean_ctor_set(v___x_1262_, 12, v_cancelTk_x3f_1258_);
lean_ctor_set(v___x_1262_, 13, v_inheritedTraceOptions_1260_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*14, v_diag_1257_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*14 + 1, v_suppressElabErrors_1259_);
v___x_1263_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___x_1262_, v___y_1243_);
lean_dec_ref_known(v___x_1262_, 14);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg___boxed(lean_object* v_ref_1264_, lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1264_, v_msg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v_ref_1264_);
return v_res_1273_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0));
v___x_1276_ = l_Lean_stringToMessageData(v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4));
v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(lean_object* v_as_1286_, size_t v_sz_1287_, size_t v_i_1288_, lean_object* v_b_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_a_1298_; lean_object* v___y_1303_; lean_object* v_____do__lift_1304_; uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_lt(v_i_1288_, v_sz_1287_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_b_1289_);
return v___x_1309_;
}
else
{
lean_object* v_fst_1310_; lean_object* v_snd_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1527_; 
v_fst_1310_ = lean_ctor_get(v_b_1289_, 0);
v_snd_1311_ = lean_ctor_get(v_b_1289_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_b_1289_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1313_ = v_b_1289_;
v_isShared_1314_ = v_isSharedCheck_1527_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_snd_1311_);
lean_inc(v_fst_1310_);
lean_dec(v_b_1289_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1527_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_a_1315_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v_____do__lift_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; 
v_a_1315_ = lean_array_uget_borrowed(v_as_1286_, v_i_1288_);
if (lean_obj_tag(v_snd_1311_) == 1)
{
lean_object* v_val_1504_; lean_object* v___x_1505_; 
v_val_1504_ = lean_ctor_get(v_snd_1311_, 0);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
lean_inc(v___y_1293_);
lean_inc_ref(v___y_1292_);
lean_inc(v_val_1504_);
v___x_1505_ = lean_infer_type(v_val_1504_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v_term_1507_; lean_object* v___x_1508_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v_term_1507_ = lean_ctor_get(v_a_1315_, 1);
lean_inc(v_term_1507_);
v___x_1508_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_term_1507_, v_a_1506_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v_____do__lift_1387_ = v_a_1509_;
v___y_1388_ = v___y_1290_;
v___y_1389_ = v___y_1291_;
v___y_1390_ = v___y_1292_;
v___y_1391_ = v___y_1293_;
v___y_1392_ = v___y_1294_;
v___y_1393_ = v___y_1295_;
goto v___jp_1386_;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref_known(v_snd_1311_, 1);
lean_del_object(v___x_1313_);
lean_dec(v_fst_1310_);
v_a_1510_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1508_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1508_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec_ref_known(v_snd_1311_, 1);
lean_del_object(v___x_1313_);
lean_dec(v_fst_1310_);
v_a_1518_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1505_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1505_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v_term_1526_; 
v_term_1526_ = lean_ctor_get(v_a_1315_, 1);
lean_inc(v_term_1526_);
v_____do__lift_1387_ = v_term_1526_;
v___y_1388_ = v___y_1290_;
v___y_1389_ = v___y_1291_;
v___y_1390_ = v___y_1292_;
v___y_1391_ = v___y_1293_;
v___y_1392_ = v___y_1294_;
v___y_1393_ = v___y_1295_;
goto v___jp_1386_;
}
v___jp_1316_:
{
lean_object* v_term_1325_; lean_object* v_proof_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_term_1325_ = lean_ctor_get(v_a_1315_, 1);
v_proof_1326_ = lean_ctor_get(v_a_1315_, 2);
lean_inc_ref(v___y_1318_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___y_1318_);
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_box(v___x_1308_);
v___x_1330_ = lean_box(v___x_1308_);
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v_proof_1326_);
v___x_1331_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 9);
lean_closure_set(v___x_1331_, 0, v_proof_1326_);
lean_closure_set(v___x_1331_, 1, v___x_1327_);
lean_closure_set(v___x_1331_, 2, v___x_1329_);
lean_closure_set(v___x_1331_, 3, v___x_1330_);
lean_closure_set(v___x_1331_, 4, v___x_1328_);
lean_closure_set(v___x_1331_, 5, v___y_1319_);
lean_closure_set(v___x_1331_, 6, v___y_1320_);
lean_closure_set(v___x_1331_, 7, v___y_1321_);
lean_closure_set(v___x_1331_, 8, v___y_1322_);
v___x_1332_ = l_Lean_Core_withFreshMacroScope___redArg(v___x_1331_, v___y_1323_, v___y_1324_);
if (lean_obj_tag(v___x_1332_) == 0)
{
if (lean_obj_tag(v_fst_1310_) == 1)
{
lean_object* v_val_1333_; lean_object* v_a_1334_; lean_object* v_fst_1335_; lean_object* v_snd_1336_; lean_object* v___x_1337_; 
lean_del_object(v___x_1313_);
v_val_1333_ = lean_ctor_get(v_fst_1310_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_fst_1310_, 1);
v_a_1334_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1332_, 1);
v_fst_1335_ = lean_ctor_get(v_val_1333_, 0);
lean_inc(v_fst_1335_);
v_snd_1336_ = lean_ctor_get(v_val_1333_, 1);
lean_inc(v_snd_1336_);
lean_dec(v_val_1333_);
v___x_1337_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_fileName_1338_; lean_object* v_fileMap_1339_; lean_object* v_options_1340_; lean_object* v_currRecDepth_1341_; lean_object* v_maxRecDepth_1342_; lean_object* v_ref_1343_; lean_object* v_currNamespace_1344_; lean_object* v_openDecls_1345_; lean_object* v_initHeartbeats_1346_; lean_object* v_maxHeartbeats_1347_; lean_object* v_quotContext_1348_; lean_object* v_currMacroScope_1349_; uint8_t v_diag_1350_; lean_object* v_cancelTk_x3f_1351_; uint8_t v_suppressElabErrors_1352_; lean_object* v_inheritedTraceOptions_1353_; lean_object* v_ref_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec_ref_known(v___x_1337_, 1);
v_fileName_1338_ = lean_ctor_get(v___y_1323_, 0);
v_fileMap_1339_ = lean_ctor_get(v___y_1323_, 1);
v_options_1340_ = lean_ctor_get(v___y_1323_, 2);
v_currRecDepth_1341_ = lean_ctor_get(v___y_1323_, 3);
v_maxRecDepth_1342_ = lean_ctor_get(v___y_1323_, 4);
v_ref_1343_ = lean_ctor_get(v___y_1323_, 5);
v_currNamespace_1344_ = lean_ctor_get(v___y_1323_, 6);
v_openDecls_1345_ = lean_ctor_get(v___y_1323_, 7);
v_initHeartbeats_1346_ = lean_ctor_get(v___y_1323_, 8);
v_maxHeartbeats_1347_ = lean_ctor_get(v___y_1323_, 9);
v_quotContext_1348_ = lean_ctor_get(v___y_1323_, 10);
v_currMacroScope_1349_ = lean_ctor_get(v___y_1323_, 11);
v_diag_1350_ = lean_ctor_get_uint8(v___y_1323_, sizeof(void*)*14);
v_cancelTk_x3f_1351_ = lean_ctor_get(v___y_1323_, 12);
v_suppressElabErrors_1352_ = lean_ctor_get_uint8(v___y_1323_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1353_ = lean_ctor_get(v___y_1323_, 13);
v_ref_1354_ = l_Lean_replaceRef(v_term_1325_, v_ref_1343_);
lean_inc_ref(v_inheritedTraceOptions_1353_);
lean_inc(v_cancelTk_x3f_1351_);
lean_inc(v_currMacroScope_1349_);
lean_inc(v_quotContext_1348_);
lean_inc(v_maxHeartbeats_1347_);
lean_inc(v_initHeartbeats_1346_);
lean_inc(v_openDecls_1345_);
lean_inc(v_currNamespace_1344_);
lean_inc(v_maxRecDepth_1342_);
lean_inc(v_currRecDepth_1341_);
lean_inc_ref(v_options_1340_);
lean_inc_ref(v_fileMap_1339_);
lean_inc_ref(v_fileName_1338_);
v___x_1355_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1355_, 0, v_fileName_1338_);
lean_ctor_set(v___x_1355_, 1, v_fileMap_1339_);
lean_ctor_set(v___x_1355_, 2, v_options_1340_);
lean_ctor_set(v___x_1355_, 3, v_currRecDepth_1341_);
lean_ctor_set(v___x_1355_, 4, v_maxRecDepth_1342_);
lean_ctor_set(v___x_1355_, 5, v_ref_1354_);
lean_ctor_set(v___x_1355_, 6, v_currNamespace_1344_);
lean_ctor_set(v___x_1355_, 7, v_openDecls_1345_);
lean_ctor_set(v___x_1355_, 8, v_initHeartbeats_1346_);
lean_ctor_set(v___x_1355_, 9, v_maxHeartbeats_1347_);
lean_ctor_set(v___x_1355_, 10, v_quotContext_1348_);
lean_ctor_set(v___x_1355_, 11, v_currMacroScope_1349_);
lean_ctor_set(v___x_1355_, 12, v_cancelTk_x3f_1351_);
lean_ctor_set(v___x_1355_, 13, v_inheritedTraceOptions_1353_);
lean_ctor_set_uint8(v___x_1355_, sizeof(void*)*14, v_diag_1350_);
lean_ctor_set_uint8(v___x_1355_, sizeof(void*)*14 + 1, v_suppressElabErrors_1352_);
v___x_1356_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_1335_, v_snd_1336_, v_a_1334_, v___y_1318_, v___y_1321_, v___y_1322_, v___x_1355_, v___y_1324_);
lean_dec_ref_known(v___x_1355_, 14);
lean_dec(v_snd_1336_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___y_1303_ = v___y_1317_;
v_____do__lift_1304_ = v_a_1357_;
goto v___jp_1302_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v___y_1317_);
v_a_1358_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1356_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1356_);
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
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_snd_1336_);
lean_dec(v_fst_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v___y_1317_);
v_a_1366_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1337_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1337_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; 
lean_dec(v_fst_1310_);
v_a_1374_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1332_, 1);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___y_1318_);
lean_ctor_set(v___x_1313_, 0, v_a_1374_);
v___x_1376_ = v___x_1313_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1374_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___y_1318_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
v___y_1303_ = v___y_1317_;
v_____do__lift_1304_ = v___x_1376_;
goto v___jp_1302_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_del_object(v___x_1313_);
lean_dec(v_fst_1310_);
v_a_1378_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1332_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1332_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
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
v___jp_1386_:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Elab_Term_elabType(v_____do__lift_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
if (lean_obj_tag(v_a_1397_) == 1)
{
lean_object* v_val_1398_; lean_object* v_snd_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1472_; 
v_val_1398_ = lean_ctor_get(v_a_1397_, 0);
lean_inc(v_val_1398_);
lean_dec_ref_known(v_a_1397_, 1);
v_snd_1399_ = lean_ctor_get(v_val_1398_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_val_1398_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_val_1398_, 0);
lean_dec(v_unused_1473_);
v___x_1401_ = v_val_1398_;
v_isShared_1402_ = v_isSharedCheck_1472_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_snd_1399_);
lean_dec(v_val_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1472_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
if (lean_obj_tag(v_snd_1311_) == 1)
{
lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1470_; 
v_fst_1403_ = lean_ctor_get(v_snd_1399_, 0);
v_snd_1404_ = lean_ctor_get(v_snd_1399_, 1);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_snd_1399_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1406_ = v_snd_1399_;
v_isShared_1407_ = v_isSharedCheck_1470_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_inc(v_fst_1403_);
lean_dec(v_snd_1399_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1470_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_val_1408_; lean_object* v___x_1409_; 
v_val_1408_ = lean_ctor_get(v_snd_1311_, 0);
lean_inc_n(v_val_1408_, 2);
lean_dec_ref_known(v_snd_1311_, 1);
lean_inc(v_fst_1403_);
v___x_1409_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1403_, v_val_1408_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; uint8_t v___x_1411_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1411_ = lean_unbox(v_a_1410_);
lean_dec(v_a_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
lean_inc(v_fst_1403_);
v___x_1412_ = lean_infer_type(v_fst_1403_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
lean_inc(v_val_1408_);
v___x_1414_ = lean_infer_type(v_val_1408_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v_term_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v_term_1416_ = lean_ctor_get(v_a_1315_, 1);
v___x_1417_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_1418_ = l_Lean_MessageData_ofExpr(v_fst_1403_);
v___x_1419_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 7);
lean_ctor_set(v___x_1406_, 1, v___x_1419_);
lean_ctor_set(v___x_1406_, 0, v___x_1418_);
v___x_1421_ = v___x_1406_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = l_Lean_MessageData_ofExpr(v_a_1413_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 7);
lean_ctor_set(v___x_1401_, 1, v___x_1422_);
lean_ctor_set(v___x_1401_, 0, v___x_1421_);
v___x_1424_ = v___x_1401_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1425_ = l_Lean_indentD(v___x_1424_);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1417_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l_Lean_MessageData_ofExpr(v_val_1408_);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1419_);
v___x_1431_ = l_Lean_MessageData_ofExpr(v_a_1415_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l_Lean_indentD(v___x_1432_);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1428_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1416_, v___x_1434_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
v___y_1317_ = v_snd_1404_;
v___y_1318_ = v_a_1395_;
v___y_1319_ = v___y_1388_;
v___y_1320_ = v___y_1389_;
v___y_1321_ = v___y_1390_;
v___y_1322_ = v___y_1391_;
v___y_1323_ = v___y_1392_;
v___y_1324_ = v___y_1393_;
goto v___jp_1316_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_snd_1404_);
lean_dec(v_a_1395_);
lean_del_object(v___x_1313_);
lean_dec(v_fst_1310_);
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
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_a_1413_);
lean_dec(v_val_1408_);
lean_del_object(v___x_1406_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
lean_del_object(v___x_1401_);
lean_dec(v_a_1395_);
lean_del_object(v___x_1313_);
lean_dec(v_fst_1310_);
v_a_1446_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1414_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1414_);
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
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_val_1408_);
lean_del_object(v___x_1406_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
lean_del_object(v___x_1401_);
lean_dec(v_a_1395_);
lean_del_object(v___x_1313_);
lean_dec(v_fst_1310_);
v_a_1454_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1412_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1412_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_dec(v_val_1408_);
lean_del_object(v___x_1406_);
lean_dec(v_fst_1403_);
lean_del_object(v___x_1401_);
v___y_1317_ = v_snd_1404_;
v___y_1318_ = v_a_1395_;
v___y_1319_ = v___y_1388_;
v___y_1320_ = v___y_1389_;
v___y_1321_ = v___y_1390_;
v___y_1322_ = v___y_1391_;
v___y_1323_ = v___y_1392_;
v___y_1324_ = v___y_1393_;
goto v___jp_1316_;
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v_val_1408_);
lean_del_object(v___x_1406_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
lean_del_object(v___x_1401_);
lean_dec(v_a_1395_);
lean_del_object(v___x_1313_);
lean_dec(v_fst_1310_);
v_a_1462_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1409_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1409_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
else
{
lean_object* v_snd_1471_; 
lean_del_object(v___x_1401_);
lean_dec(v_snd_1311_);
v_snd_1471_ = lean_ctor_get(v_snd_1399_, 1);
lean_inc(v_snd_1471_);
lean_dec(v_snd_1399_);
v___y_1317_ = v_snd_1471_;
v___y_1318_ = v_a_1395_;
v___y_1319_ = v___y_1388_;
v___y_1320_ = v___y_1389_;
v___y_1321_ = v___y_1390_;
v___y_1322_ = v___y_1391_;
v___y_1323_ = v___y_1392_;
v___y_1324_ = v___y_1393_;
goto v___jp_1316_;
}
}
}
else
{
lean_object* v_term_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v_a_1397_);
lean_del_object(v___x_1313_);
v_term_1474_ = lean_ctor_get(v_a_1315_, 1);
v___x_1475_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7);
v___x_1476_ = l_Lean_indentExpr(v_a_1395_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1474_, v___x_1477_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref_known(v___x_1478_, 1);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_fst_1310_);
lean_ctor_set(v___x_1479_, 1, v_snd_1311_);
v_a_1298_ = v___x_1479_;
goto v___jp_1297_;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v_snd_1311_);
lean_dec(v_fst_1310_);
v_a_1480_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1478_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1478_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_a_1395_);
lean_del_object(v___x_1313_);
lean_dec(v_snd_1311_);
lean_dec(v_fst_1310_);
v_a_1488_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1396_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1396_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_del_object(v___x_1313_);
lean_dec(v_snd_1311_);
lean_dec(v_fst_1310_);
v_a_1496_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1394_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1394_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
v___jp_1297_:
{
size_t v___x_1299_; size_t v___x_1300_; 
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1288_, v___x_1299_);
v_i_1288_ = v___x_1300_;
v_b_1289_ = v_a_1298_;
goto _start;
}
v___jp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_____do__lift_1304_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___y_1303_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v_a_1298_ = v___x_1307_;
goto v___jp_1297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___boxed(lean_object* v_as_1528_, lean_object* v_sz_1529_, lean_object* v_i_1530_, lean_object* v_b_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
size_t v_sz_boxed_1539_; size_t v_i_boxed_1540_; lean_object* v_res_1541_; 
v_sz_boxed_1539_ = lean_unbox_usize(v_sz_1529_);
lean_dec(v_sz_1529_);
v_i_boxed_1540_ = lean_unbox_usize(v_i_1530_);
lean_dec(v_i_1530_);
v_res_1541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_as_1528_, v_sz_boxed_1539_, v_i_boxed_1540_, v_b_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v_as_1528_);
return v_res_1541_;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__4(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1547_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__3));
v___x_1548_ = lean_unsigned_to_nat(14u);
v___x_1549_ = lean_unsigned_to_nat(22u);
v___x_1550_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__2));
v___x_1551_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__1));
v___x_1552_ = l_mkPanicMessageWithDecl(v___x_1551_, v___x_1550_, v___x_1549_, v___x_1548_, v___x_1547_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object* v_steps_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; size_t v_sz_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__0));
v_sz_1562_ = lean_array_size(v_steps_1553_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_steps_1553_, v_sz_1562_, v___x_1563_, v___x_1561_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1580_; 
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v___x_1566_, 0);
lean_dec(v_unused_1581_);
v___x_1568_ = v___x_1566_;
v_isShared_1569_ = v_isSharedCheck_1580_;
goto v_resetjp_1567_;
}
else
{
lean_dec(v___x_1566_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1580_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_fst_1570_; 
v_fst_1570_ = lean_ctor_get(v_a_1565_, 0);
lean_inc(v_fst_1570_);
lean_dec(v_a_1565_);
if (lean_obj_tag(v_fst_1570_) == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = lean_obj_once(&l_Lean_Elab_Term_elabCalcSteps___closed__4, &l_Lean_Elab_Term_elabCalcSteps___closed__4_once, _init_l_Lean_Elab_Term_elabCalcSteps___closed__4);
v___x_1572_ = l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(v___x_1571_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1572_);
v___x_1574_ = v___x_1568_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
else
{
lean_object* v_val_1576_; lean_object* v___x_1578_; 
v_val_1576_ = lean_ctor_get(v_fst_1570_, 0);
lean_inc(v_val_1576_);
lean_dec_ref_known(v_fst_1570_, 1);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_val_1576_);
v___x_1578_ = v___x_1568_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_val_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1565_);
v_a_1582_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1566_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1566_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_a_1590_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1564_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1564_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps___boxed(lean_object* v_steps_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Elab_Term_elabCalcSteps(v_steps_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec_ref(v_steps_1598_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(lean_object* v_00_u03b1_1607_, lean_object* v_ref_1608_, lean_object* v_msg_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1608_, v_msg_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___boxed(lean_object* v_00_u03b1_1618_, lean_object* v_ref_1619_, lean_object* v_msg_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(v_00_u03b1_1618_, v_ref_1619_, v_msg_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v_ref_1619_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(lean_object* v_00_u03b1_1629_, lean_object* v_msg_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1639_, lean_object* v_msg_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(v_00_u03b1_1639_, v_msg_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(lean_object* v_msgData_1649_, lean_object* v_macroStack_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1649_, v_macroStack_1650_, v___y_1655_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1659_, lean_object* v_macroStack_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(v_msgData_1659_, v_macroStack_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1668_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = l_Lean_Elab_abortTermExceptionId;
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg(){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___boxed(lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(lean_object* v_00_u03b1_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___boxed(lean_object* v_00_u03b1_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(v_00_u03b1_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(lean_object* v_msg_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___f_1697_; lean_object* v___x_6547__overap_1698_; lean_object* v___x_1699_; 
v___f_1697_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_6547__overap_1698_ = lean_panic_fn_borrowed(v___f_1697_, v_msg_1691_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
v___x_1699_ = lean_apply_5(v___x_6547__overap_1698_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, lean_box(0));
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg___boxed(lean_object* v_msg_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(lean_object* v_00_u03b1_1707_, lean_object* v_msg_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___boxed(lean_object* v_00_u03b1_1715_, lean_object* v_msg_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(v_00_u03b1_1715_, v_msg_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1722_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(uint8_t v___y_1730_, uint8_t v_suppressElabErrors_1731_, lean_object* v_x_1732_){
_start:
{
if (lean_obj_tag(v_x_1732_) == 1)
{
lean_object* v_pre_1733_; 
v_pre_1733_ = lean_ctor_get(v_x_1732_, 0);
switch(lean_obj_tag(v_pre_1733_))
{
case 1:
{
lean_object* v_pre_1734_; 
v_pre_1734_ = lean_ctor_get(v_pre_1733_, 0);
switch(lean_obj_tag(v_pre_1734_))
{
case 0:
{
lean_object* v_str_1735_; lean_object* v_str_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v_str_1735_ = lean_ctor_get(v_x_1732_, 1);
v_str_1736_ = lean_ctor_get(v_pre_1733_, 1);
v___x_1737_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13));
v___x_1738_ = lean_string_dec_eq(v_str_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0));
v___x_1740_ = lean_string_dec_eq(v_str_1736_, v___x_1739_);
if (v___x_1740_ == 0)
{
return v___y_1730_;
}
else
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1));
v___x_1742_ = lean_string_dec_eq(v_str_1735_, v___x_1741_);
if (v___x_1742_ == 0)
{
return v___y_1730_;
}
else
{
return v_suppressElabErrors_1731_;
}
}
}
else
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2));
v___x_1744_ = lean_string_dec_eq(v_str_1735_, v___x_1743_);
if (v___x_1744_ == 0)
{
return v___y_1730_;
}
else
{
return v_suppressElabErrors_1731_;
}
}
}
case 1:
{
lean_object* v_pre_1745_; 
v_pre_1745_ = lean_ctor_get(v_pre_1734_, 0);
if (lean_obj_tag(v_pre_1745_) == 0)
{
lean_object* v_str_1746_; lean_object* v_str_1747_; lean_object* v_str_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_str_1746_ = lean_ctor_get(v_x_1732_, 1);
v_str_1747_ = lean_ctor_get(v_pre_1733_, 1);
v_str_1748_ = lean_ctor_get(v_pre_1734_, 1);
v___x_1749_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3));
v___x_1750_ = lean_string_dec_eq(v_str_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
return v___y_1730_;
}
else
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4));
v___x_1752_ = lean_string_dec_eq(v_str_1747_, v___x_1751_);
if (v___x_1752_ == 0)
{
return v___y_1730_;
}
else
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5));
v___x_1754_ = lean_string_dec_eq(v_str_1746_, v___x_1753_);
if (v___x_1754_ == 0)
{
return v___y_1730_;
}
else
{
return v_suppressElabErrors_1731_;
}
}
}
}
else
{
return v___y_1730_;
}
}
default: 
{
return v___y_1730_;
}
}
}
case 0:
{
lean_object* v_str_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_str_1755_ = lean_ctor_get(v_x_1732_, 1);
v___x_1756_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6));
v___x_1757_ = lean_string_dec_eq(v_str_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
return v___y_1730_;
}
else
{
return v_suppressElabErrors_1731_;
}
}
default: 
{
return v___y_1730_;
}
}
}
else
{
return v___y_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed(lean_object* v___y_1758_, lean_object* v_suppressElabErrors_1759_, lean_object* v_x_1760_){
_start:
{
uint8_t v___y_8930__boxed_1761_; uint8_t v_suppressElabErrors_boxed_1762_; uint8_t v_res_1763_; lean_object* v_r_1764_; 
v___y_8930__boxed_1761_ = lean_unbox(v___y_1758_);
v_suppressElabErrors_boxed_1762_ = lean_unbox(v_suppressElabErrors_1759_);
v_res_1763_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(v___y_8930__boxed_1761_, v_suppressElabErrors_boxed_1762_, v_x_1760_);
lean_dec(v_x_1760_);
v_r_1764_ = lean_box(v_res_1763_);
return v_r_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(lean_object* v_ref_1765_, lean_object* v_msgData_1766_, uint8_t v_severity_1767_, uint8_t v_isSilent_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___y_1775_; uint8_t v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; uint8_t v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1811_; uint8_t v___y_1812_; lean_object* v___y_1813_; uint8_t v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1836_; uint8_t v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; uint8_t v___y_1840_; lean_object* v___y_1841_; uint8_t v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; uint8_t v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; uint8_t v___y_1853_; uint8_t v___x_1858_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1864_; uint8_t v___y_1865_; uint8_t v___y_1866_; uint8_t v___y_1868_; uint8_t v___x_1883_; 
v___x_1858_ = 2;
v___x_1883_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1767_, v___x_1858_);
if (v___x_1883_ == 0)
{
v___y_1868_ = v___x_1883_;
goto v___jp_1867_;
}
else
{
uint8_t v___x_1884_; 
lean_inc_ref(v_msgData_1766_);
v___x_1884_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1766_);
v___y_1868_ = v___x_1884_;
goto v___jp_1867_;
}
v___jp_1774_:
{
lean_object* v___x_1784_; lean_object* v_currNamespace_1785_; lean_object* v_openDecls_1786_; lean_object* v_env_1787_; lean_object* v_nextMacroScope_1788_; lean_object* v_ngen_1789_; lean_object* v_auxDeclNGen_1790_; lean_object* v_traceState_1791_; lean_object* v_cache_1792_; lean_object* v_messages_1793_; lean_object* v_infoState_1794_; lean_object* v_snapshotTasks_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1809_; 
v___x_1784_ = lean_st_ref_take(v___y_1783_);
v_currNamespace_1785_ = lean_ctor_get(v___y_1782_, 6);
v_openDecls_1786_ = lean_ctor_get(v___y_1782_, 7);
v_env_1787_ = lean_ctor_get(v___x_1784_, 0);
v_nextMacroScope_1788_ = lean_ctor_get(v___x_1784_, 1);
v_ngen_1789_ = lean_ctor_get(v___x_1784_, 2);
v_auxDeclNGen_1790_ = lean_ctor_get(v___x_1784_, 3);
v_traceState_1791_ = lean_ctor_get(v___x_1784_, 4);
v_cache_1792_ = lean_ctor_get(v___x_1784_, 5);
v_messages_1793_ = lean_ctor_get(v___x_1784_, 6);
v_infoState_1794_ = lean_ctor_get(v___x_1784_, 7);
v_snapshotTasks_1795_ = lean_ctor_get(v___x_1784_, 8);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1797_ = v___x_1784_;
v_isShared_1798_ = v_isSharedCheck_1809_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_snapshotTasks_1795_);
lean_inc(v_infoState_1794_);
lean_inc(v_messages_1793_);
lean_inc(v_cache_1792_);
lean_inc(v_traceState_1791_);
lean_inc(v_auxDeclNGen_1790_);
lean_inc(v_ngen_1789_);
lean_inc(v_nextMacroScope_1788_);
lean_inc(v_env_1787_);
lean_dec(v___x_1784_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1809_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_inc(v_openDecls_1786_);
lean_inc(v_currNamespace_1785_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_currNamespace_1785_);
lean_ctor_set(v___x_1799_, 1, v_openDecls_1786_);
v___x_1800_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___y_1779_);
lean_inc_ref(v___y_1775_);
lean_inc_ref(v___y_1781_);
v___x_1801_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1801_, 0, v___y_1781_);
lean_ctor_set(v___x_1801_, 1, v___y_1778_);
lean_ctor_set(v___x_1801_, 2, v___y_1777_);
lean_ctor_set(v___x_1801_, 3, v___y_1775_);
lean_ctor_set(v___x_1801_, 4, v___x_1800_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*5, v___y_1780_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*5 + 1, v___y_1776_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*5 + 2, v_isSilent_1768_);
v___x_1802_ = l_Lean_MessageLog_add(v___x_1801_, v_messages_1793_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 6, v___x_1802_);
v___x_1804_ = v___x_1797_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_env_1787_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_nextMacroScope_1788_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_ngen_1789_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_auxDeclNGen_1790_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_traceState_1791_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v_cache_1792_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v_infoState_1794_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_snapshotTasks_1795_);
v___x_1804_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_st_ref_set(v___y_1783_, v___x_1804_);
v___x_1806_ = lean_box(0);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
}
v___jp_1810_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1834_; 
v___x_1819_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1766_);
v___x_1820_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v___x_1819_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1834_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1834_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_inc_ref_n(v___y_1815_, 2);
v___x_1825_ = l_Lean_FileMap_toPosition(v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
v___x_1826_ = l_Lean_FileMap_toPosition(v___y_1815_, v___y_1818_);
lean_dec(v___y_1818_);
v___x_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
v___x_1828_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
if (v___y_1817_ == 0)
{
lean_del_object(v___x_1823_);
lean_dec_ref(v___y_1811_);
v___y_1775_ = v___x_1828_;
v___y_1776_ = v___y_1812_;
v___y_1777_ = v___x_1827_;
v___y_1778_ = v___x_1825_;
v___y_1779_ = v_a_1821_;
v___y_1780_ = v___y_1814_;
v___y_1781_ = v___y_1813_;
v___y_1782_ = v___y_1771_;
v___y_1783_ = v___y_1772_;
goto v___jp_1774_;
}
else
{
uint8_t v___x_1829_; 
lean_inc(v_a_1821_);
v___x_1829_ = l_Lean_MessageData_hasTag(v___y_1811_, v_a_1821_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
lean_dec_ref_known(v___x_1827_, 1);
lean_dec_ref(v___x_1825_);
lean_dec(v_a_1821_);
v___x_1830_ = lean_box(0);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1830_);
v___x_1832_ = v___x_1823_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
else
{
lean_del_object(v___x_1823_);
v___y_1775_ = v___x_1828_;
v___y_1776_ = v___y_1812_;
v___y_1777_ = v___x_1827_;
v___y_1778_ = v___x_1825_;
v___y_1779_ = v_a_1821_;
v___y_1780_ = v___y_1814_;
v___y_1781_ = v___y_1813_;
v___y_1782_ = v___y_1771_;
v___y_1783_ = v___y_1772_;
goto v___jp_1774_;
}
}
}
}
v___jp_1835_:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_Syntax_getTailPos_x3f(v___y_1838_, v___y_1840_);
lean_dec(v___y_1838_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_inc(v___y_1843_);
v___y_1811_ = v___y_1836_;
v___y_1812_ = v___y_1837_;
v___y_1813_ = v___y_1841_;
v___y_1814_ = v___y_1840_;
v___y_1815_ = v___y_1839_;
v___y_1816_ = v___y_1843_;
v___y_1817_ = v___y_1842_;
v___y_1818_ = v___y_1843_;
goto v___jp_1810_;
}
else
{
lean_object* v_val_1845_; 
v_val_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_val_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___y_1811_ = v___y_1836_;
v___y_1812_ = v___y_1837_;
v___y_1813_ = v___y_1841_;
v___y_1814_ = v___y_1840_;
v___y_1815_ = v___y_1839_;
v___y_1816_ = v___y_1843_;
v___y_1817_ = v___y_1842_;
v___y_1818_ = v_val_1845_;
goto v___jp_1810_;
}
}
v___jp_1846_:
{
lean_object* v_ref_1854_; lean_object* v___x_1855_; 
v_ref_1854_ = l_Lean_replaceRef(v_ref_1765_, v___y_1848_);
v___x_1855_ = l_Lean_Syntax_getPos_x3f(v_ref_1854_, v___y_1850_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_unsigned_to_nat(0u);
v___y_1836_ = v___y_1847_;
v___y_1837_ = v___y_1853_;
v___y_1838_ = v_ref_1854_;
v___y_1839_ = v___y_1851_;
v___y_1840_ = v___y_1850_;
v___y_1841_ = v___y_1849_;
v___y_1842_ = v___y_1852_;
v___y_1843_ = v___x_1856_;
goto v___jp_1835_;
}
else
{
lean_object* v_val_1857_; 
v_val_1857_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_val_1857_);
lean_dec_ref_known(v___x_1855_, 1);
v___y_1836_ = v___y_1847_;
v___y_1837_ = v___y_1853_;
v___y_1838_ = v_ref_1854_;
v___y_1839_ = v___y_1851_;
v___y_1840_ = v___y_1850_;
v___y_1841_ = v___y_1849_;
v___y_1842_ = v___y_1852_;
v___y_1843_ = v_val_1857_;
goto v___jp_1835_;
}
}
v___jp_1859_:
{
if (v___y_1866_ == 0)
{
v___y_1847_ = v___y_1860_;
v___y_1848_ = v___y_1861_;
v___y_1849_ = v___y_1863_;
v___y_1850_ = v___y_1865_;
v___y_1851_ = v___y_1862_;
v___y_1852_ = v___y_1864_;
v___y_1853_ = v_severity_1767_;
goto v___jp_1846_;
}
else
{
v___y_1847_ = v___y_1860_;
v___y_1848_ = v___y_1861_;
v___y_1849_ = v___y_1863_;
v___y_1850_ = v___y_1865_;
v___y_1851_ = v___y_1862_;
v___y_1852_ = v___y_1864_;
v___y_1853_ = v___x_1858_;
goto v___jp_1846_;
}
}
v___jp_1867_:
{
if (v___y_1868_ == 0)
{
lean_object* v_fileName_1869_; lean_object* v_fileMap_1870_; lean_object* v_options_1871_; lean_object* v_ref_1872_; uint8_t v_suppressElabErrors_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___f_1876_; uint8_t v___x_1877_; uint8_t v___x_1878_; 
v_fileName_1869_ = lean_ctor_get(v___y_1771_, 0);
v_fileMap_1870_ = lean_ctor_get(v___y_1771_, 1);
v_options_1871_ = lean_ctor_get(v___y_1771_, 2);
v_ref_1872_ = lean_ctor_get(v___y_1771_, 5);
v_suppressElabErrors_1873_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*14 + 1);
v___x_1874_ = lean_box(v___y_1868_);
v___x_1875_ = lean_box(v_suppressElabErrors_1873_);
v___f_1876_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1876_, 0, v___x_1874_);
lean_closure_set(v___f_1876_, 1, v___x_1875_);
v___x_1877_ = 1;
v___x_1878_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1767_, v___x_1877_);
if (v___x_1878_ == 0)
{
v___y_1860_ = v___f_1876_;
v___y_1861_ = v_ref_1872_;
v___y_1862_ = v_fileMap_1870_;
v___y_1863_ = v_fileName_1869_;
v___y_1864_ = v_suppressElabErrors_1873_;
v___y_1865_ = v___y_1868_;
v___y_1866_ = v___x_1878_;
goto v___jp_1859_;
}
else
{
lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1879_ = l_Lean_warningAsError;
v___x_1880_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_options_1871_, v___x_1879_);
v___y_1860_ = v___f_1876_;
v___y_1861_ = v_ref_1872_;
v___y_1862_ = v_fileMap_1870_;
v___y_1863_ = v_fileName_1869_;
v___y_1864_ = v_suppressElabErrors_1873_;
v___y_1865_ = v___y_1868_;
v___y_1866_ = v___x_1880_;
goto v___jp_1859_;
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec_ref(v_msgData_1766_);
v___x_1881_ = lean_box(0);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___boxed(lean_object* v_ref_1885_, lean_object* v_msgData_1886_, lean_object* v_severity_1887_, lean_object* v_isSilent_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v_severity_boxed_1894_; uint8_t v_isSilent_boxed_1895_; lean_object* v_res_1896_; 
v_severity_boxed_1894_ = lean_unbox(v_severity_1887_);
v_isSilent_boxed_1895_ = lean_unbox(v_isSilent_1888_);
v_res_1896_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1885_, v_msgData_1886_, v_severity_boxed_1894_, v_isSilent_boxed_1895_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v_ref_1885_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(lean_object* v_ref_1897_, lean_object* v_msgData_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
uint8_t v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = 2;
v___x_1905_ = 0;
v___x_1906_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1897_, v_msgData_1898_, v___x_1904_, v___x_1905_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1___boxed(lean_object* v_ref_1907_, lean_object* v_msgData_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_ref_1907_, v_msgData_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v_ref_1907_);
return v_res_1914_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1));
v___x_1919_ = l_Lean_MessageData_ofFormat(v___x_1918_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2);
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4));
v___x_1924_ = l_Lean_stringToMessageData(v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6));
v___x_1927_ = l_Lean_stringToMessageData(v___x_1926_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1929_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_1930_ = lean_unsigned_to_nat(57u);
v___x_1931_ = lean_unsigned_to_nat(133u);
v___x_1932_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8));
v___x_1933_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_1934_ = l_mkPanicMessageWithDecl(v___x_1933_, v___x_1932_, v___x_1931_, v___x_1930_, v___x_1929_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object* v_steps_1935_, lean_object* v_expectedType_1936_, lean_object* v_result_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v___x_1943_; 
lean_inc(v_a_1941_);
lean_inc_ref(v_a_1940_);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc_ref(v_result_1937_);
v___x_1943_ = lean_infer_type(v_result_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; lean_object* v_a_1946_; lean_object* v___x_1947_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___x_1970_; lean_object* v_a_1971_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1945_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_1944_, v_a_1939_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
v___x_1947_ = l_Lean_Expr_headBeta(v_a_1946_);
v___x_1970_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_1947_);
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1970_);
if (lean_obj_tag(v_a_1971_) == 1)
{
lean_object* v_val_1972_; lean_object* v_snd_1973_; lean_object* v_fst_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2220_; 
v_val_1972_ = lean_ctor_get(v_a_1971_, 0);
lean_inc(v_val_1972_);
lean_dec_ref_known(v_a_1971_, 1);
v_snd_1973_ = lean_ctor_get(v_val_1972_, 1);
v_fst_1974_ = lean_ctor_get(v_val_1972_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_val_1972_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_1976_ = v_val_1972_;
v_isShared_1977_ = v_isSharedCheck_2220_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_snd_1973_);
lean_inc(v_fst_1974_);
lean_dec(v_val_1972_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2220_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_fst_1978_; lean_object* v_snd_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2219_; 
v_fst_1978_ = lean_ctor_get(v_snd_1973_, 0);
v_snd_1979_ = lean_ctor_get(v_snd_1973_, 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_snd_1973_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_1981_ = v_snd_1973_;
v_isShared_1982_ = v_isSharedCheck_2219_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snd_1979_);
lean_inc(v_fst_1978_);
lean_dec(v_snd_1973_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2219_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v_a_1984_; 
v___x_1983_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_expectedType_1936_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref(v___x_1983_);
if (lean_obj_tag(v_a_1984_) == 1)
{
lean_object* v_val_1985_; lean_object* v_snd_1986_; lean_object* v_fst_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2218_; 
v_val_1985_ = lean_ctor_get(v_a_1984_, 0);
lean_inc(v_val_1985_);
lean_dec_ref_known(v_a_1984_, 1);
v_snd_1986_ = lean_ctor_get(v_val_1985_, 1);
v_fst_1987_ = lean_ctor_get(v_val_1985_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_val_1985_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_1989_ = v_val_1985_;
v_isShared_1990_ = v_isSharedCheck_2218_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_snd_1986_);
lean_inc(v_fst_1987_);
lean_dec(v_val_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2218_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v_fst_1991_; lean_object* v_snd_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2217_; 
v_fst_1991_ = lean_ctor_get(v_snd_1986_, 0);
v_snd_1992_ = lean_ctor_get(v_snd_1986_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_snd_1986_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_1994_ = v_snd_1986_;
v_isShared_1995_ = v_isSharedCheck_2217_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_snd_1992_);
lean_inc(v_fst_1991_);
lean_dec(v_snd_1986_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2217_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
uint8_t v_failed_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1974_, v_fst_1987_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; uint8_t v___x_2110_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = lean_unbox(v_a_2109_);
if (v___x_2110_ == 0)
{
lean_dec(v_a_2109_);
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_dec(v_fst_1991_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_dec(v_fst_1978_);
lean_del_object(v___x_1976_);
v___y_1949_ = v_a_1938_;
v___y_1950_ = v_a_1939_;
v___y_1951_ = v_a_1940_;
v___y_1952_ = v_a_1941_;
goto v___jp_1948_;
}
else
{
lean_object* v___x_2111_; 
lean_inc(v_fst_1991_);
lean_inc(v_fst_1978_);
v___x_2111_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1978_, v_fst_1991_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; uint8_t v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = lean_unbox(v_a_2112_);
lean_dec(v_a_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_1978_, v_fst_1991_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v_fst_2116_; lean_object* v_snd_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2191_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v_fst_2116_ = lean_ctor_get(v_a_2115_, 0);
v_snd_2117_ = lean_ctor_get(v_a_2115_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_a_2115_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2119_ = v_a_2115_;
v_isShared_2120_ = v_isSharedCheck_2191_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_snd_2117_);
lean_inc(v_fst_2116_);
lean_dec(v_a_2115_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2191_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; 
lean_inc(v_a_1941_);
lean_inc_ref(v_a_1940_);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_fst_2116_);
v___x_2121_ = lean_infer_type(v_fst_2116_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
lean_inc(v_a_1941_);
lean_inc_ref(v_a_1940_);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_snd_2117_);
v___x_2123_ = lean_infer_type(v_snd_2117_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2122_, v_a_2124_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v_fst_2127_; lean_object* v_snd_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2166_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v_fst_2127_ = lean_ctor_get(v_a_2126_, 0);
v_snd_2128_ = lean_ctor_get(v_a_2126_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2130_ = v_a_2126_;
v_isShared_2131_ = v_isSharedCheck_2166_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_snd_2128_);
lean_inc(v_fst_2127_);
lean_dec(v_a_2126_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2166_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v_term_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2132_ = ((lean_object*)(l_Lean_Elab_Term_instInhabitedCalcStepView_default));
v___x_2133_ = lean_unsigned_to_nat(0u);
v___x_2134_ = lean_array_get_borrowed(v___x_2132_, v_steps_1935_, v___x_2133_);
v_term_2135_ = lean_ctor_get(v___x_2134_, 1);
v___x_2136_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_2137_ = l_Lean_MessageData_ofExpr(v_fst_2116_);
v___x_2138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2131_ == 0)
{
lean_ctor_set_tag(v___x_2130_, 7);
lean_ctor_set(v___x_2130_, 1, v___x_2138_);
lean_ctor_set(v___x_2130_, 0, v___x_2137_);
v___x_2140_ = v___x_2130_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = l_Lean_MessageData_ofExpr(v_fst_2127_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set_tag(v___x_2119_, 7);
lean_ctor_set(v___x_2119_, 1, v___x_2141_);
lean_ctor_set(v___x_2119_, 0, v___x_2140_);
v___x_2143_ = v___x_2119_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2144_ = l_Lean_indentD(v___x_2143_);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2136_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_MessageData_ofExpr(v_snd_2117_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
lean_ctor_set(v___x_2149_, 1, v___x_2138_);
v___x_2150_ = l_Lean_MessageData_ofExpr(v_snd_2128_);
v___x_2151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_Lean_indentD(v___x_2151_);
v___x_2153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2147_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2135_, v___x_2153_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_2154_) == 0)
{
uint8_t v___x_2155_; 
lean_dec_ref_known(v___x_2154_, 1);
v___x_2155_ = lean_unbox(v_a_2109_);
lean_dec(v_a_2109_);
v_failed_1997_ = v___x_2155_;
v___y_1998_ = v_a_1938_;
v___y_1999_ = v_a_1939_;
v___y_2000_ = v_a_1940_;
v___y_2001_ = v_a_1941_;
goto v___jp_1996_;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_a_2109_);
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_del_object(v___x_1976_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v_a_2156_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2154_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2154_);
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
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_del_object(v___x_2119_);
lean_dec(v_snd_2117_);
lean_dec(v_fst_2116_);
lean_dec(v_a_2109_);
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_del_object(v___x_1976_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v_a_2167_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2125_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2125_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_a_2122_);
lean_del_object(v___x_2119_);
lean_dec(v_snd_2117_);
lean_dec(v_fst_2116_);
lean_dec(v_a_2109_);
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_del_object(v___x_1976_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v_a_2175_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2123_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2123_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2119_);
lean_dec(v_snd_2117_);
lean_dec(v_fst_2116_);
lean_dec(v_a_2109_);
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_del_object(v___x_1976_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v_a_2183_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2121_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2121_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_a_2109_);
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_del_object(v___x_1976_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v_a_2192_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2114_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2114_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
uint8_t v___x_2200_; 
lean_dec(v_a_2109_);
lean_dec(v_fst_1991_);
lean_dec(v_fst_1978_);
v___x_2200_ = 0;
v_failed_1997_ = v___x_2200_;
v___y_1998_ = v_a_1938_;
v___y_1999_ = v_a_1939_;
v___y_2000_ = v_a_1940_;
v___y_2001_ = v_a_1941_;
goto v___jp_1996_;
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_a_2109_);
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_dec(v_fst_1991_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_dec(v_fst_1978_);
lean_del_object(v___x_1976_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v_a_2201_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2111_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2111_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_dec(v_fst_1991_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_dec(v_fst_1978_);
lean_del_object(v___x_1976_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v_a_2209_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2108_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2108_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
v___jp_1996_:
{
lean_object* v___x_2002_; 
lean_inc(v_snd_1992_);
lean_inc(v_snd_1979_);
v___x_2002_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_1979_, v_snd_1992_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; uint8_t v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = lean_unbox(v_a_2003_);
lean_dec(v_a_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v___x_2005_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_snd_1979_, v_snd_1992_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2091_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2005_, 1);
v_fst_2007_ = lean_ctor_get(v_a_2006_, 0);
v_snd_2008_ = lean_ctor_get(v_a_2006_, 1);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_a_2006_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2010_ = v_a_2006_;
v_isShared_2011_ = v_isSharedCheck_2091_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_a_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2091_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; 
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
lean_inc(v_fst_2007_);
v___x_2012_ = lean_infer_type(v_fst_2007_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
lean_inc(v_snd_2008_);
v___x_2014_ = lean_infer_type(v_snd_2008_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2013_, v_a_2015_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v_fst_2018_; lean_object* v_snd_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2066_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v_fst_2018_ = lean_ctor_get(v_a_2017_, 0);
v_snd_2019_ = lean_ctor_get(v_a_2017_, 1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_a_2017_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2021_ = v_a_2017_;
v_isShared_2022_ = v_isSharedCheck_2066_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_snd_2019_);
lean_inc(v_fst_2018_);
lean_dec(v_a_2017_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2066_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v_term_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2023_ = ((lean_object*)(l_Lean_Elab_Term_instInhabitedCalcStepView_default));
v___x_2024_ = lean_array_get_size(v_steps_1935_);
v___x_2025_ = lean_unsigned_to_nat(1u);
v___x_2026_ = lean_nat_sub(v___x_2024_, v___x_2025_);
v___x_2027_ = lean_array_get_borrowed(v___x_2023_, v_steps_1935_, v___x_2026_);
lean_dec(v___x_2026_);
v_term_2028_ = lean_ctor_get(v___x_2027_, 1);
v___x_2029_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5);
v___x_2030_ = l_Lean_MessageData_ofExpr(v_fst_2007_);
v___x_2031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2022_ == 0)
{
lean_ctor_set_tag(v___x_2021_, 7);
lean_ctor_set(v___x_2021_, 1, v___x_2031_);
lean_ctor_set(v___x_2021_, 0, v___x_2030_);
v___x_2033_ = v___x_2021_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = l_Lean_MessageData_ofExpr(v_fst_2018_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 7);
lean_ctor_set(v___x_2010_, 1, v___x_2034_);
lean_ctor_set(v___x_2010_, 0, v___x_2033_);
v___x_2036_ = v___x_2010_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = l_Lean_indentD(v___x_2036_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 7);
lean_ctor_set(v___x_1994_, 1, v___x_2037_);
lean_ctor_set(v___x_1994_, 0, v___x_2029_);
v___x_2039_ = v___x_1994_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
if (v_isShared_1990_ == 0)
{
lean_ctor_set_tag(v___x_1989_, 7);
lean_ctor_set(v___x_1989_, 1, v___x_2040_);
lean_ctor_set(v___x_1989_, 0, v___x_2039_);
v___x_2042_ = v___x_1989_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = l_Lean_MessageData_ofExpr(v_snd_2008_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 7);
lean_ctor_set(v___x_1981_, 1, v___x_2031_);
lean_ctor_set(v___x_1981_, 0, v___x_2043_);
v___x_2045_ = v___x_1981_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2031_);
v___x_2045_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = l_Lean_MessageData_ofExpr(v_snd_2019_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set_tag(v___x_1976_, 7);
lean_ctor_set(v___x_1976_, 1, v___x_2046_);
lean_ctor_set(v___x_1976_, 0, v___x_2045_);
v___x_2048_ = v___x_1976_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = l_Lean_indentD(v___x_2048_);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2042_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2028_, v___x_2050_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_dec_ref_known(v___x_2051_, 1);
v___y_1957_ = v___y_1998_;
v___y_1958_ = v___y_1999_;
v___y_1959_ = v___y_2000_;
v___y_1960_ = v___y_2001_;
goto v___jp_1956_;
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
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
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_dec(v_fst_2007_);
lean_del_object(v___x_1994_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_del_object(v___x_1976_);
v_a_2067_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2016_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2016_);
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
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_2013_);
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_dec(v_fst_2007_);
lean_del_object(v___x_1994_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_del_object(v___x_1976_);
v_a_2075_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2014_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2014_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_del_object(v___x_2010_);
lean_dec(v_snd_2008_);
lean_dec(v_fst_2007_);
lean_del_object(v___x_1994_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_del_object(v___x_1976_);
v_a_2083_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2012_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2012_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_del_object(v___x_1994_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_del_object(v___x_1976_);
v_a_2092_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2005_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2005_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_del_object(v___x_1976_);
if (v_failed_1997_ == 0)
{
v___y_1949_ = v___y_1998_;
v___y_1950_ = v___y_1999_;
v___y_1951_ = v___y_2000_;
v___y_1952_ = v___y_2001_;
goto v___jp_1948_;
}
else
{
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v___y_1957_ = v___y_1998_;
v___y_1958_ = v___y_1999_;
v___y_1959_ = v___y_2000_;
v___y_1960_ = v___y_2001_;
goto v___jp_1956_;
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_del_object(v___x_1994_);
lean_dec(v_snd_1992_);
lean_del_object(v___x_1989_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_del_object(v___x_1976_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v_a_2100_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2002_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2002_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1984_);
lean_del_object(v___x_1981_);
lean_dec(v_snd_1979_);
lean_dec(v_fst_1978_);
lean_del_object(v___x_1976_);
lean_dec(v_fst_1974_);
v___y_1949_ = v_a_1938_;
v___y_1950_ = v_a_1939_;
v___y_1951_ = v_a_1940_;
v___y_1952_ = v_a_1941_;
goto v___jp_1948_;
}
}
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec(v_a_1971_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v___x_2221_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9);
v___x_2222_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v___x_2221_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
return v___x_2222_;
}
v___jp_1948_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3);
v___x_1954_ = lean_box(0);
v___x_1955_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1953_, v_expectedType_1936_, v___x_1947_, v_result_1937_, v___x_1954_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
return v___x_1955_;
}
v___jp_1956_:
{
lean_object* v___x_1961_; lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
v___x_1961_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_result_1937_);
lean_dec_ref(v_expectedType_1936_);
v_a_2223_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_1943_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_1943_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(lean_object* v_steps_2231_, lean_object* v_expectedType_2232_, lean_object* v_result_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2231_, v_expectedType_2232_, v_result_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec_ref(v_steps_2231_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure(lean_object* v_00_u03b1_2240_, lean_object* v_steps_2241_, lean_object* v_expectedType_2242_, lean_object* v_result_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2241_, v_expectedType_2242_, v_result_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___boxed(lean_object* v_00_u03b1_2250_, lean_object* v_steps_2251_, lean_object* v_expectedType_2252_, lean_object* v_result_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Elab_Term_throwCalcFailure(v_00_u03b1_2250_, v_steps_2251_, v_expectedType_2252_, v_result_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec_ref(v_steps_2251_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0(lean_object* v_a_2260_, lean_object* v_x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2260_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0___boxed(lean_object* v_a_2270_, lean_object* v_x_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_Elab_Term_elabCalc___lam__0(v_a_2270_, v_x_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v_x_2271_);
lean_dec_ref(v_a_2270_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1(lean_object* v_a_2280_, lean_object* v_x_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2280_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1___boxed(lean_object* v_a_2290_, lean_object* v_x_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Elab_Term_elabCalc___lam__1(v_a_2290_, v_x_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v_x_2291_);
lean_dec_ref(v_a_2290_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object* v_x_2304_, lean_object* v_x_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
lean_inc(v_x_2304_);
v___x_2314_ = l_Lean_Syntax_isOfKind(v_x_2304_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; 
lean_dec(v_x_2305_);
lean_dec(v_x_2304_);
v___x_2315_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2315_;
}
else
{
lean_object* v___x_2316_; lean_object* v_steps_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2316_ = lean_unsigned_to_nat(1u);
v_steps_2317_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2316_);
v___x_2318_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_2317_);
v___x_2319_ = l_Lean_Syntax_isOfKind(v_steps_2317_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; 
lean_dec(v_steps_2317_);
lean_dec(v_x_2305_);
lean_dec(v_x_2304_);
v___x_2320_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2320_;
}
else
{
lean_object* v_fileName_2321_; lean_object* v_fileMap_2322_; lean_object* v_options_2323_; lean_object* v_currRecDepth_2324_; lean_object* v_maxRecDepth_2325_; lean_object* v_ref_2326_; lean_object* v_currNamespace_2327_; lean_object* v_openDecls_2328_; lean_object* v_initHeartbeats_2329_; lean_object* v_maxHeartbeats_2330_; lean_object* v_quotContext_2331_; lean_object* v_currMacroScope_2332_; uint8_t v_diag_2333_; lean_object* v_cancelTk_x3f_2334_; uint8_t v_suppressElabErrors_2335_; lean_object* v_inheritedTraceOptions_2336_; lean_object* v___x_2337_; lean_object* v_tk_2338_; lean_object* v_ref_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_fileName_2321_ = lean_ctor_get(v_a_2310_, 0);
v_fileMap_2322_ = lean_ctor_get(v_a_2310_, 1);
v_options_2323_ = lean_ctor_get(v_a_2310_, 2);
v_currRecDepth_2324_ = lean_ctor_get(v_a_2310_, 3);
v_maxRecDepth_2325_ = lean_ctor_get(v_a_2310_, 4);
v_ref_2326_ = lean_ctor_get(v_a_2310_, 5);
v_currNamespace_2327_ = lean_ctor_get(v_a_2310_, 6);
v_openDecls_2328_ = lean_ctor_get(v_a_2310_, 7);
v_initHeartbeats_2329_ = lean_ctor_get(v_a_2310_, 8);
v_maxHeartbeats_2330_ = lean_ctor_get(v_a_2310_, 9);
v_quotContext_2331_ = lean_ctor_get(v_a_2310_, 10);
v_currMacroScope_2332_ = lean_ctor_get(v_a_2310_, 11);
v_diag_2333_ = lean_ctor_get_uint8(v_a_2310_, sizeof(void*)*14);
v_cancelTk_x3f_2334_ = lean_ctor_get(v_a_2310_, 12);
v_suppressElabErrors_2335_ = lean_ctor_get_uint8(v_a_2310_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2336_ = lean_ctor_get(v_a_2310_, 13);
v___x_2337_ = lean_unsigned_to_nat(0u);
v_tk_2338_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2337_);
lean_dec(v_x_2304_);
v_ref_2339_ = l_Lean_replaceRef(v_tk_2338_, v_ref_2326_);
lean_dec(v_tk_2338_);
lean_inc_ref(v_inheritedTraceOptions_2336_);
lean_inc(v_cancelTk_x3f_2334_);
lean_inc(v_currMacroScope_2332_);
lean_inc(v_quotContext_2331_);
lean_inc(v_maxHeartbeats_2330_);
lean_inc(v_initHeartbeats_2329_);
lean_inc(v_openDecls_2328_);
lean_inc(v_currNamespace_2327_);
lean_inc(v_maxRecDepth_2325_);
lean_inc(v_currRecDepth_2324_);
lean_inc_ref(v_options_2323_);
lean_inc_ref(v_fileMap_2322_);
lean_inc_ref(v_fileName_2321_);
v___x_2340_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2340_, 0, v_fileName_2321_);
lean_ctor_set(v___x_2340_, 1, v_fileMap_2322_);
lean_ctor_set(v___x_2340_, 2, v_options_2323_);
lean_ctor_set(v___x_2340_, 3, v_currRecDepth_2324_);
lean_ctor_set(v___x_2340_, 4, v_maxRecDepth_2325_);
lean_ctor_set(v___x_2340_, 5, v_ref_2339_);
lean_ctor_set(v___x_2340_, 6, v_currNamespace_2327_);
lean_ctor_set(v___x_2340_, 7, v_openDecls_2328_);
lean_ctor_set(v___x_2340_, 8, v_initHeartbeats_2329_);
lean_ctor_set(v___x_2340_, 9, v_maxHeartbeats_2330_);
lean_ctor_set(v___x_2340_, 10, v_quotContext_2331_);
lean_ctor_set(v___x_2340_, 11, v_currMacroScope_2332_);
lean_ctor_set(v___x_2340_, 12, v_cancelTk_x3f_2334_);
lean_ctor_set(v___x_2340_, 13, v_inheritedTraceOptions_2336_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*14, v_diag_2333_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*14 + 1, v_suppressElabErrors_2335_);
v___x_2341_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_2317_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v___x_2340_, v_a_2311_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = l_Lean_Elab_Term_elabCalcSteps(v_a_2342_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v___x_2340_, v_a_2311_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v_fst_2345_; lean_object* v___f_2346_; lean_object* v___f_2347_; lean_object* v___x_2348_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v_fst_2345_ = lean_ctor_get(v_a_2344_, 0);
lean_inc(v_fst_2345_);
lean_dec(v_a_2344_);
lean_inc(v_a_2342_);
v___f_2346_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2346_, 0, v_a_2342_);
v___f_2347_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__1___boxed), 9, 1);
lean_closure_set(v___f_2347_, 0, v_a_2342_);
v___x_2348_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(v_x_2305_, v_fst_2345_, v___f_2346_, v___f_2347_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v___x_2340_, v_a_2311_);
lean_dec_ref_known(v___x_2340_, 14);
return v___x_2348_;
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2342_);
lean_dec_ref_known(v___x_2340_, 14);
lean_dec(v_x_2305_);
v_a_2349_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2343_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2343_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref_known(v___x_2340_, 14);
lean_dec(v_x_2305_);
v_a_2357_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2341_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2341_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object* v_x_2365_, lean_object* v_x_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_Elab_Term_elabCalc(v_x_2365_, v_x_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1(){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2382_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2383_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
v___x_2384_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2385_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___boxed), 9, 0);
v___x_2386_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2382_, v___x_2383_, v___x_2384_, v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___boxed(lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3(){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2392_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0));
v___x_2393_ = l_Lean_addBuiltinDocString(v___x_2391_, v___x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___boxed(lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5(){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2423_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6));
v___x_2424_ = l_Lean_addBuiltinDeclarationRanges(v___x_2422_, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___boxed(lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
return v_res_2426_;
}
}
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Calc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
