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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabCalc"};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 61, 75, 63, 20, 229, 120, 81)}};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Elaborator for the `calc` term mode variant. "};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(116) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(121) << 1) | 1)),((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value),((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(116) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(116) << 1) | 1)),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value),((lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6 = (const lean_object*)&l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___boxed(lean_object*);
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
v___x_41_ = lean_apply_7(v_k_33_, v_b_34_, v_c_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, lean_box(0));
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed(lean_object* v_k_42_, lean_object* v_b_43_, lean_object* v_c_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(v_k_42_, v_b_43_, v_c_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
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
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec_ref(v_a_163_);
v_u_176_ = lean_ctor_get(v_a_172_, 0);
lean_inc(v_u_176_);
lean_dec_ref(v_a_172_);
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
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v___x_183_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
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
lean_inc(v_a_209_);
lean_dec_ref(v___x_208_);
lean_inc(v_a_209_);
v___f_210_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed), 8, 1);
lean_closure_set(v___f_210_, 0, v_a_209_);
v___x_211_ = 0;
v___x_212_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_a_209_, v___f_210_, v___x_211_, v___x_211_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_212_;
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
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
uint8_t v___x_247_; 
v___x_247_ = l_Lean_Expr_hasMVar(v_e_244_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v_e_244_);
return v___x_248_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg___boxed(lean_object* v_e_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_e_269_, v___y_270_);
lean_dec(v___y_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(lean_object* v_e_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_e_273_, v___y_275_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___boxed(lean_object* v_e_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(v_e_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(lean_object* v_msg_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___f_294_; lean_object* v___x_7458__overap_295_; lean_object* v___x_296_; 
v___f_294_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_7458__overap_295_ = lean_panic_fn(v___f_294_, v_msg_288_);
v___x_296_ = lean_apply_5(v___x_7458__overap_295_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, lean_box(0));
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___boxed(lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v_msg_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
return v_res_303_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__5(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__4));
v___x_313_ = l_Lean_stringToMessageData(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__7(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__6));
v___x_316_ = l_Lean_stringToMessageData(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__11(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_320_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_321_ = lean_unsigned_to_nat(72u);
v___x_322_ = lean_unsigned_to_nat(35u);
v___x_323_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__9));
v___x_324_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_325_ = l_mkPanicMessageWithDecl(v___x_324_, v___x_323_, v___x_322_, v___x_321_, v___x_320_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcTrans___closed__12(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_326_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_327_ = lean_unsigned_to_nat(53u);
v___x_328_ = lean_unsigned_to_nat(34u);
v___x_329_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__9));
v___x_330_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_331_ = l_mkPanicMessageWithDecl(v___x_330_, v___x_329_, v___x_328_, v___x_327_, v___x_326_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object* v_result_332_, lean_object* v_resultType_333_, lean_object* v_step_334_, lean_object* v_stepType_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_341_; lean_object* v_a_342_; 
v___x_341_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_resultType_333_);
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref(v___x_341_);
if (lean_obj_tag(v_a_342_) == 1)
{
lean_object* v_val_343_; lean_object* v_snd_344_; lean_object* v_fst_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_601_; 
v_val_343_ = lean_ctor_get(v_a_342_, 0);
lean_inc(v_val_343_);
lean_dec_ref(v_a_342_);
v_snd_344_ = lean_ctor_get(v_val_343_, 1);
v_fst_345_ = lean_ctor_get(v_val_343_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_val_343_);
if (v_isSharedCheck_601_ == 0)
{
v___x_347_ = v_val_343_;
v_isShared_348_ = v_isSharedCheck_601_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snd_344_);
lean_inc(v_fst_345_);
lean_dec(v_val_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_601_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_fst_349_; lean_object* v_snd_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_600_; 
v_fst_349_ = lean_ctor_get(v_snd_344_, 0);
v_snd_350_ = lean_ctor_get(v_snd_344_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_snd_344_);
if (v_isSharedCheck_600_ == 0)
{
v___x_352_ = v_snd_344_;
v_isShared_353_ = v_isSharedCheck_600_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_snd_350_);
lean_inc(v_fst_349_);
lean_dec(v_snd_344_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_600_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v_a_357_; 
v___x_354_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_stepType_335_, v_a_337_);
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref(v___x_354_);
v___x_356_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_355_);
lean_dec(v_a_355_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref(v___x_356_);
if (lean_obj_tag(v_a_357_) == 1)
{
lean_object* v_val_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_597_; 
v_val_358_ = lean_ctor_get(v_a_357_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_357_);
if (v_isSharedCheck_597_ == 0)
{
v___x_360_ = v_a_357_;
v_isShared_361_ = v_isSharedCheck_597_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_val_358_);
lean_dec(v_a_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_597_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_snd_362_; lean_object* v_fst_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_596_; 
v_snd_362_ = lean_ctor_get(v_val_358_, 1);
v_fst_363_ = lean_ctor_get(v_val_358_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v_val_358_);
if (v_isSharedCheck_596_ == 0)
{
v___x_365_ = v_val_358_;
v_isShared_366_ = v_isSharedCheck_596_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snd_362_);
lean_inc(v_fst_363_);
lean_dec(v_val_358_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_596_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v_snd_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_594_; 
v_snd_367_ = lean_ctor_get(v_snd_362_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_snd_362_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_snd_362_, 0);
lean_dec(v_unused_595_);
v___x_369_ = v_snd_362_;
v_isShared_370_ = v_isSharedCheck_594_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_snd_367_);
lean_dec(v_snd_362_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_594_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; 
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_fst_345_);
v___x_371_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_fst_345_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref(v___x_371_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_fst_363_);
v___x_373_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(v_fst_363_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_375_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref(v___x_373_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_fst_349_);
v___x_375_ = lean_infer_type(v_fst_349_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___x_375_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_snd_350_);
v___x_377_ = lean_infer_type(v_snd_350_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_379_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref(v___x_377_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_snd_367_);
v___x_379_ = lean_infer_type(v_snd_367_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref(v___x_379_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_a_376_);
v___x_381_ = l_Lean_Meta_getLevel(v_a_376_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_383_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref(v___x_381_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_a_378_);
v___x_383_ = l_Lean_Meta_getLevel(v_a_378_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_385_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref(v___x_383_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_a_380_);
v___x_385_ = l_Lean_Meta_getLevel(v_a_380_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v___x_385_);
v___x_387_ = l_Lean_Meta_mkFreshLevelMVar(v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref(v___x_387_);
lean_inc(v_a_388_);
v___x_389_ = l_Lean_mkSort(v_a_388_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_380_);
v___x_390_ = l_Lean_mkArrow(v_a_380_, v___x_389_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref(v___x_390_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_376_);
v___x_392_ = l_Lean_mkArrow(v_a_376_, v_a_391_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref(v___x_392_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v_a_393_);
v___x_395_ = v___x_360_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_393_);
v___x_395_ = v_reuseFailAlloc_505_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = 0;
v___x_397_ = lean_box(0);
lean_inc_ref(v_a_336_);
v___x_398_ = l_Lean_Meta_mkFreshExprMVar(v___x_395_, v___x_396_, v___x_397_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref(v___x_398_);
v___x_400_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__1));
v___x_401_ = lean_box(0);
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 1);
lean_ctor_set(v___x_365_, 1, v___x_401_);
lean_ctor_set(v___x_365_, 0, v_a_386_);
v___x_403_ = v___x_365_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_386_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_496_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 1);
lean_ctor_set(v___x_352_, 1, v___x_403_);
lean_ctor_set(v___x_352_, 0, v_a_384_);
v___x_405_ = v___x_352_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_384_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_403_);
v___x_405_ = v_reuseFailAlloc_495_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 1);
lean_ctor_set(v___x_347_, 1, v___x_405_);
lean_ctor_set(v___x_347_, 0, v_a_382_);
v___x_407_ = v___x_347_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_382_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_405_);
v___x_407_ = v_reuseFailAlloc_494_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v_a_388_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v_a_374_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v_a_372_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
lean_inc_ref(v___x_410_);
v___x_411_ = l_Lean_mkConst(v___x_400_, v___x_410_);
v___x_412_ = lean_unsigned_to_nat(6u);
v___x_413_ = lean_mk_empty_array_with_capacity(v___x_412_);
lean_inc(v_a_376_);
v___x_414_ = lean_array_push(v___x_413_, v_a_376_);
lean_inc(v_a_378_);
v___x_415_ = lean_array_push(v___x_414_, v_a_378_);
lean_inc(v_a_380_);
v___x_416_ = lean_array_push(v___x_415_, v_a_380_);
lean_inc(v_fst_345_);
v___x_417_ = lean_array_push(v___x_416_, v_fst_345_);
lean_inc(v_fst_363_);
v___x_418_ = lean_array_push(v___x_417_, v_fst_363_);
lean_inc(v_a_399_);
v___x_419_ = lean_array_push(v___x_418_, v_a_399_);
v___x_420_ = l_Lean_mkAppN(v___x_411_, v___x_419_);
lean_dec_ref(v___x_419_);
v___x_421_ = lean_box(0);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc_ref(v___x_420_);
v___x_422_ = l_Lean_Meta_trySynthInstance(v___x_420_, v___x_421_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref(v___x_422_);
if (lean_obj_tag(v_a_423_) == 1)
{
lean_object* v_a_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v___x_420_);
v_a_424_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref(v_a_423_);
v___x_425_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__3));
v___x_426_ = l_Lean_mkConst(v___x_425_, v___x_410_);
v___x_427_ = lean_unsigned_to_nat(12u);
v___x_428_ = lean_mk_empty_array_with_capacity(v___x_427_);
v___x_429_ = lean_array_push(v___x_428_, v_a_376_);
v___x_430_ = lean_array_push(v___x_429_, v_a_378_);
v___x_431_ = lean_array_push(v___x_430_, v_a_380_);
v___x_432_ = lean_array_push(v___x_431_, v_fst_345_);
v___x_433_ = lean_array_push(v___x_432_, v_fst_363_);
v___x_434_ = lean_array_push(v___x_433_, v_a_399_);
v___x_435_ = lean_array_push(v___x_434_, v_a_424_);
v___x_436_ = lean_array_push(v___x_435_, v_fst_349_);
v___x_437_ = lean_array_push(v___x_436_, v_snd_350_);
v___x_438_ = lean_array_push(v___x_437_, v_snd_367_);
v___x_439_ = lean_array_push(v___x_438_, v_result_332_);
v___x_440_ = lean_array_push(v___x_439_, v_step_334_);
v___x_441_ = l_Lean_mkAppN(v___x_426_, v___x_440_);
lean_dec_ref(v___x_440_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc_ref(v___x_441_);
v___x_442_ = lean_infer_type(v___x_441_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_471_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref(v___x_442_);
v___x_444_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_443_, v_a_337_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_471_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_471_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_471_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_457_; lean_object* v_a_458_; 
v___x_449_ = l_Lean_Expr_headBeta(v_a_445_);
v___x_457_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_449_);
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
if (lean_obj_tag(v_a_458_) == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_del_object(v___x_447_);
lean_dec_ref(v___x_441_);
lean_del_object(v___x_369_);
v___x_459_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__5, &l_Lean_Elab_Term_mkCalcTrans___closed__5_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__5);
v___x_460_ = l_Lean_indentExpr(v___x_449_);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_461_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_dec_ref(v_a_458_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
goto v___jp_450_;
}
v___jp_450_:
{
lean_object* v___x_452_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_449_);
lean_ctor_set(v___x_369_, 0, v___x_441_);
v___x_452_ = v___x_369_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_449_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_452_);
v___x_454_ = v___x_447_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v___x_441_);
lean_del_object(v___x_369_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
v_a_472_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_442_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_442_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_a_423_);
lean_dec_ref(v___x_410_);
lean_dec(v_a_399_);
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_dec(v_fst_363_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_dec(v_fst_345_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v___x_480_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__7, &l_Lean_Elab_Term_mkCalcTrans___closed__7_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__7);
v___x_481_ = l_Lean_indentExpr(v___x_420_);
v___x_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = l_Lean_useDiagnosticMsg;
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_484_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
return v___x_485_;
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref(v___x_420_);
lean_dec_ref(v___x_410_);
lean_dec(v_a_399_);
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_dec(v_fst_363_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_486_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_422_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_422_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_a_388_);
lean_dec(v_a_386_);
lean_dec(v_a_384_);
lean_dec(v_a_382_);
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_497_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_398_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_398_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec(v_a_388_);
lean_dec(v_a_386_);
lean_dec(v_a_384_);
lean_dec(v_a_382_);
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_506_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_392_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_392_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_a_388_);
lean_dec(v_a_386_);
lean_dec(v_a_384_);
lean_dec(v_a_382_);
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_514_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_390_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_390_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_a_386_);
lean_dec(v_a_384_);
lean_dec(v_a_382_);
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_522_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_387_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_387_);
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
lean_dec(v_a_384_);
lean_dec(v_a_382_);
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_530_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_385_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_385_);
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
lean_dec(v_a_382_);
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_538_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_383_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_383_);
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
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_546_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_381_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_381_);
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
lean_dec(v_a_378_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_554_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_379_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_379_);
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
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_562_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_377_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_377_);
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
lean_dec(v_a_374_);
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_570_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_375_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_375_);
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
lean_dec(v_a_372_);
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_578_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_373_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_373_);
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
lean_del_object(v___x_369_);
lean_dec(v_snd_367_);
lean_del_object(v___x_365_);
lean_dec(v_fst_363_);
lean_del_object(v___x_360_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v_a_586_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_371_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_371_);
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
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_a_357_);
lean_del_object(v___x_352_);
lean_dec(v_snd_350_);
lean_dec(v_fst_349_);
lean_del_object(v___x_347_);
lean_dec(v_fst_345_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v___x_598_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__11, &l_Lean_Elab_Term_mkCalcTrans___closed__11_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__11);
v___x_599_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v___x_598_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
return v___x_599_;
}
}
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_a_342_);
lean_dec_ref(v_stepType_335_);
lean_dec_ref(v_step_334_);
lean_dec_ref(v_result_332_);
v___x_602_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcTrans___closed__12, &l_Lean_Elab_Term_mkCalcTrans___closed__12_once, _init_l_Lean_Elab_Term_mkCalcTrans___closed__12);
v___x_603_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(v___x_602_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___boxed(lean_object* v_result_604_, lean_object* v_resultType_605_, lean_object* v_step_606_, lean_object* v_stepType_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Elab_Term_mkCalcTrans(v_result_604_, v_resultType_605_, v_step_606_, v_stepType_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec_ref(v_resultType_605_);
return v_res_613_;
}
}
static lean_object* _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
v___x_636_ = l_String_toRawSubstring_x27(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(lean_object* v_type_661_, lean_object* v_t_662_, uint8_t v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
if (v_a_663_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec_ref(v_type_661_);
v___x_671_ = lean_box(v_a_663_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_t_662_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
else
{
if (lean_obj_tag(v_t_662_) == 1)
{
lean_object* v_info_674_; lean_object* v_kind_675_; lean_object* v_args_676_; lean_object* v_k_678_; uint8_t v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; 
v_info_674_ = lean_ctor_get(v_t_662_, 0);
v_kind_675_ = lean_ctor_get(v_t_662_, 1);
v_args_676_ = lean_ctor_get(v_t_662_, 2);
if (lean_obj_tag(v_kind_675_) == 1)
{
lean_object* v_pre_715_; 
v_pre_715_ = lean_ctor_get(v_kind_675_, 0);
if (lean_obj_tag(v_pre_715_) == 1)
{
lean_object* v_pre_716_; 
v_pre_716_ = lean_ctor_get(v_pre_715_, 0);
if (lean_obj_tag(v_pre_716_) == 1)
{
lean_object* v_pre_717_; 
v_pre_717_ = lean_ctor_get(v_pre_716_, 0);
if (lean_obj_tag(v_pre_717_) == 1)
{
lean_object* v_pre_718_; 
v_pre_718_ = lean_ctor_get(v_pre_717_, 0);
if (lean_obj_tag(v_pre_718_) == 0)
{
lean_object* v_str_719_; lean_object* v_str_720_; lean_object* v_str_721_; lean_object* v_str_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_str_719_ = lean_ctor_get(v_kind_675_, 1);
v_str_720_ = lean_ctor_get(v_pre_715_, 1);
v_str_721_ = lean_ctor_get(v_pre_716_, 1);
v_str_722_ = lean_ctor_get(v_pre_717_, 1);
v___x_723_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0));
v___x_724_ = lean_string_dec_eq(v_str_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_inc_ref(v_kind_675_);
lean_inc_ref(v_args_676_);
lean_inc(v_info_674_);
lean_dec_ref(v_t_662_);
v_k_678_ = v_kind_675_;
v___y_679_ = v_a_663_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
goto v___jp_677_;
}
else
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1));
v___x_726_ = lean_string_dec_eq(v_str_721_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_inc_ref(v_str_721_);
lean_inc_ref(v_str_720_);
lean_inc_ref(v_str_719_);
lean_inc(v_pre_718_);
lean_inc_ref(v_args_676_);
lean_inc(v_info_674_);
lean_dec_ref(v_t_662_);
v___x_727_ = l_Lean_Name_str___override(v_pre_718_, v___x_723_);
v___x_728_ = l_Lean_Name_str___override(v___x_727_, v_str_721_);
v___x_729_ = l_Lean_Name_str___override(v___x_728_, v_str_720_);
v___x_730_ = l_Lean_Name_str___override(v___x_729_, v_str_719_);
v_k_678_ = v___x_730_;
v___y_679_ = v_a_663_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
goto v___jp_677_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2));
v___x_732_ = lean_string_dec_eq(v_str_720_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_inc_ref(v_str_720_);
lean_inc(v_pre_718_);
lean_inc_ref(v_str_719_);
lean_inc_ref(v_args_676_);
lean_inc(v_info_674_);
lean_dec_ref(v_t_662_);
v___x_733_ = l_Lean_Name_str___override(v_pre_718_, v___x_723_);
v___x_734_ = l_Lean_Name_str___override(v___x_733_, v___x_725_);
v___x_735_ = l_Lean_Name_str___override(v___x_734_, v_str_720_);
v___x_736_ = l_Lean_Name_str___override(v___x_735_, v_str_719_);
v_k_678_ = v___x_736_;
v___y_679_ = v_a_663_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
goto v___jp_677_;
}
else
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3));
v___x_738_ = lean_string_dec_eq(v_str_719_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_inc(v_pre_718_);
lean_inc_ref(v_str_719_);
lean_inc_ref(v_args_676_);
lean_inc(v_info_674_);
lean_dec_ref(v_t_662_);
v___x_739_ = l_Lean_Name_str___override(v_pre_718_, v___x_723_);
v___x_740_ = l_Lean_Name_str___override(v___x_739_, v___x_725_);
v___x_741_ = l_Lean_Name_str___override(v___x_740_, v___x_731_);
v___x_742_ = l_Lean_Name_str___override(v___x_741_, v_str_719_);
v_k_678_ = v___x_742_;
v___y_679_ = v_a_663_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
goto v___jp_677_;
}
else
{
lean_object* v___x_743_; 
lean_inc_ref(v_a_668_);
v___x_743_ = l_Lean_Elab_Term_exprToSyntax(v_type_661_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_776_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_776_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_776_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_776_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_ref_748_; lean_object* v_quotContext_749_; lean_object* v_currMacroScope_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v_ref_748_ = lean_ctor_get(v_a_668_, 5);
lean_inc(v_ref_748_);
v_quotContext_749_ = lean_ctor_get(v_a_668_, 10);
lean_inc(v_quotContext_749_);
v_currMacroScope_750_ = lean_ctor_get(v_a_668_, 11);
lean_inc(v_currMacroScope_750_);
lean_dec_ref(v_a_668_);
v___x_751_ = 0;
v___x_752_ = l_Lean_SourceInfo_fromRef(v_ref_748_, v___x_751_);
lean_dec(v_ref_748_);
v___x_753_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5));
v___x_754_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7));
v___x_755_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8));
lean_inc(v___x_752_);
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_752_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10));
v___x_758_ = lean_obj_once(&l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12, &l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once, _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12);
v___x_759_ = l_Lean_addMacroScope(v_quotContext_749_, v_pre_718_, v_currMacroScope_750_);
v___x_760_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20));
lean_inc(v___x_752_);
v___x_761_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_761_, 0, v___x_752_);
lean_ctor_set(v___x_761_, 1, v___x_758_);
lean_ctor_set(v___x_761_, 2, v___x_759_);
lean_ctor_set(v___x_761_, 3, v___x_760_);
lean_inc(v___x_752_);
v___x_762_ = l_Lean_Syntax_node1(v___x_752_, v___x_757_, v___x_761_);
lean_inc(v___x_752_);
v___x_763_ = l_Lean_Syntax_node2(v___x_752_, v___x_754_, v___x_756_, v___x_762_);
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21));
lean_inc(v___x_752_);
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_752_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23));
lean_inc(v___x_752_);
v___x_767_ = l_Lean_Syntax_node1(v___x_752_, v___x_766_, v_a_744_);
v___x_768_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24));
lean_inc(v___x_752_);
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_752_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_Syntax_node5(v___x_752_, v___x_753_, v___x_763_, v_t_662_, v___x_765_, v___x_767_, v___x_769_);
v___x_771_ = lean_box(v___x_751_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_772_);
v___x_774_ = v___x_746_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v_t_662_);
lean_dec_ref(v_a_668_);
v_a_777_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_743_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_743_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
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
lean_inc_ref(v_kind_675_);
lean_inc_ref(v_args_676_);
lean_inc(v_info_674_);
lean_dec_ref(v_t_662_);
v_k_678_ = v_kind_675_;
v___y_679_ = v_a_663_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
goto v___jp_677_;
}
}
else
{
lean_inc_ref(v_kind_675_);
lean_inc_ref(v_args_676_);
lean_inc(v_info_674_);
lean_dec_ref(v_t_662_);
v_k_678_ = v_kind_675_;
v___y_679_ = v_a_663_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
goto v___jp_677_;
}
}
else
{
lean_inc_ref(v_kind_675_);
lean_inc_ref(v_args_676_);
lean_inc(v_info_674_);
lean_dec_ref(v_t_662_);
v_k_678_ = v_kind_675_;
v___y_679_ = v_a_663_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
goto v___jp_677_;
}
}
else
{
lean_inc_ref(v_kind_675_);
lean_inc_ref(v_args_676_);
lean_inc(v_info_674_);
lean_dec_ref(v_t_662_);
v_k_678_ = v_kind_675_;
v___y_679_ = v_a_663_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
goto v___jp_677_;
}
}
else
{
lean_inc_ref(v_args_676_);
lean_inc(v_kind_675_);
lean_inc(v_info_674_);
lean_dec_ref(v_t_662_);
v_k_678_ = v_kind_675_;
v___y_679_ = v_a_663_;
v___y_680_ = v_a_664_;
v___y_681_ = v_a_665_;
v___y_682_ = v_a_666_;
v___y_683_ = v_a_667_;
v___y_684_ = v_a_668_;
v___y_685_ = v_a_669_;
goto v___jp_677_;
}
v___jp_677_:
{
size_t v_sz_686_; size_t v___x_687_; lean_object* v___x_688_; 
v_sz_686_ = lean_array_size(v_args_676_);
v___x_687_ = ((size_t)0ULL);
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_661_, v_sz_686_, v___x_687_, v_args_676_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_706_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_706_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_706_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_706_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_705_; 
v_fst_693_ = lean_ctor_get(v_a_689_, 0);
v_snd_694_ = lean_ctor_get(v_a_689_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_a_689_);
if (v_isSharedCheck_705_ == 0)
{
v___x_696_ = v_a_689_;
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_inc(v_fst_693_);
lean_dec(v_a_689_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_698_, 0, v_info_674_);
lean_ctor_set(v___x_698_, 1, v_k_678_);
lean_ctor_set(v___x_698_, 2, v_fst_693_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_snd_694_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_700_);
v___x_702_ = v___x_691_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_k_678_);
lean_dec(v_info_674_);
v_a_707_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_688_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_688_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
else
{
uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec_ref(v_type_661_);
v___x_785_ = 0;
v___x_786_ = lean_box(v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_t_662_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(lean_object* v_type_789_, size_t v_sz_790_, size_t v_i_791_, lean_object* v_bs_792_, uint8_t v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = lean_usize_dec_lt(v_i_791_, v_sz_790_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec_ref(v_type_789_);
v___x_802_ = lean_box(v___y_793_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_bs_792_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
else
{
lean_object* v_v_805_; lean_object* v___x_806_; 
v_v_805_ = lean_array_uget_borrowed(v_bs_792_, v_i_791_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_795_);
lean_inc_ref(v___y_794_);
lean_inc(v_v_805_);
lean_inc_ref(v_type_789_);
v___x_806_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_789_, v_v_805_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v_fst_808_; lean_object* v_snd_809_; lean_object* v___x_810_; lean_object* v_bs_x27_811_; size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v___x_806_);
v_fst_808_ = lean_ctor_get(v_a_807_, 0);
lean_inc(v_fst_808_);
v_snd_809_ = lean_ctor_get(v_a_807_, 1);
lean_inc(v_snd_809_);
lean_dec(v_a_807_);
v___x_810_ = lean_unsigned_to_nat(0u);
v_bs_x27_811_ = lean_array_uset(v_bs_792_, v_i_791_, v___x_810_);
v___x_812_ = ((size_t)1ULL);
v___x_813_ = lean_usize_add(v_i_791_, v___x_812_);
v___x_814_ = lean_array_uset(v_bs_x27_811_, v_i_791_, v_fst_808_);
v___x_815_ = lean_unbox(v_snd_809_);
lean_dec(v_snd_809_);
v_i_791_ = v___x_813_;
v_bs_792_ = v___x_814_;
v___y_793_ = v___x_815_;
goto _start;
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec_ref(v_bs_792_);
lean_dec_ref(v_type_789_);
v_a_817_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_806_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_806_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0___boxed(lean_object* v_type_825_, lean_object* v_sz_826_, lean_object* v_i_827_, lean_object* v_bs_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
size_t v_sz_boxed_837_; size_t v_i_boxed_838_; uint8_t v___y_7889__boxed_839_; lean_object* v_res_840_; 
v_sz_boxed_837_ = lean_unbox_usize(v_sz_826_);
lean_dec(v_sz_826_);
v_i_boxed_838_ = lean_unbox_usize(v_i_827_);
lean_dec(v_i_827_);
v___y_7889__boxed_839_ = lean_unbox(v___y_829_);
v_res_840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_825_, v_sz_boxed_837_, v_i_boxed_838_, v_bs_828_, v___y_7889__boxed_839_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object* v_type_841_, lean_object* v_t_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
uint8_t v_a_7958__boxed_851_; lean_object* v_res_852_; 
v_a_7958__boxed_851_ = lean_unbox(v_a_843_);
v_res_852_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_841_, v_t_842_, v_a_7958__boxed_851_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object* v_t_853_, lean_object* v_type_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
uint8_t v___x_862_; lean_object* v___x_863_; 
v___x_862_ = 1;
v___x_863_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(v_type_854_, v_t_853_, v___x_862_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_872_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_fst_868_; lean_object* v___x_870_; 
v_fst_868_ = lean_ctor_get(v_a_864_, 0);
lean_inc(v_fst_868_);
lean_dec(v_a_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_fst_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_fst_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_863_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_863_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType___boxed(lean_object* v_t_881_, lean_object* v_type_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_t_881_, v_type_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
return v_res_890_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
v___x_896_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg(){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0);
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___boxed(lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(lean_object* v_00_u03b1_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___boxed(lean_object* v_00_u03b1_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(v_00_u03b1_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__7));
v___x_937_ = l_String_toRawSubstring_x27(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView(lean_object* v_step0_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_ref_954_; lean_object* v_quotContext_955_; lean_object* v_currMacroScope_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_ref_954_ = lean_ctor_get(v_a_951_, 5);
lean_inc(v_ref_954_);
v_quotContext_955_ = lean_ctor_get(v_a_951_, 10);
lean_inc(v_quotContext_955_);
v_currMacroScope_956_ = lean_ctor_get(v_a_951_, 11);
lean_inc(v_currMacroScope_956_);
lean_dec_ref(v_a_951_);
v___x_957_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_946_);
v___x_958_ = l_Lean_Syntax_isOfKind(v_step0_946_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec(v_currMacroScope_956_);
lean_dec(v_quotContext_955_);
lean_dec(v_ref_954_);
lean_dec(v_step0_946_);
v___x_959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_959_;
}
else
{
lean_object* v___x_960_; lean_object* v_term_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v_term_961_ = l_Lean_Syntax_getArg(v_step0_946_, v___x_960_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = l_Lean_Syntax_getArg(v_step0_946_, v___x_962_);
lean_inc(v___x_963_);
v___x_964_ = l_Lean_Syntax_matchesNull(v___x_963_, v___x_960_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; uint8_t v___x_966_; 
lean_dec(v_currMacroScope_956_);
lean_dec(v_quotContext_955_);
lean_dec(v_ref_954_);
v___x_965_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_963_);
v___x_966_ = l_Lean_Syntax_matchesNull(v___x_963_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec(v___x_963_);
lean_dec(v_term_961_);
lean_dec(v_step0_946_);
v___x_967_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_967_;
}
else
{
lean_object* v_proof_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_proof_968_ = l_Lean_Syntax_getArg(v___x_963_, v___x_962_);
lean_dec(v___x_963_);
v___x_969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_969_, 0, v_step0_946_);
lean_ctor_set(v___x_969_, 1, v_term_961_);
lean_ctor_set(v___x_969_, 2, v_proof_968_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
else
{
lean_object* v_ref_971_; uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v___x_963_);
v_ref_971_ = l_Lean_replaceRef(v_step0_946_, v_ref_954_);
lean_dec(v_ref_954_);
v___x_972_ = 0;
v___x_973_ = l_Lean_SourceInfo_fromRef(v_ref_971_, v___x_972_);
lean_dec(v_ref_971_);
v___x_974_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__3));
v___x_975_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__4));
lean_inc(v___x_973_);
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_973_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5));
v___x_978_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__6));
lean_inc(v___x_973_);
v___x_979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_973_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
lean_inc(v___x_973_);
v___x_980_ = l_Lean_Syntax_node1(v___x_973_, v___x_977_, v___x_979_);
lean_inc(v___x_973_);
v___x_981_ = l_Lean_Syntax_node3(v___x_973_, v___x_974_, v_term_961_, v___x_976_, v___x_980_);
v___x_982_ = lean_obj_once(&l_Lean_Elab_Term_mkCalcFirstStepView___closed__8, &l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once, _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8);
v___x_983_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__9));
v___x_984_ = l_Lean_addMacroScope(v_quotContext_955_, v___x_983_, v_currMacroScope_956_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__11));
v___x_986_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_986_, 0, v___x_973_);
lean_ctor_set(v___x_986_, 1, v___x_982_);
lean_ctor_set(v___x_986_, 2, v___x_984_);
lean_ctor_set(v___x_986_, 3, v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_987_, 0, v_step0_946_);
lean_ctor_set(v___x_987_, 1, v___x_981_);
lean_ctor_set(v___x_987_, 2, v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___boxed(lean_object* v_step0_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(lean_object* v_as_1002_, size_t v_sz_1003_, size_t v_i_1004_, lean_object* v_b_1005_){
_start:
{
lean_object* v_a_1008_; uint8_t v___x_1012_; 
v___x_1012_ = lean_usize_dec_lt(v_i_1004_, v_sz_1003_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_b_1005_);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; lean_object* v_a_1015_; uint8_t v___x_1016_; 
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1));
v_a_1015_ = lean_array_uget_borrowed(v_as_1002_, v_i_1004_);
lean_inc(v_a_1015_);
v___x_1016_ = l_Lean_Syntax_isOfKind(v_a_1015_, v___x_1014_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_dec_ref(v___x_1017_);
v_a_1008_ = v_b_1005_;
goto v___jp_1007_;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_b_1005_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = l_Lean_Syntax_getArg(v_a_1015_, v___x_1026_);
v___x_1028_ = lean_unsigned_to_nat(2u);
v___x_1029_ = l_Lean_Syntax_getArg(v_a_1015_, v___x_1028_);
lean_inc(v_a_1015_);
v___x_1030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1030_, 0, v_a_1015_);
lean_ctor_set(v___x_1030_, 1, v___x_1027_);
lean_ctor_set(v___x_1030_, 2, v___x_1029_);
v___x_1031_ = lean_array_push(v_b_1005_, v___x_1030_);
v_a_1008_ = v___x_1031_;
goto v___jp_1007_;
}
}
v___jp_1007_:
{
size_t v___x_1009_; size_t v___x_1010_; 
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_1004_, v___x_1009_);
v_i_1004_ = v___x_1010_;
v_b_1005_ = v_a_1008_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___boxed(lean_object* v_as_1032_, lean_object* v_sz_1033_, lean_object* v_i_1034_, lean_object* v_b_1035_, lean_object* v___y_1036_){
_start:
{
size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1033_);
lean_dec(v_sz_1033_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1032_, v_sz_boxed_1037_, v_i_boxed_1038_, v_b_1035_);
lean_dec_ref(v_as_1032_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object* v_steps_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_1044_);
v___x_1053_ = l_Lean_Syntax_isOfKind(v_steps_1044_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
lean_dec_ref(v_a_1049_);
lean_dec(v_steps_1044_);
v___x_1054_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; lean_object* v_step0_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v_step0_1056_ = l_Lean_Syntax_getArg(v_steps_1044_, v___x_1055_);
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1));
lean_inc(v_step0_1056_);
v___x_1058_ = l_Lean_Syntax_isOfKind(v_step0_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec(v_step0_1056_);
lean_dec_ref(v_a_1049_);
lean_dec(v_steps_1044_);
v___x_1059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Elab_Term_mkCalcFirstStepView(v_step0_1056_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_rest_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; size_t v_sz_1067_; size_t v___x_1068_; lean_object* v___x_1069_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = l_Lean_Syntax_getArg(v_steps_1044_, v___x_1062_);
lean_dec(v_steps_1044_);
v_rest_1064_ = l_Lean_Syntax_getArgs(v___x_1063_);
lean_dec(v___x_1063_);
v___x_1065_ = lean_mk_empty_array_with_capacity(v___x_1062_);
v___x_1066_ = lean_array_push(v___x_1065_, v_a_1061_);
v_sz_1067_ = lean_array_size(v_rest_1064_);
v___x_1068_ = ((size_t)0ULL);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_rest_1064_, v_sz_1067_, v___x_1068_, v___x_1066_);
lean_dec_ref(v_rest_1064_);
return v___x_1069_;
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_steps_1044_);
v_a_1070_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1060_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1060_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews___boxed(lean_object* v_steps_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
lean_dec(v_a_1084_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(lean_object* v_as_1087_, size_t v_sz_1088_, size_t v_i_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_1087_, v_sz_1088_, v_i_1089_, v_b_1090_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(lean_object* v_as_1099_, lean_object* v_sz_1100_, lean_object* v_i_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
size_t v_sz_boxed_1110_; size_t v_i_boxed_1111_; lean_object* v_res_1112_; 
v_sz_boxed_1110_ = lean_unbox_usize(v_sz_1100_);
lean_dec(v_sz_1100_);
v_i_boxed_1111_ = lean_unbox_usize(v_i_1101_);
lean_dec(v_i_1101_);
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(v_as_1099_, v_sz_boxed_1110_, v_i_boxed_1111_, v_b_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v_as_1099_);
return v_res_1112_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = l_Lean_instInhabitedExpr;
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(lean_object* v_msg_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_obj_once(&l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0, &l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0);
v___x_1117_ = lean_panic_fn(v___x_1116_, v_msg_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(lean_object* v_opts_1118_, lean_object* v_opt_1119_){
_start:
{
lean_object* v_name_1120_; lean_object* v_defValue_1121_; lean_object* v_map_1122_; lean_object* v___x_1123_; 
v_name_1120_ = lean_ctor_get(v_opt_1119_, 0);
v_defValue_1121_ = lean_ctor_get(v_opt_1119_, 1);
v_map_1122_ = lean_ctor_get(v_opts_1118_, 0);
v___x_1123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1122_, v_name_1120_);
if (lean_obj_tag(v___x_1123_) == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_unbox(v_defValue_1121_);
return v___x_1124_;
}
else
{
lean_object* v_val_1125_; 
v_val_1125_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_val_1125_);
lean_dec_ref(v___x_1123_);
if (lean_obj_tag(v_val_1125_) == 1)
{
uint8_t v_v_1126_; 
v_v_1126_ = lean_ctor_get_uint8(v_val_1125_, 0);
lean_dec_ref(v_val_1125_);
return v_v_1126_;
}
else
{
uint8_t v___x_1127_; 
lean_dec(v_val_1125_);
v___x_1127_ = lean_unbox(v_defValue_1121_);
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_opts_1128_, lean_object* v_opt_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_opts_1128_, v_opt_1129_);
lean_dec_ref(v_opt_1129_);
lean_dec_ref(v_opts_1128_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_box(1);
v___x_1133_ = l_Lean_MessageData_ofFormat(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2));
v___x_1138_ = l_Lean_MessageData_ofFormat(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
return v_x_1139_;
}
else
{
lean_object* v_head_1141_; lean_object* v_tail_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1164_; 
v_head_1141_ = lean_ctor_get(v_x_1140_, 0);
v_tail_1142_ = lean_ctor_get(v_x_1140_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1144_ = v_x_1140_;
v_isShared_1145_ = v_isSharedCheck_1164_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_tail_1142_);
lean_inc(v_head_1141_);
lean_dec(v_x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1164_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_before_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1162_; 
v_before_1146_ = lean_ctor_get(v_head_1141_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_head_1141_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v_head_1141_, 1);
lean_dec(v_unused_1163_);
v___x_1148_ = v_head_1141_;
v_isShared_1149_ = v_isSharedCheck_1162_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_before_1146_);
lean_dec(v_head_1141_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1162_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 7);
lean_ctor_set(v___x_1148_, 1, v___x_1150_);
lean_ctor_set(v___x_1148_, 0, v_x_1139_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_x_1139_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3);
if (v_isShared_1145_ == 0)
{
lean_ctor_set_tag(v___x_1144_, 7);
lean_ctor_set(v___x_1144_, 1, v___x_1153_);
lean_ctor_set(v___x_1144_, 0, v___x_1152_);
v___x_1155_ = v___x_1144_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = l_Lean_MessageData_ofSyntax(v_before_1146_);
v___x_1157_ = l_Lean_indentD(v___x_1156_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1155_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v_x_1139_ = v___x_1158_;
v_x_1140_ = v_tail_1142_;
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
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_1169_ = l_Lean_MessageData_ofFormat(v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_1170_, lean_object* v_macroStack_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_options_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v_options_1174_ = lean_ctor_get(v___y_1172_, 2);
v___x_1175_ = l_Lean_Elab_pp_macroStack;
v___x_1176_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_options_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_dec(v_macroStack_1171_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_msgData_1170_);
return v___x_1177_;
}
else
{
if (lean_obj_tag(v_macroStack_1171_) == 0)
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_msgData_1170_);
return v___x_1178_;
}
else
{
lean_object* v_head_1179_; lean_object* v_after_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1195_; 
v_head_1179_ = lean_ctor_get(v_macroStack_1171_, 0);
lean_inc(v_head_1179_);
v_after_1180_ = lean_ctor_get(v_head_1179_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_head_1179_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_head_1179_, 0);
lean_dec(v_unused_1196_);
v___x_1182_ = v_head_1179_;
v_isShared_1183_ = v_isSharedCheck_1195_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_after_1180_);
lean_dec(v_head_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1195_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 7);
lean_ctor_set(v___x_1182_, 1, v___x_1184_);
lean_ctor_set(v___x_1182_, 0, v_msgData_1170_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_msgData_1170_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_msgData_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1187_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Lean_MessageData_ofSyntax(v_after_1180_);
v___x_1190_ = l_Lean_indentD(v___x_1189_);
v_msgData_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1191_, 0, v___x_1188_);
lean_ctor_set(v_msgData_1191_, 1, v___x_1190_);
v___x_1192_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(v_msgData_1191_, v_macroStack_1171_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1197_, lean_object* v_macroStack_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1197_, v_macroStack_1198_, v___y_1199_);
lean_dec_ref(v___y_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(lean_object* v_msg_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_ref_1210_; lean_object* v___x_1211_; lean_object* v_a_1212_; lean_object* v_macroStack_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
v_ref_1210_ = lean_ctor_get(v___y_1207_, 5);
v___x_1211_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_1202_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v___x_1211_);
v_macroStack_1213_ = lean_ctor_get(v___y_1203_, 1);
lean_inc(v_macroStack_1213_);
lean_dec_ref(v___y_1203_);
lean_inc(v_macroStack_1213_);
v___x_1214_ = l_Lean_Elab_getBetterRef(v_ref_1210_, v_macroStack_1213_);
v___x_1215_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_a_1212_, v_macroStack_1213_, v___y_1207_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1214_);
lean_ctor_set(v___x_1220_, 1, v_a_1216_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set_tag(v___x_1218_, 1);
lean_ctor_set(v___x_1218_, 0, v___x_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(lean_object* v_ref_1234_, lean_object* v_msg_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_fileName_1243_; lean_object* v_fileMap_1244_; lean_object* v_options_1245_; lean_object* v_currRecDepth_1246_; lean_object* v_maxRecDepth_1247_; lean_object* v_ref_1248_; lean_object* v_currNamespace_1249_; lean_object* v_openDecls_1250_; lean_object* v_initHeartbeats_1251_; lean_object* v_maxHeartbeats_1252_; lean_object* v_quotContext_1253_; lean_object* v_currMacroScope_1254_; uint8_t v_diag_1255_; lean_object* v_cancelTk_x3f_1256_; uint8_t v_suppressElabErrors_1257_; lean_object* v_inheritedTraceOptions_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1267_; 
v_fileName_1243_ = lean_ctor_get(v___y_1240_, 0);
v_fileMap_1244_ = lean_ctor_get(v___y_1240_, 1);
v_options_1245_ = lean_ctor_get(v___y_1240_, 2);
v_currRecDepth_1246_ = lean_ctor_get(v___y_1240_, 3);
v_maxRecDepth_1247_ = lean_ctor_get(v___y_1240_, 4);
v_ref_1248_ = lean_ctor_get(v___y_1240_, 5);
v_currNamespace_1249_ = lean_ctor_get(v___y_1240_, 6);
v_openDecls_1250_ = lean_ctor_get(v___y_1240_, 7);
v_initHeartbeats_1251_ = lean_ctor_get(v___y_1240_, 8);
v_maxHeartbeats_1252_ = lean_ctor_get(v___y_1240_, 9);
v_quotContext_1253_ = lean_ctor_get(v___y_1240_, 10);
v_currMacroScope_1254_ = lean_ctor_get(v___y_1240_, 11);
v_diag_1255_ = lean_ctor_get_uint8(v___y_1240_, sizeof(void*)*14);
v_cancelTk_x3f_1256_ = lean_ctor_get(v___y_1240_, 12);
v_suppressElabErrors_1257_ = lean_ctor_get_uint8(v___y_1240_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1258_ = lean_ctor_get(v___y_1240_, 13);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___y_1240_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1260_ = v___y_1240_;
v_isShared_1261_ = v_isSharedCheck_1267_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_inheritedTraceOptions_1258_);
lean_inc(v_cancelTk_x3f_1256_);
lean_inc(v_currMacroScope_1254_);
lean_inc(v_quotContext_1253_);
lean_inc(v_maxHeartbeats_1252_);
lean_inc(v_initHeartbeats_1251_);
lean_inc(v_openDecls_1250_);
lean_inc(v_currNamespace_1249_);
lean_inc(v_ref_1248_);
lean_inc(v_maxRecDepth_1247_);
lean_inc(v_currRecDepth_1246_);
lean_inc(v_options_1245_);
lean_inc(v_fileMap_1244_);
lean_inc(v_fileName_1243_);
lean_dec(v___y_1240_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1267_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_ref_1262_; lean_object* v___x_1264_; 
v_ref_1262_ = l_Lean_replaceRef(v_ref_1234_, v_ref_1248_);
lean_dec(v_ref_1248_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 5, v_ref_1262_);
v___x_1264_ = v___x_1260_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_fileName_1243_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_fileMap_1244_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_options_1245_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v_currRecDepth_1246_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v_maxRecDepth_1247_);
lean_ctor_set(v_reuseFailAlloc_1266_, 5, v_ref_1262_);
lean_ctor_set(v_reuseFailAlloc_1266_, 6, v_currNamespace_1249_);
lean_ctor_set(v_reuseFailAlloc_1266_, 7, v_openDecls_1250_);
lean_ctor_set(v_reuseFailAlloc_1266_, 8, v_initHeartbeats_1251_);
lean_ctor_set(v_reuseFailAlloc_1266_, 9, v_maxHeartbeats_1252_);
lean_ctor_set(v_reuseFailAlloc_1266_, 10, v_quotContext_1253_);
lean_ctor_set(v_reuseFailAlloc_1266_, 11, v_currMacroScope_1254_);
lean_ctor_set(v_reuseFailAlloc_1266_, 12, v_cancelTk_x3f_1256_);
lean_ctor_set(v_reuseFailAlloc_1266_, 13, v_inheritedTraceOptions_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1266_, sizeof(void*)*14, v_diag_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1266_, sizeof(void*)*14 + 1, v_suppressElabErrors_1257_);
v___x_1264_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___x_1264_, v___y_1241_);
lean_dec_ref(v___x_1264_);
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg___boxed(lean_object* v_ref_1268_, lean_object* v_msg_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1268_, v_msg_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec(v_ref_1268_);
return v_res_1277_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(lean_object* v_as_1290_, size_t v_sz_1291_, size_t v_i_1292_, lean_object* v_b_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_a_1302_; lean_object* v___y_1307_; lean_object* v_a_1308_; uint8_t v___x_1312_; 
v___x_1312_ = lean_usize_dec_lt(v_i_1292_, v_sz_1291_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_b_1293_);
return v___x_1313_;
}
else
{
lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1531_; 
v_fst_1314_ = lean_ctor_get(v_b_1293_, 0);
v_snd_1315_ = lean_ctor_get(v_b_1293_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_b_1293_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1317_ = v_b_1293_;
v_isShared_1318_ = v_isSharedCheck_1531_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_inc(v_fst_1314_);
lean_dec(v_b_1293_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1531_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_a_1319_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v_a_1397_; 
v_a_1319_ = lean_array_uget_borrowed(v_as_1290_, v_i_1292_);
if (lean_obj_tag(v_snd_1315_) == 1)
{
lean_object* v_val_1508_; lean_object* v___x_1509_; 
v_val_1508_ = lean_ctor_get(v_snd_1315_, 0);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v_val_1508_);
v___x_1509_ = lean_infer_type(v_val_1508_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v_term_1511_; lean_object* v___x_1512_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1509_);
v_term_1511_ = lean_ctor_get(v_a_1319_, 1);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
lean_inc(v_term_1511_);
v___x_1512_ = l_Lean_Elab_Term_annotateFirstHoleWithType(v_term_1511_, v_a_1510_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v___x_1512_);
v_a_1397_ = v_a_1513_;
goto v___jp_1396_;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v_snd_1315_);
lean_del_object(v___x_1317_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1514_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1512_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1512_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v_snd_1315_);
lean_del_object(v___x_1317_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1522_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1509_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1509_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_term_1530_; 
v_term_1530_ = lean_ctor_get(v_a_1319_, 1);
lean_inc(v_term_1530_);
v_a_1397_ = v_term_1530_;
goto v___jp_1396_;
}
v___jp_1320_:
{
lean_object* v_term_1329_; lean_object* v_proof_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_term_1329_ = lean_ctor_get(v_a_1319_, 1);
v_proof_1330_ = lean_ctor_get(v_a_1319_, 2);
lean_inc_ref(v___y_1322_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___y_1322_);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_box(v___x_1312_);
v___x_1334_ = lean_box(v___x_1312_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
lean_inc(v___y_1324_);
lean_inc_ref(v___y_1323_);
lean_inc(v_proof_1330_);
v___x_1335_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 9);
lean_closure_set(v___x_1335_, 0, v_proof_1330_);
lean_closure_set(v___x_1335_, 1, v___x_1331_);
lean_closure_set(v___x_1335_, 2, v___x_1333_);
lean_closure_set(v___x_1335_, 3, v___x_1334_);
lean_closure_set(v___x_1335_, 4, v___x_1332_);
lean_closure_set(v___x_1335_, 5, v___y_1323_);
lean_closure_set(v___x_1335_, 6, v___y_1324_);
lean_closure_set(v___x_1335_, 7, v___y_1325_);
lean_closure_set(v___x_1335_, 8, v___y_1326_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
v___x_1336_ = l_Lean_Core_withFreshMacroScope___redArg(v___x_1335_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1336_) == 0)
{
if (lean_obj_tag(v_fst_1314_) == 1)
{
lean_object* v_val_1337_; lean_object* v_a_1338_; lean_object* v_fst_1339_; lean_object* v_snd_1340_; lean_object* v___x_1341_; 
lean_del_object(v___x_1317_);
v_val_1337_ = lean_ctor_get(v_fst_1314_, 0);
lean_inc(v_val_1337_);
lean_dec_ref(v_fst_1314_);
v_a_1338_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1336_);
v_fst_1339_ = lean_ctor_get(v_val_1337_, 0);
lean_inc(v_fst_1339_);
v_snd_1340_ = lean_ctor_get(v_val_1337_, 1);
lean_inc(v_snd_1340_);
lean_dec(v_val_1337_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
v___x_1341_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_fileName_1342_; lean_object* v_fileMap_1343_; lean_object* v_options_1344_; lean_object* v_currRecDepth_1345_; lean_object* v_maxRecDepth_1346_; lean_object* v_ref_1347_; lean_object* v_currNamespace_1348_; lean_object* v_openDecls_1349_; lean_object* v_initHeartbeats_1350_; lean_object* v_maxHeartbeats_1351_; lean_object* v_quotContext_1352_; lean_object* v_currMacroScope_1353_; uint8_t v_diag_1354_; lean_object* v_cancelTk_x3f_1355_; uint8_t v_suppressElabErrors_1356_; lean_object* v_inheritedTraceOptions_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v___x_1341_);
v_fileName_1342_ = lean_ctor_get(v___y_1327_, 0);
v_fileMap_1343_ = lean_ctor_get(v___y_1327_, 1);
v_options_1344_ = lean_ctor_get(v___y_1327_, 2);
v_currRecDepth_1345_ = lean_ctor_get(v___y_1327_, 3);
v_maxRecDepth_1346_ = lean_ctor_get(v___y_1327_, 4);
v_ref_1347_ = lean_ctor_get(v___y_1327_, 5);
v_currNamespace_1348_ = lean_ctor_get(v___y_1327_, 6);
v_openDecls_1349_ = lean_ctor_get(v___y_1327_, 7);
v_initHeartbeats_1350_ = lean_ctor_get(v___y_1327_, 8);
v_maxHeartbeats_1351_ = lean_ctor_get(v___y_1327_, 9);
v_quotContext_1352_ = lean_ctor_get(v___y_1327_, 10);
v_currMacroScope_1353_ = lean_ctor_get(v___y_1327_, 11);
v_diag_1354_ = lean_ctor_get_uint8(v___y_1327_, sizeof(void*)*14);
v_cancelTk_x3f_1355_ = lean_ctor_get(v___y_1327_, 12);
v_suppressElabErrors_1356_ = lean_ctor_get_uint8(v___y_1327_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1357_ = lean_ctor_get(v___y_1327_, 13);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___y_1327_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1359_ = v___y_1327_;
v_isShared_1360_ = v_isSharedCheck_1375_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_inheritedTraceOptions_1357_);
lean_inc(v_cancelTk_x3f_1355_);
lean_inc(v_currMacroScope_1353_);
lean_inc(v_quotContext_1352_);
lean_inc(v_maxHeartbeats_1351_);
lean_inc(v_initHeartbeats_1350_);
lean_inc(v_openDecls_1349_);
lean_inc(v_currNamespace_1348_);
lean_inc(v_ref_1347_);
lean_inc(v_maxRecDepth_1346_);
lean_inc(v_currRecDepth_1345_);
lean_inc(v_options_1344_);
lean_inc(v_fileMap_1343_);
lean_inc(v_fileName_1342_);
lean_dec(v___y_1327_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1375_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_ref_1361_; lean_object* v___x_1363_; 
v_ref_1361_ = l_Lean_replaceRef(v_term_1329_, v_ref_1347_);
lean_dec(v_ref_1347_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 5, v_ref_1361_);
v___x_1363_ = v___x_1359_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_fileName_1342_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_fileMap_1343_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_options_1344_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_currRecDepth_1345_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_maxRecDepth_1346_);
lean_ctor_set(v_reuseFailAlloc_1374_, 5, v_ref_1361_);
lean_ctor_set(v_reuseFailAlloc_1374_, 6, v_currNamespace_1348_);
lean_ctor_set(v_reuseFailAlloc_1374_, 7, v_openDecls_1349_);
lean_ctor_set(v_reuseFailAlloc_1374_, 8, v_initHeartbeats_1350_);
lean_ctor_set(v_reuseFailAlloc_1374_, 9, v_maxHeartbeats_1351_);
lean_ctor_set(v_reuseFailAlloc_1374_, 10, v_quotContext_1352_);
lean_ctor_set(v_reuseFailAlloc_1374_, 11, v_currMacroScope_1353_);
lean_ctor_set(v_reuseFailAlloc_1374_, 12, v_cancelTk_x3f_1355_);
lean_ctor_set(v_reuseFailAlloc_1374_, 13, v_inheritedTraceOptions_1357_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*14, v_diag_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*14 + 1, v_suppressElabErrors_1356_);
v___x_1363_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_1339_, v_snd_1340_, v_a_1338_, v___y_1322_, v___y_1325_, v___y_1326_, v___x_1363_, v___y_1328_);
lean_dec(v_snd_1340_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1364_);
v___y_1307_ = v___y_1321_;
v_a_1308_ = v_a_1365_;
goto v___jp_1306_;
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1366_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1364_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1364_);
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
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_snd_1340_);
lean_dec(v_fst_1339_);
lean_dec(v_a_1338_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1376_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1341_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1341_);
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
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v_fst_1314_);
v_a_1384_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1336_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v___y_1322_);
lean_ctor_set(v___x_1317_, 0, v_a_1384_);
v___x_1386_ = v___x_1317_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1384_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___y_1322_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
v___y_1307_ = v___y_1321_;
v_a_1308_ = v___x_1386_;
goto v___jp_1306_;
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_del_object(v___x_1317_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1388_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1336_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1336_);
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
lean_object* v___x_1398_; 
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
v___x_1398_ = l_Lean_Elab_Term_elabType(v_a_1397_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1400_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_1399_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
if (lean_obj_tag(v_a_1401_) == 1)
{
lean_object* v_val_1402_; lean_object* v_snd_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1476_; 
v_val_1402_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_val_1402_);
lean_dec_ref(v_a_1401_);
v_snd_1403_ = lean_ctor_get(v_val_1402_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_val_1402_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v_val_1402_, 0);
lean_dec(v_unused_1477_);
v___x_1405_ = v_val_1402_;
v_isShared_1406_ = v_isSharedCheck_1476_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_snd_1403_);
lean_dec(v_val_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1476_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
if (lean_obj_tag(v_snd_1315_) == 1)
{
lean_object* v_fst_1407_; lean_object* v_snd_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1474_; 
v_fst_1407_ = lean_ctor_get(v_snd_1403_, 0);
v_snd_1408_ = lean_ctor_get(v_snd_1403_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_snd_1403_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1410_ = v_snd_1403_;
v_isShared_1411_ = v_isSharedCheck_1474_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_snd_1408_);
lean_inc(v_fst_1407_);
lean_dec(v_snd_1403_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1474_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_val_1412_; lean_object* v___x_1413_; 
v_val_1412_ = lean_ctor_get(v_snd_1315_, 0);
lean_inc(v_val_1412_);
lean_dec_ref(v_snd_1315_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v_val_1412_);
lean_inc(v_fst_1407_);
v___x_1413_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1407_, v_val_1412_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; uint8_t v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = lean_unbox(v_a_1414_);
lean_dec(v_a_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v_fst_1407_);
v___x_1416_ = lean_infer_type(v_fst_1407_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1418_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref(v___x_1416_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v_val_1412_);
v___x_1418_ = lean_infer_type(v_val_1412_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v_term_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
v_term_1420_ = lean_ctor_get(v_a_1319_, 1);
v___x_1421_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_1422_ = l_Lean_MessageData_ofExpr(v_fst_1407_);
v___x_1423_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 7);
lean_ctor_set(v___x_1410_, 1, v___x_1423_);
lean_ctor_set(v___x_1410_, 0, v___x_1422_);
v___x_1425_ = v___x_1410_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = l_Lean_MessageData_ofExpr(v_a_1417_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 7);
lean_ctor_set(v___x_1405_, 1, v___x_1426_);
lean_ctor_set(v___x_1405_, 0, v___x_1425_);
v___x_1428_ = v___x_1405_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1429_ = l_Lean_indentD(v___x_1428_);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1421_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l_Lean_MessageData_ofExpr(v_val_1412_);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1423_);
v___x_1435_ = l_Lean_MessageData_ofExpr(v_a_1419_);
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = l_Lean_indentD(v___x_1436_);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1432_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
lean_inc_ref(v___y_1298_);
lean_inc_ref(v___y_1294_);
v___x_1439_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1420_, v___x_1438_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec_ref(v___x_1439_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
v___y_1321_ = v_snd_1408_;
v___y_1322_ = v_a_1399_;
v___y_1323_ = v___y_1294_;
v___y_1324_ = v___y_1295_;
v___y_1325_ = v___y_1296_;
v___y_1326_ = v___y_1297_;
v___y_1327_ = v___y_1298_;
v___y_1328_ = v___y_1299_;
goto v___jp_1320_;
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_snd_1408_);
lean_dec(v_a_1399_);
lean_del_object(v___x_1317_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_a_1417_);
lean_dec(v_val_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_snd_1408_);
lean_dec(v_fst_1407_);
lean_del_object(v___x_1405_);
lean_dec(v_a_1399_);
lean_del_object(v___x_1317_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1450_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1418_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1418_);
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
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_val_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_snd_1408_);
lean_dec(v_fst_1407_);
lean_del_object(v___x_1405_);
lean_dec(v_a_1399_);
lean_del_object(v___x_1317_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1458_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1416_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1416_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_dec(v_val_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_fst_1407_);
lean_del_object(v___x_1405_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
v___y_1321_ = v_snd_1408_;
v___y_1322_ = v_a_1399_;
v___y_1323_ = v___y_1294_;
v___y_1324_ = v___y_1295_;
v___y_1325_ = v___y_1296_;
v___y_1326_ = v___y_1297_;
v___y_1327_ = v___y_1298_;
v___y_1328_ = v___y_1299_;
goto v___jp_1320_;
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_val_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_snd_1408_);
lean_dec(v_fst_1407_);
lean_del_object(v___x_1405_);
lean_dec(v_a_1399_);
lean_del_object(v___x_1317_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1466_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1413_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1413_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
else
{
lean_object* v_snd_1475_; 
lean_del_object(v___x_1405_);
lean_dec(v_snd_1315_);
v_snd_1475_ = lean_ctor_get(v_snd_1403_, 1);
lean_inc(v_snd_1475_);
lean_dec(v_snd_1403_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
v___y_1321_ = v_snd_1475_;
v___y_1322_ = v_a_1399_;
v___y_1323_ = v___y_1294_;
v___y_1324_ = v___y_1295_;
v___y_1325_ = v___y_1296_;
v___y_1326_ = v___y_1297_;
v___y_1327_ = v___y_1298_;
v___y_1328_ = v___y_1299_;
goto v___jp_1320_;
}
}
}
else
{
lean_object* v_term_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec(v_a_1401_);
lean_del_object(v___x_1317_);
v_term_1478_ = lean_ctor_get(v_a_1319_, 1);
v___x_1479_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7);
v___x_1480_ = l_Lean_indentExpr(v_a_1399_);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
lean_inc_ref(v___y_1298_);
lean_inc_ref(v___y_1294_);
v___x_1482_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_1478_, v___x_1481_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v___x_1483_; 
lean_dec_ref(v___x_1482_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_fst_1314_);
lean_ctor_set(v___x_1483_, 1, v_snd_1315_);
v_a_1302_ = v___x_1483_;
goto v___jp_1301_;
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_snd_1315_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1484_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1482_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1482_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_a_1399_);
lean_del_object(v___x_1317_);
lean_dec(v_snd_1315_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1492_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1400_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1400_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_del_object(v___x_1317_);
lean_dec(v_snd_1315_);
lean_dec(v_fst_1314_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_a_1500_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1398_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1398_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
v___jp_1301_:
{
size_t v___x_1303_; size_t v___x_1304_; 
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_add(v_i_1292_, v___x_1303_);
v_i_1292_ = v___x_1304_;
v_b_1293_ = v_a_1302_;
goto _start;
}
v___jp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_a_1308_);
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___y_1307_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v_a_1302_ = v___x_1311_;
goto v___jp_1301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___boxed(lean_object* v_as_1532_, lean_object* v_sz_1533_, lean_object* v_i_1534_, lean_object* v_b_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
size_t v_sz_boxed_1543_; size_t v_i_boxed_1544_; lean_object* v_res_1545_; 
v_sz_boxed_1543_ = lean_unbox_usize(v_sz_1533_);
lean_dec(v_sz_1533_);
v_i_boxed_1544_ = lean_unbox_usize(v_i_1534_);
lean_dec(v_i_1534_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_as_1532_, v_sz_boxed_1543_, v_i_boxed_1544_, v_b_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec_ref(v_as_1532_);
return v_res_1545_;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabCalcSteps___closed__4(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1551_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__3));
v___x_1552_ = lean_unsigned_to_nat(14u);
v___x_1553_ = lean_unsigned_to_nat(22u);
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__2));
v___x_1555_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__1));
v___x_1556_ = l_mkPanicMessageWithDecl(v___x_1555_, v___x_1554_, v___x_1553_, v___x_1552_, v___x_1551_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object* v_steps_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v___x_1565_; size_t v_sz_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1565_ = ((lean_object*)(l_Lean_Elab_Term_elabCalcSteps___closed__0));
v_sz_1566_ = lean_array_size(v_steps_1557_);
v___x_1567_ = ((size_t)0ULL);
lean_inc(v_a_1563_);
lean_inc_ref(v_a_1562_);
lean_inc(v_a_1561_);
lean_inc_ref(v_a_1560_);
lean_inc(v_a_1559_);
lean_inc_ref(v_a_1558_);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_steps_1557_, v_sz_1566_, v___x_1567_, v___x_1565_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1584_; 
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v___x_1570_, 0);
lean_dec(v_unused_1585_);
v___x_1572_ = v___x_1570_;
v_isShared_1573_ = v_isSharedCheck_1584_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v___x_1570_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1584_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_fst_1574_; 
v_fst_1574_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_fst_1574_);
lean_dec(v_a_1569_);
if (lean_obj_tag(v_fst_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1575_ = lean_obj_once(&l_Lean_Elab_Term_elabCalcSteps___closed__4, &l_Lean_Elab_Term_elabCalcSteps___closed__4_once, _init_l_Lean_Elab_Term_elabCalcSteps___closed__4);
v___x_1576_ = l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(v___x_1575_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1576_);
v___x_1578_ = v___x_1572_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
else
{
lean_object* v_val_1580_; lean_object* v___x_1582_; 
v_val_1580_ = lean_ctor_get(v_fst_1574_, 0);
lean_inc(v_val_1580_);
lean_dec_ref(v_fst_1574_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_val_1580_);
v___x_1582_ = v___x_1572_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_val_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_a_1569_);
v_a_1586_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1570_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1570_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
v_a_1594_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1568_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1568_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps___boxed(lean_object* v_steps_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Elab_Term_elabCalcSteps(v_steps_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec_ref(v_steps_1602_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(lean_object* v_00_u03b1_1611_, lean_object* v_ref_1612_, lean_object* v_msg_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_ref_1612_, v_msg_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___boxed(lean_object* v_00_u03b1_1622_, lean_object* v_ref_1623_, lean_object* v_msg_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(v_00_u03b1_1622_, v_ref_1623_, v_msg_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec(v_ref_1623_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(lean_object* v_00_u03b1_1633_, lean_object* v_msg_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_msg_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(v_00_u03b1_1643_, v_msg_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(lean_object* v_msgData_1653_, lean_object* v_macroStack_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_1653_, v_macroStack_1654_, v___y_1659_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1663_, lean_object* v_macroStack_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(v_msgData_1663_, v_macroStack_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1672_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = lean_box(0);
v___x_1674_ = l_Lean_Elab_abortTermExceptionId;
v___x_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v___x_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg(){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0);
v___x_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___boxed(lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(lean_object* v_00_u03b1_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___boxed(lean_object* v_00_u03b1_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(v_00_u03b1_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(lean_object* v_msg_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___f_1701_; lean_object* v___x_6544__overap_1702_; lean_object* v___x_1703_; 
v___f_1701_ = ((lean_object*)(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0));
v___x_6544__overap_1702_ = lean_panic_fn(v___f_1701_, v_msg_1695_);
v___x_1703_ = lean_apply_5(v___x_6544__overap_1702_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, lean_box(0));
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg___boxed(lean_object* v_msg_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(lean_object* v_00_u03b1_1711_, lean_object* v_msg_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v_msg_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_msg_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(v_00_u03b1_1719_, v_msg_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(uint8_t v___y_1734_, uint8_t v_suppressElabErrors_1735_, lean_object* v_x_1736_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 1)
{
lean_object* v_pre_1737_; 
v_pre_1737_ = lean_ctor_get(v_x_1736_, 0);
switch(lean_obj_tag(v_pre_1737_))
{
case 1:
{
lean_object* v_pre_1738_; 
v_pre_1738_ = lean_ctor_get(v_pre_1737_, 0);
switch(lean_obj_tag(v_pre_1738_))
{
case 0:
{
lean_object* v_str_1739_; lean_object* v_str_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v_str_1739_ = lean_ctor_get(v_x_1736_, 1);
v_str_1740_ = lean_ctor_get(v_pre_1737_, 1);
v___x_1741_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13));
v___x_1742_ = lean_string_dec_eq(v_str_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0));
v___x_1744_ = lean_string_dec_eq(v_str_1740_, v___x_1743_);
if (v___x_1744_ == 0)
{
return v___y_1734_;
}
else
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1));
v___x_1746_ = lean_string_dec_eq(v_str_1739_, v___x_1745_);
if (v___x_1746_ == 0)
{
return v___y_1734_;
}
else
{
return v_suppressElabErrors_1735_;
}
}
}
else
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2));
v___x_1748_ = lean_string_dec_eq(v_str_1739_, v___x_1747_);
if (v___x_1748_ == 0)
{
return v___y_1734_;
}
else
{
return v_suppressElabErrors_1735_;
}
}
}
case 1:
{
lean_object* v_pre_1749_; 
v_pre_1749_ = lean_ctor_get(v_pre_1738_, 0);
if (lean_obj_tag(v_pre_1749_) == 0)
{
lean_object* v_str_1750_; lean_object* v_str_1751_; lean_object* v_str_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_str_1750_ = lean_ctor_get(v_x_1736_, 1);
v_str_1751_ = lean_ctor_get(v_pre_1737_, 1);
v_str_1752_ = lean_ctor_get(v_pre_1738_, 1);
v___x_1753_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3));
v___x_1754_ = lean_string_dec_eq(v_str_1752_, v___x_1753_);
if (v___x_1754_ == 0)
{
return v___y_1734_;
}
else
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4));
v___x_1756_ = lean_string_dec_eq(v_str_1751_, v___x_1755_);
if (v___x_1756_ == 0)
{
return v___y_1734_;
}
else
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5));
v___x_1758_ = lean_string_dec_eq(v_str_1750_, v___x_1757_);
if (v___x_1758_ == 0)
{
return v___y_1734_;
}
else
{
return v_suppressElabErrors_1735_;
}
}
}
}
else
{
return v___y_1734_;
}
}
default: 
{
return v___y_1734_;
}
}
}
case 0:
{
lean_object* v_str_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_str_1759_ = lean_ctor_get(v_x_1736_, 1);
v___x_1760_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6));
v___x_1761_ = lean_string_dec_eq(v_str_1759_, v___x_1760_);
if (v___x_1761_ == 0)
{
return v___y_1734_;
}
else
{
return v_suppressElabErrors_1735_;
}
}
default: 
{
return v___y_1734_;
}
}
}
else
{
return v___y_1734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed(lean_object* v___y_1762_, lean_object* v_suppressElabErrors_1763_, lean_object* v_x_1764_){
_start:
{
uint8_t v___y_8931__boxed_1765_; uint8_t v_suppressElabErrors_boxed_1766_; uint8_t v_res_1767_; lean_object* v_r_1768_; 
v___y_8931__boxed_1765_ = lean_unbox(v___y_1762_);
v_suppressElabErrors_boxed_1766_ = lean_unbox(v_suppressElabErrors_1763_);
v_res_1767_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(v___y_8931__boxed_1765_, v_suppressElabErrors_boxed_1766_, v_x_1764_);
lean_dec(v_x_1764_);
v_r_1768_ = lean_box(v_res_1767_);
return v_r_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(lean_object* v_ref_1769_, lean_object* v_msgData_1770_, uint8_t v_severity_1771_, uint8_t v_isSilent_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
uint8_t v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; uint8_t v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1815_; uint8_t v___y_1816_; uint8_t v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; uint8_t v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1840_; uint8_t v___y_1841_; uint8_t v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1851_; uint8_t v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; uint8_t v___y_1856_; uint8_t v___y_1857_; uint8_t v___x_1862_; lean_object* v___y_1864_; uint8_t v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; uint8_t v___y_1869_; uint8_t v___y_1870_; uint8_t v___y_1872_; uint8_t v___x_1887_; 
v___x_1862_ = 2;
v___x_1887_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1771_, v___x_1862_);
if (v___x_1887_ == 0)
{
v___y_1872_ = v___x_1887_;
goto v___jp_1871_;
}
else
{
uint8_t v___x_1888_; 
lean_inc_ref(v_msgData_1770_);
v___x_1888_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1770_);
v___y_1872_ = v___x_1888_;
goto v___jp_1871_;
}
v___jp_1778_:
{
lean_object* v___x_1788_; lean_object* v_currNamespace_1789_; lean_object* v_openDecls_1790_; lean_object* v_env_1791_; lean_object* v_nextMacroScope_1792_; lean_object* v_ngen_1793_; lean_object* v_auxDeclNGen_1794_; lean_object* v_traceState_1795_; lean_object* v_cache_1796_; lean_object* v_messages_1797_; lean_object* v_infoState_1798_; lean_object* v_snapshotTasks_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1813_; 
v___x_1788_ = lean_st_ref_take(v___y_1787_);
v_currNamespace_1789_ = lean_ctor_get(v___y_1786_, 6);
lean_inc(v_currNamespace_1789_);
v_openDecls_1790_ = lean_ctor_get(v___y_1786_, 7);
lean_inc(v_openDecls_1790_);
lean_dec_ref(v___y_1786_);
v_env_1791_ = lean_ctor_get(v___x_1788_, 0);
v_nextMacroScope_1792_ = lean_ctor_get(v___x_1788_, 1);
v_ngen_1793_ = lean_ctor_get(v___x_1788_, 2);
v_auxDeclNGen_1794_ = lean_ctor_get(v___x_1788_, 3);
v_traceState_1795_ = lean_ctor_get(v___x_1788_, 4);
v_cache_1796_ = lean_ctor_get(v___x_1788_, 5);
v_messages_1797_ = lean_ctor_get(v___x_1788_, 6);
v_infoState_1798_ = lean_ctor_get(v___x_1788_, 7);
v_snapshotTasks_1799_ = lean_ctor_get(v___x_1788_, 8);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1801_ = v___x_1788_;
v_isShared_1802_ = v_isSharedCheck_1813_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snapshotTasks_1799_);
lean_inc(v_infoState_1798_);
lean_inc(v_messages_1797_);
lean_inc(v_cache_1796_);
lean_inc(v_traceState_1795_);
lean_inc(v_auxDeclNGen_1794_);
lean_inc(v_ngen_1793_);
lean_inc(v_nextMacroScope_1792_);
lean_inc(v_env_1791_);
lean_dec(v___x_1788_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1813_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v_currNamespace_1789_);
lean_ctor_set(v___x_1803_, 1, v_openDecls_1790_);
v___x_1804_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___y_1782_);
v___x_1805_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1805_, 0, v___y_1781_);
lean_ctor_set(v___x_1805_, 1, v___y_1780_);
lean_ctor_set(v___x_1805_, 2, v___y_1785_);
lean_ctor_set(v___x_1805_, 3, v___y_1783_);
lean_ctor_set(v___x_1805_, 4, v___x_1804_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*5, v___y_1784_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*5 + 1, v___y_1779_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*5 + 2, v_isSilent_1772_);
v___x_1806_ = l_Lean_MessageLog_add(v___x_1805_, v_messages_1797_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 6, v___x_1806_);
v___x_1808_ = v___x_1801_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_env_1791_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_nextMacroScope_1792_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_ngen_1793_);
lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_auxDeclNGen_1794_);
lean_ctor_set(v_reuseFailAlloc_1812_, 4, v_traceState_1795_);
lean_ctor_set(v_reuseFailAlloc_1812_, 5, v_cache_1796_);
lean_ctor_set(v_reuseFailAlloc_1812_, 6, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1812_, 7, v_infoState_1798_);
lean_ctor_set(v_reuseFailAlloc_1812_, 8, v_snapshotTasks_1799_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = lean_st_ref_set(v___y_1787_, v___x_1808_);
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
}
v___jp_1814_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1838_; 
v___x_1823_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1770_);
v___x_1824_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v___x_1823_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1838_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1838_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_inc_ref(v___y_1819_);
v___x_1829_ = l_Lean_FileMap_toPosition(v___y_1819_, v___y_1821_);
lean_dec(v___y_1821_);
v___x_1830_ = l_Lean_FileMap_toPosition(v___y_1819_, v___y_1822_);
lean_dec(v___y_1822_);
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11));
if (v___y_1817_ == 0)
{
lean_del_object(v___x_1827_);
lean_dec_ref(v___y_1815_);
v___y_1779_ = v___y_1816_;
v___y_1780_ = v___x_1829_;
v___y_1781_ = v___y_1818_;
v___y_1782_ = v_a_1825_;
v___y_1783_ = v___x_1832_;
v___y_1784_ = v___y_1820_;
v___y_1785_ = v___x_1831_;
v___y_1786_ = v___y_1775_;
v___y_1787_ = v___y_1776_;
goto v___jp_1778_;
}
else
{
uint8_t v___x_1833_; 
lean_inc(v_a_1825_);
v___x_1833_ = l_Lean_MessageData_hasTag(v___y_1815_, v_a_1825_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_dec_ref(v___x_1831_);
lean_dec_ref(v___x_1829_);
lean_dec(v_a_1825_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v___y_1775_);
v___x_1834_ = lean_box(0);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1834_);
v___x_1836_ = v___x_1827_;
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
lean_del_object(v___x_1827_);
v___y_1779_ = v___y_1816_;
v___y_1780_ = v___x_1829_;
v___y_1781_ = v___y_1818_;
v___y_1782_ = v_a_1825_;
v___y_1783_ = v___x_1832_;
v___y_1784_ = v___y_1820_;
v___y_1785_ = v___x_1831_;
v___y_1786_ = v___y_1775_;
v___y_1787_ = v___y_1776_;
goto v___jp_1778_;
}
}
}
}
v___jp_1839_:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Syntax_getTailPos_x3f(v___y_1845_, v___y_1846_);
lean_dec(v___y_1845_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_inc(v___y_1847_);
v___y_1815_ = v___y_1840_;
v___y_1816_ = v___y_1841_;
v___y_1817_ = v___y_1842_;
v___y_1818_ = v___y_1843_;
v___y_1819_ = v___y_1844_;
v___y_1820_ = v___y_1846_;
v___y_1821_ = v___y_1847_;
v___y_1822_ = v___y_1847_;
goto v___jp_1814_;
}
else
{
lean_object* v_val_1849_; 
v_val_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_val_1849_);
lean_dec_ref(v___x_1848_);
v___y_1815_ = v___y_1840_;
v___y_1816_ = v___y_1841_;
v___y_1817_ = v___y_1842_;
v___y_1818_ = v___y_1843_;
v___y_1819_ = v___y_1844_;
v___y_1820_ = v___y_1846_;
v___y_1821_ = v___y_1847_;
v___y_1822_ = v_val_1849_;
goto v___jp_1814_;
}
}
v___jp_1850_:
{
lean_object* v_ref_1858_; lean_object* v___x_1859_; 
v_ref_1858_ = l_Lean_replaceRef(v_ref_1769_, v___y_1853_);
lean_dec(v___y_1853_);
v___x_1859_ = l_Lean_Syntax_getPos_x3f(v_ref_1858_, v___y_1856_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___y_1840_ = v___y_1851_;
v___y_1841_ = v___y_1857_;
v___y_1842_ = v___y_1852_;
v___y_1843_ = v___y_1854_;
v___y_1844_ = v___y_1855_;
v___y_1845_ = v_ref_1858_;
v___y_1846_ = v___y_1856_;
v___y_1847_ = v___x_1860_;
goto v___jp_1839_;
}
else
{
lean_object* v_val_1861_; 
v_val_1861_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_val_1861_);
lean_dec_ref(v___x_1859_);
v___y_1840_ = v___y_1851_;
v___y_1841_ = v___y_1857_;
v___y_1842_ = v___y_1852_;
v___y_1843_ = v___y_1854_;
v___y_1844_ = v___y_1855_;
v___y_1845_ = v_ref_1858_;
v___y_1846_ = v___y_1856_;
v___y_1847_ = v_val_1861_;
goto v___jp_1839_;
}
}
v___jp_1863_:
{
if (v___y_1870_ == 0)
{
v___y_1851_ = v___y_1868_;
v___y_1852_ = v___y_1865_;
v___y_1853_ = v___y_1864_;
v___y_1854_ = v___y_1866_;
v___y_1855_ = v___y_1867_;
v___y_1856_ = v___y_1869_;
v___y_1857_ = v_severity_1771_;
goto v___jp_1850_;
}
else
{
v___y_1851_ = v___y_1868_;
v___y_1852_ = v___y_1865_;
v___y_1853_ = v___y_1864_;
v___y_1854_ = v___y_1866_;
v___y_1855_ = v___y_1867_;
v___y_1856_ = v___y_1869_;
v___y_1857_ = v___x_1862_;
goto v___jp_1850_;
}
}
v___jp_1871_:
{
if (v___y_1872_ == 0)
{
lean_object* v_fileName_1873_; lean_object* v_fileMap_1874_; lean_object* v_options_1875_; lean_object* v_ref_1876_; uint8_t v_suppressElabErrors_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___f_1880_; uint8_t v___x_1881_; uint8_t v___x_1882_; 
v_fileName_1873_ = lean_ctor_get(v___y_1775_, 0);
v_fileMap_1874_ = lean_ctor_get(v___y_1775_, 1);
v_options_1875_ = lean_ctor_get(v___y_1775_, 2);
v_ref_1876_ = lean_ctor_get(v___y_1775_, 5);
v_suppressElabErrors_1877_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*14 + 1);
v___x_1878_ = lean_box(v___y_1872_);
v___x_1879_ = lean_box(v_suppressElabErrors_1877_);
v___f_1880_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1880_, 0, v___x_1878_);
lean_closure_set(v___f_1880_, 1, v___x_1879_);
v___x_1881_ = 1;
v___x_1882_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1771_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_inc_ref(v_fileMap_1874_);
lean_inc_ref(v_fileName_1873_);
lean_inc(v_ref_1876_);
v___y_1864_ = v_ref_1876_;
v___y_1865_ = v_suppressElabErrors_1877_;
v___y_1866_ = v_fileName_1873_;
v___y_1867_ = v_fileMap_1874_;
v___y_1868_ = v___f_1880_;
v___y_1869_ = v___y_1872_;
v___y_1870_ = v___x_1882_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = l_Lean_warningAsError;
v___x_1884_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_options_1875_, v___x_1883_);
lean_inc_ref(v_fileMap_1874_);
lean_inc_ref(v_fileName_1873_);
lean_inc(v_ref_1876_);
v___y_1864_ = v_ref_1876_;
v___y_1865_ = v_suppressElabErrors_1877_;
v___y_1866_ = v_fileName_1873_;
v___y_1867_ = v_fileMap_1874_;
v___y_1868_ = v___f_1880_;
v___y_1869_ = v___y_1872_;
v___y_1870_ = v___x_1884_;
goto v___jp_1863_;
}
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_msgData_1770_);
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___boxed(lean_object* v_ref_1889_, lean_object* v_msgData_1890_, lean_object* v_severity_1891_, lean_object* v_isSilent_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
uint8_t v_severity_boxed_1898_; uint8_t v_isSilent_boxed_1899_; lean_object* v_res_1900_; 
v_severity_boxed_1898_ = lean_unbox(v_severity_1891_);
v_isSilent_boxed_1899_ = lean_unbox(v_isSilent_1892_);
v_res_1900_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1889_, v_msgData_1890_, v_severity_boxed_1898_, v_isSilent_boxed_1899_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v_ref_1889_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(lean_object* v_ref_1901_, lean_object* v_msgData_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
uint8_t v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = 2;
v___x_1909_ = 0;
v___x_1910_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_1901_, v_msgData_1902_, v___x_1908_, v___x_1909_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1___boxed(lean_object* v_ref_1911_, lean_object* v_msgData_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_ref_1911_, v_msgData_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v_ref_1911_);
return v_res_1918_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1));
v___x_1923_ = l_Lean_MessageData_ofFormat(v___x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2);
v___x_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4));
v___x_1928_ = l_Lean_stringToMessageData(v___x_1927_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6));
v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1933_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__10));
v___x_1934_ = lean_unsigned_to_nat(57u);
v___x_1935_ = lean_unsigned_to_nat(133u);
v___x_1936_ = ((lean_object*)(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8));
v___x_1937_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcTrans___closed__8));
v___x_1938_ = l_mkPanicMessageWithDecl(v___x_1937_, v___x_1936_, v___x_1935_, v___x_1934_, v___x_1933_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object* v_steps_1939_, lean_object* v_expectedType_1940_, lean_object* v_result_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; 
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
lean_inc_ref(v_result_1941_);
v___x_1947_ = lean_infer_type(v_result_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v_a_1950_; lean_object* v___x_1951_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___x_1974_; lean_object* v_a_1975_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_1948_, v_a_1943_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = l_Lean_Expr_headBeta(v_a_1950_);
v___x_1974_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_1951_);
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref(v___x_1974_);
if (lean_obj_tag(v_a_1975_) == 1)
{
lean_object* v_val_1976_; lean_object* v_snd_1977_; lean_object* v_fst_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2224_; 
v_val_1976_ = lean_ctor_get(v_a_1975_, 0);
lean_inc(v_val_1976_);
lean_dec_ref(v_a_1975_);
v_snd_1977_ = lean_ctor_get(v_val_1976_, 1);
v_fst_1978_ = lean_ctor_get(v_val_1976_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_val_1976_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_1980_ = v_val_1976_;
v_isShared_1981_ = v_isSharedCheck_2224_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_snd_1977_);
lean_inc(v_fst_1978_);
lean_dec(v_val_1976_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2224_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_fst_1982_; lean_object* v_snd_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2223_; 
v_fst_1982_ = lean_ctor_get(v_snd_1977_, 0);
v_snd_1983_ = lean_ctor_get(v_snd_1977_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_snd_1977_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_1985_ = v_snd_1977_;
v_isShared_1986_ = v_isSharedCheck_2223_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snd_1983_);
lean_inc(v_fst_1982_);
lean_dec(v_snd_1977_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2223_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v_a_1988_; 
v___x_1987_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_expectedType_1940_);
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref(v___x_1987_);
if (lean_obj_tag(v_a_1988_) == 1)
{
lean_object* v_val_1989_; lean_object* v_snd_1990_; lean_object* v_fst_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2222_; 
v_val_1989_ = lean_ctor_get(v_a_1988_, 0);
lean_inc(v_val_1989_);
lean_dec_ref(v_a_1988_);
v_snd_1990_ = lean_ctor_get(v_val_1989_, 1);
v_fst_1991_ = lean_ctor_get(v_val_1989_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_val_1989_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_1993_ = v_val_1989_;
v_isShared_1994_ = v_isSharedCheck_2222_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_snd_1990_);
lean_inc(v_fst_1991_);
lean_dec(v_val_1989_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2222_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_fst_1995_; lean_object* v_snd_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2221_; 
v_fst_1995_ = lean_ctor_get(v_snd_1990_, 0);
v_snd_1996_ = lean_ctor_get(v_snd_1990_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_snd_1990_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_1998_ = v_snd_1990_;
v_isShared_1999_ = v_isSharedCheck_2221_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_snd_1996_);
lean_inc(v_fst_1995_);
lean_dec(v_snd_1990_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2221_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
uint8_t v_failed_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___x_2112_; 
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2112_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1978_, v_fst_1991_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; uint8_t v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2112_);
v___x_2114_ = lean_unbox(v_a_2113_);
if (v___x_2114_ == 0)
{
lean_dec(v_a_2113_);
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_dec(v_fst_1995_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_dec(v_fst_1982_);
lean_del_object(v___x_1980_);
v___y_1953_ = v_a_1942_;
v___y_1954_ = v_a_1943_;
v___y_1955_ = v_a_1944_;
v___y_1956_ = v_a_1945_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_2115_; 
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
lean_inc(v_fst_1995_);
lean_inc(v_fst_1982_);
v___x_2115_ = l_Lean_Meta_isExprDefEqGuarded(v_fst_1982_, v_fst_1995_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; uint8_t v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = lean_unbox(v_a_2116_);
lean_dec(v_a_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2118_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_1982_, v_fst_1995_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v_fst_2120_; lean_object* v_snd_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2195_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2118_);
v_fst_2120_ = lean_ctor_get(v_a_2119_, 0);
v_snd_2121_ = lean_ctor_get(v_a_2119_, 1);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_a_2119_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2123_ = v_a_2119_;
v_isShared_2124_ = v_isSharedCheck_2195_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_snd_2121_);
lean_inc(v_fst_2120_);
lean_dec(v_a_2119_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2195_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; 
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
lean_inc(v_fst_2120_);
v___x_2125_ = lean_infer_type(v_fst_2120_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref(v___x_2125_);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
lean_inc(v_snd_2121_);
v___x_2127_ = lean_infer_type(v_snd_2121_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
lean_inc(v_a_1945_);
lean_inc_ref(v_a_1944_);
lean_inc(v_a_1943_);
lean_inc_ref(v_a_1942_);
v___x_2129_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2126_, v_a_2128_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v_fst_2131_; lean_object* v_snd_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2170_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
v_fst_2131_ = lean_ctor_get(v_a_2130_, 0);
v_snd_2132_ = lean_ctor_get(v_a_2130_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_a_2130_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2134_ = v_a_2130_;
v_isShared_2135_ = v_isSharedCheck_2170_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_snd_2132_);
lean_inc(v_fst_2131_);
lean_dec(v_a_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2170_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_term_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2136_ = ((lean_object*)(l_Lean_Elab_Term_instInhabitedCalcStepView_default));
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_array_get_borrowed(v___x_2136_, v_steps_1939_, v___x_2137_);
v_term_2139_ = lean_ctor_get(v___x_2138_, 1);
v___x_2140_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
v___x_2141_ = l_Lean_MessageData_ofExpr(v_fst_2120_);
v___x_2142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 7);
lean_ctor_set(v___x_2134_, 1, v___x_2142_);
lean_ctor_set(v___x_2134_, 0, v___x_2141_);
v___x_2144_ = v___x_2134_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2145_ = l_Lean_MessageData_ofExpr(v_fst_2131_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set_tag(v___x_2123_, 7);
lean_ctor_set(v___x_2123_, 1, v___x_2145_);
lean_ctor_set(v___x_2123_, 0, v___x_2144_);
v___x_2147_ = v___x_2123_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2148_ = l_Lean_indentD(v___x_2147_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2140_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
v___x_2151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_Lean_MessageData_ofExpr(v_snd_2121_);
v___x_2153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v___x_2142_);
v___x_2154_ = l_Lean_MessageData_ofExpr(v_snd_2132_);
v___x_2155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = l_Lean_indentD(v___x_2155_);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2151_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
lean_inc_ref(v_a_1944_);
v___x_2158_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2139_, v___x_2157_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_2158_) == 0)
{
uint8_t v___x_2159_; 
lean_dec_ref(v___x_2158_);
v___x_2159_ = lean_unbox(v_a_2113_);
lean_dec(v_a_2113_);
v_failed_2001_ = v___x_2159_;
v___y_2002_ = v_a_1942_;
v___y_2003_ = v_a_1943_;
v___y_2004_ = v_a_1944_;
v___y_2005_ = v_a_1945_;
goto v___jp_2000_;
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_a_2113_);
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_del_object(v___x_1980_);
lean_dec_ref(v___x_1951_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v_a_2160_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2158_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2158_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_del_object(v___x_2123_);
lean_dec(v_snd_2121_);
lean_dec(v_fst_2120_);
lean_dec(v_a_2113_);
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_del_object(v___x_1980_);
lean_dec_ref(v___x_1951_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v_a_2171_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2129_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2129_);
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
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_a_2126_);
lean_del_object(v___x_2123_);
lean_dec(v_snd_2121_);
lean_dec(v_fst_2120_);
lean_dec(v_a_2113_);
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_del_object(v___x_1980_);
lean_dec_ref(v___x_1951_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v_a_2179_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2127_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2127_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_del_object(v___x_2123_);
lean_dec(v_snd_2121_);
lean_dec(v_fst_2120_);
lean_dec(v_a_2113_);
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_del_object(v___x_1980_);
lean_dec_ref(v___x_1951_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v_a_2187_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2125_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2125_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec(v_a_2113_);
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_del_object(v___x_1980_);
lean_dec_ref(v___x_1951_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v_a_2196_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2118_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2118_);
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
else
{
uint8_t v___x_2204_; 
lean_dec(v_a_2113_);
lean_dec(v_fst_1995_);
lean_dec(v_fst_1982_);
v___x_2204_ = 0;
v_failed_2001_ = v___x_2204_;
v___y_2002_ = v_a_1942_;
v___y_2003_ = v_a_1943_;
v___y_2004_ = v_a_1944_;
v___y_2005_ = v_a_1945_;
goto v___jp_2000_;
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2113_);
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_dec(v_fst_1995_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_dec(v_fst_1982_);
lean_del_object(v___x_1980_);
lean_dec_ref(v___x_1951_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v_a_2205_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2115_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2115_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_dec(v_fst_1995_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_dec(v_fst_1982_);
lean_del_object(v___x_1980_);
lean_dec_ref(v___x_1951_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v_a_2213_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2112_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2112_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
v___jp_2000_:
{
lean_object* v___x_2006_; 
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v_snd_1996_);
lean_inc(v_snd_1983_);
v___x_2006_ = l_Lean_Meta_isExprDefEqGuarded(v_snd_1983_, v_snd_1996_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; uint8_t v___x_2008_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2006_);
v___x_2008_ = lean_unbox(v_a_2007_);
lean_dec(v_a_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec_ref(v___x_1951_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
v___x_2009_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_snd_1983_, v_snd_1996_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2095_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_2009_);
v_fst_2011_ = lean_ctor_get(v_a_2010_, 0);
v_snd_2012_ = lean_ctor_get(v_a_2010_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_a_2010_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2014_ = v_a_2010_;
v_isShared_2015_ = v_isSharedCheck_2095_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_snd_2012_);
lean_inc(v_fst_2011_);
lean_dec(v_a_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2095_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; 
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v_fst_2011_);
v___x_2016_ = lean_infer_type(v_fst_2011_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref(v___x_2016_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v_snd_2012_);
v___x_2018_ = lean_infer_type(v_snd_2012_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_2018_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
v___x_2020_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_2017_, v_a_2019_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v_fst_2022_; lean_object* v_snd_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2070_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
v_fst_2022_ = lean_ctor_get(v_a_2021_, 0);
v_snd_2023_ = lean_ctor_get(v_a_2021_, 1);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_a_2021_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2025_ = v_a_2021_;
v_isShared_2026_ = v_isSharedCheck_2070_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_snd_2023_);
lean_inc(v_fst_2022_);
lean_dec(v_a_2021_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2070_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v_term_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2027_ = ((lean_object*)(l_Lean_Elab_Term_instInhabitedCalcStepView_default));
v___x_2028_ = lean_array_get_size(v_steps_1939_);
v___x_2029_ = lean_unsigned_to_nat(1u);
v___x_2030_ = lean_nat_sub(v___x_2028_, v___x_2029_);
v___x_2031_ = lean_array_get_borrowed(v___x_2027_, v_steps_1939_, v___x_2030_);
lean_dec(v___x_2030_);
v_term_2032_ = lean_ctor_get(v___x_2031_, 1);
v___x_2033_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5);
v___x_2034_ = l_Lean_MessageData_ofExpr(v_fst_2011_);
v___x_2035_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
if (v_isShared_2026_ == 0)
{
lean_ctor_set_tag(v___x_2025_, 7);
lean_ctor_set(v___x_2025_, 1, v___x_2035_);
lean_ctor_set(v___x_2025_, 0, v___x_2034_);
v___x_2037_ = v___x_2025_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = l_Lean_MessageData_ofExpr(v_fst_2022_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 7);
lean_ctor_set(v___x_2014_, 1, v___x_2038_);
lean_ctor_set(v___x_2014_, 0, v___x_2037_);
v___x_2040_ = v___x_2014_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2041_ = l_Lean_indentD(v___x_2040_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 7);
lean_ctor_set(v___x_1998_, 1, v___x_2041_);
lean_ctor_set(v___x_1998_, 0, v___x_2033_);
v___x_2043_ = v___x_1998_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2044_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7);
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 7);
lean_ctor_set(v___x_1993_, 1, v___x_2044_);
lean_ctor_set(v___x_1993_, 0, v___x_2043_);
v___x_2046_ = v___x_1993_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = l_Lean_MessageData_ofExpr(v_snd_2012_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 7);
lean_ctor_set(v___x_1985_, 1, v___x_2035_);
lean_ctor_set(v___x_1985_, 0, v___x_2047_);
v___x_2049_ = v___x_1985_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2035_);
v___x_2049_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2050_ = l_Lean_MessageData_ofExpr(v_snd_2023_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 7);
lean_ctor_set(v___x_1980_, 1, v___x_2050_);
lean_ctor_set(v___x_1980_, 0, v___x_2049_);
v___x_2052_ = v___x_1980_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = l_Lean_indentD(v___x_2052_);
v___x_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2046_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_inc_ref(v___y_2004_);
v___x_2055_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(v_term_2032_, v___x_2054_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref(v___x_2055_);
v___y_1961_ = v___y_2002_;
v___y_1962_ = v___y_2003_;
v___y_1963_ = v___y_2004_;
v___y_1964_ = v___y_2005_;
goto v___jp_1960_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_del_object(v___x_2014_);
lean_dec(v_snd_2012_);
lean_dec(v_fst_2011_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_del_object(v___x_1998_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_del_object(v___x_1980_);
v_a_2071_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2020_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2020_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_a_2017_);
lean_del_object(v___x_2014_);
lean_dec(v_snd_2012_);
lean_dec(v_fst_2011_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_del_object(v___x_1998_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_del_object(v___x_1980_);
v_a_2079_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2018_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2018_);
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
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_del_object(v___x_2014_);
lean_dec(v_snd_2012_);
lean_dec(v_fst_2011_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_del_object(v___x_1998_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_del_object(v___x_1980_);
v_a_2087_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2016_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2016_);
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
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_del_object(v___x_1998_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_del_object(v___x_1980_);
v_a_2096_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2009_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2009_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_del_object(v___x_1980_);
if (v_failed_2001_ == 0)
{
v___y_1953_ = v___y_2002_;
v___y_1954_ = v___y_2003_;
v___y_1955_ = v___y_2004_;
v___y_1956_ = v___y_2005_;
goto v___jp_1952_;
}
else
{
lean_dec_ref(v___x_1951_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v___y_1961_ = v___y_2002_;
v___y_1962_ = v___y_2003_;
v___y_1963_ = v___y_2004_;
v___y_1964_ = v___y_2005_;
goto v___jp_1960_;
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_del_object(v___x_1998_);
lean_dec(v_snd_1996_);
lean_del_object(v___x_1993_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_del_object(v___x_1980_);
lean_dec_ref(v___x_1951_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v_a_2104_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2006_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2006_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1988_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_dec(v_fst_1982_);
lean_del_object(v___x_1980_);
lean_dec(v_fst_1978_);
v___y_1953_ = v_a_1942_;
v___y_1954_ = v_a_1943_;
v___y_1955_ = v_a_1944_;
v___y_1956_ = v_a_1945_;
goto v___jp_1952_;
}
}
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v_a_1975_);
lean_dec_ref(v___x_1951_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v___x_2225_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9);
v___x_2226_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(v___x_2225_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_2226_;
}
v___jp_1952_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_obj_once(&l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3, &l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once, _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3);
v___x_1958_ = lean_box(0);
v___x_1959_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1957_, v_expectedType_1940_, v___x_1951_, v_result_1941_, v___x_1958_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
return v___x_1959_;
}
v___jp_1960_:
{
lean_object* v___x_1965_; lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
v___x_1965_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_result_1941_);
lean_dec_ref(v_expectedType_1940_);
v_a_2227_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_1947_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_1947_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(lean_object* v_steps_2235_, lean_object* v_expectedType_2236_, lean_object* v_result_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2235_, v_expectedType_2236_, v_result_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
lean_dec_ref(v_steps_2235_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure(lean_object* v_00_u03b1_2244_, lean_object* v_steps_2245_, lean_object* v_expectedType_2246_, lean_object* v_result_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_steps_2245_, v_expectedType_2246_, v_result_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___boxed(lean_object* v_00_u03b1_2254_, lean_object* v_steps_2255_, lean_object* v_expectedType_2256_, lean_object* v_result_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Elab_Term_throwCalcFailure(v_00_u03b1_2254_, v_steps_2255_, v_expectedType_2256_, v_result_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_steps_2255_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0(lean_object* v_a_2264_, lean_object* v_x_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2264_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0___boxed(lean_object* v_a_2274_, lean_object* v_x_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Elab_Term_elabCalc___lam__0(v_a_2274_, v_x_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v_x_2275_);
lean_dec_ref(v_a_2274_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1(lean_object* v_a_2284_, lean_object* v_x_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_2284_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1___boxed(lean_object* v_a_2294_, lean_object* v_x_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Elab_Term_elabCalc___lam__1(v_a_2294_, v_x_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v_x_2295_);
lean_dec_ref(v_a_2294_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object* v_x_2308_, lean_object* v_x_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
lean_inc(v_x_2308_);
v___x_2318_ = l_Lean_Syntax_isOfKind(v_x_2308_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; 
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_x_2309_);
lean_dec(v_x_2308_);
v___x_2319_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2319_;
}
else
{
lean_object* v___x_2320_; lean_object* v_steps_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2320_ = lean_unsigned_to_nat(1u);
v_steps_2321_ = l_Lean_Syntax_getArg(v_x_2308_, v___x_2320_);
v___x_2322_ = ((lean_object*)(l_Lean_Elab_Term_mkCalcStepViews___closed__1));
lean_inc(v_steps_2321_);
v___x_2323_ = l_Lean_Syntax_isOfKind(v_steps_2321_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; 
lean_dec(v_steps_2321_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_x_2309_);
lean_dec(v_x_2308_);
v___x_2324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
return v___x_2324_;
}
else
{
lean_object* v_fileName_2325_; lean_object* v_fileMap_2326_; lean_object* v_options_2327_; lean_object* v_currRecDepth_2328_; lean_object* v_maxRecDepth_2329_; lean_object* v_ref_2330_; lean_object* v_currNamespace_2331_; lean_object* v_openDecls_2332_; lean_object* v_initHeartbeats_2333_; lean_object* v_maxHeartbeats_2334_; lean_object* v_quotContext_2335_; lean_object* v_currMacroScope_2336_; uint8_t v_diag_2337_; lean_object* v_cancelTk_x3f_2338_; uint8_t v_suppressElabErrors_2339_; lean_object* v_inheritedTraceOptions_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2374_; 
v_fileName_2325_ = lean_ctor_get(v_a_2314_, 0);
v_fileMap_2326_ = lean_ctor_get(v_a_2314_, 1);
v_options_2327_ = lean_ctor_get(v_a_2314_, 2);
v_currRecDepth_2328_ = lean_ctor_get(v_a_2314_, 3);
v_maxRecDepth_2329_ = lean_ctor_get(v_a_2314_, 4);
v_ref_2330_ = lean_ctor_get(v_a_2314_, 5);
v_currNamespace_2331_ = lean_ctor_get(v_a_2314_, 6);
v_openDecls_2332_ = lean_ctor_get(v_a_2314_, 7);
v_initHeartbeats_2333_ = lean_ctor_get(v_a_2314_, 8);
v_maxHeartbeats_2334_ = lean_ctor_get(v_a_2314_, 9);
v_quotContext_2335_ = lean_ctor_get(v_a_2314_, 10);
v_currMacroScope_2336_ = lean_ctor_get(v_a_2314_, 11);
v_diag_2337_ = lean_ctor_get_uint8(v_a_2314_, sizeof(void*)*14);
v_cancelTk_x3f_2338_ = lean_ctor_get(v_a_2314_, 12);
v_suppressElabErrors_2339_ = lean_ctor_get_uint8(v_a_2314_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2340_ = lean_ctor_get(v_a_2314_, 13);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_a_2314_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2342_ = v_a_2314_;
v_isShared_2343_ = v_isSharedCheck_2374_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_inheritedTraceOptions_2340_);
lean_inc(v_cancelTk_x3f_2338_);
lean_inc(v_currMacroScope_2336_);
lean_inc(v_quotContext_2335_);
lean_inc(v_maxHeartbeats_2334_);
lean_inc(v_initHeartbeats_2333_);
lean_inc(v_openDecls_2332_);
lean_inc(v_currNamespace_2331_);
lean_inc(v_ref_2330_);
lean_inc(v_maxRecDepth_2329_);
lean_inc(v_currRecDepth_2328_);
lean_inc(v_options_2327_);
lean_inc(v_fileMap_2326_);
lean_inc(v_fileName_2325_);
lean_dec(v_a_2314_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2374_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v_tk_2345_; lean_object* v_ref_2346_; lean_object* v___x_2348_; 
v___x_2344_ = lean_unsigned_to_nat(0u);
v_tk_2345_ = l_Lean_Syntax_getArg(v_x_2308_, v___x_2344_);
lean_dec(v_x_2308_);
v_ref_2346_ = l_Lean_replaceRef(v_tk_2345_, v_ref_2330_);
lean_dec(v_ref_2330_);
lean_dec(v_tk_2345_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 5, v_ref_2346_);
v___x_2348_ = v___x_2342_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_fileName_2325_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_fileMap_2326_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_options_2327_);
lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_currRecDepth_2328_);
lean_ctor_set(v_reuseFailAlloc_2373_, 4, v_maxRecDepth_2329_);
lean_ctor_set(v_reuseFailAlloc_2373_, 5, v_ref_2346_);
lean_ctor_set(v_reuseFailAlloc_2373_, 6, v_currNamespace_2331_);
lean_ctor_set(v_reuseFailAlloc_2373_, 7, v_openDecls_2332_);
lean_ctor_set(v_reuseFailAlloc_2373_, 8, v_initHeartbeats_2333_);
lean_ctor_set(v_reuseFailAlloc_2373_, 9, v_maxHeartbeats_2334_);
lean_ctor_set(v_reuseFailAlloc_2373_, 10, v_quotContext_2335_);
lean_ctor_set(v_reuseFailAlloc_2373_, 11, v_currMacroScope_2336_);
lean_ctor_set(v_reuseFailAlloc_2373_, 12, v_cancelTk_x3f_2338_);
lean_ctor_set(v_reuseFailAlloc_2373_, 13, v_inheritedTraceOptions_2340_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*14, v_diag_2337_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*14 + 1, v_suppressElabErrors_2339_);
v___x_2348_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; 
lean_inc_ref(v___x_2348_);
v___x_2349_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_2321_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v___x_2348_, v_a_2315_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
lean_inc(v_a_2315_);
lean_inc_ref(v___x_2348_);
lean_inc(v_a_2313_);
lean_inc_ref(v_a_2312_);
lean_inc(v_a_2311_);
lean_inc_ref(v_a_2310_);
v___x_2351_ = l_Lean_Elab_Term_elabCalcSteps(v_a_2350_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v___x_2348_, v_a_2315_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v_fst_2353_; lean_object* v___f_2354_; lean_object* v___f_2355_; lean_object* v___x_2356_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref(v___x_2351_);
v_fst_2353_ = lean_ctor_get(v_a_2352_, 0);
lean_inc(v_fst_2353_);
lean_dec(v_a_2352_);
lean_inc(v_a_2350_);
v___f_2354_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2354_, 0, v_a_2350_);
v___f_2355_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__1___boxed), 9, 1);
lean_closure_set(v___f_2355_, 0, v_a_2350_);
v___x_2356_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(v_x_2309_, v_fst_2353_, v___f_2354_, v___f_2355_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v___x_2348_, v_a_2315_);
return v___x_2356_;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2350_);
lean_dec_ref(v___x_2348_);
lean_dec(v_a_2315_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_x_2309_);
v_a_2357_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2351_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2351_);
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
lean_dec_ref(v___x_2348_);
lean_dec(v_a_2315_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_x_2309_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object* v_x_2375_, lean_object* v_x_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Elab_Term_elabCalc(v_x_2375_, v_x_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1(){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2392_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2393_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___closed__1));
v___x_2394_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2395_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___boxed), 9, 0);
v___x_2396_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2392_, v___x_2393_, v___x_2394_, v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___boxed(lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3(){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2402_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0));
v___x_2403_ = l_Lean_addBuiltinDocString(v___x_2401_, v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___boxed(lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5(){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1));
v___x_2433_ = ((lean_object*)(l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6));
v___x_2434_ = l_Lean_addBuiltinDeclarationRanges(v___x_2432_, v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___boxed(lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
return v_res_2436_;
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
res = l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
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
