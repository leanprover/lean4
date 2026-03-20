// Lean compiler output
// Module: Lean.Meta.Tactic.AC.Main
// Imports: public import Lean.Meta.Tactic.Refl public import Lean.Meta.Tactic.Simp.Main public import Lean.Elab.Tactic.Rewrite import Init.Omega
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_AC_mergeIdem(lean_object*);
lean_object* l_Lean_Data_AC_Expr_toList(lean_object*);
lean_object* l_Lean_Data_AC_sort(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Meta_AC_instInhabitedPreContext_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_AC_instInhabitedPreContext_default___closed__0 = (const lean_object*)&l_Lean_Meta_AC_instInhabitedPreContext_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_AC_instInhabitedPreContext_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_instInhabitedPreContext_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_AC_instInhabitedPreContext_default___closed__1 = (const lean_object*)&l_Lean_Meta_AC_instInhabitedPreContext_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2;
static lean_once_cell_t l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instInhabitedPreContext_default;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instInhabitedPreContext;
LEAN_EXPORT uint8_t l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__0 = (const lean_object*)&l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__0_value;
static const lean_closure_object l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__1 = (const lean_object*)&l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__1_value;
static const lean_closure_object l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__2 = (const lean_object*)&l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__2_value;
static const lean_ctor_object l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__2_value),((lean_object*)&l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__0_value),((lean_object*)&l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__1_value)}};
static const lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__3 = (const lean_object*)&l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool = (const lean_object*)&l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__3_value;
static const lean_ctor_object l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__0 = (const lean_object*)&l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__0_value;
static const lean_closure_object l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__1 = (const lean_object*)&l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__1_value;
static const lean_closure_object l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__2 = (const lean_object*)&l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__0_value),((lean_object*)&l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__1_value),((lean_object*)&l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__2_value)}};
static const lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__3 = (const lean_object*)&l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr = (const lean_object*)&l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__3_value;
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_getInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "got instance"};
static const lean_object* l_Lean_Meta_AC_getInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_AC_getInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_AC_getInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_getInstance___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_getInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_AC_getInstance___closed__0 = (const lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value;
static const lean_string_object l_Lean_Meta_AC_getInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AC"};
static const lean_object* l_Lean_Meta_AC_getInstance___closed__1 = (const lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value;
static const lean_ctor_object l_Lean_Meta_AC_getInstance___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_AC_getInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_getInstance___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 102, 180, 37, 89, 238, 212, 46)}};
static const lean_object* l_Lean_Meta_AC_getInstance___closed__2 = (const lean_object*)&l_Lean_Meta_AC_getInstance___closed__2_value;
static const lean_string_object l_Lean_Meta_AC_getInstance___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "trying: "};
static const lean_object* l_Lean_Meta_AC_getInstance___closed__3 = (const lean_object*)&l_Lean_Meta_AC_getInstance___closed__3_value;
static lean_once_cell_t l_Lean_Meta_AC_getInstance___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_getInstance___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_preContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_AC_preContext___closed__0 = (const lean_object*)&l_Lean_Meta_AC_preContext___closed__0_value;
static const lean_string_object l_Lean_Meta_AC_preContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Associative"};
static const lean_object* l_Lean_Meta_AC_preContext___closed__1 = (const lean_object*)&l_Lean_Meta_AC_preContext___closed__1_value;
static const lean_ctor_object l_Lean_Meta_AC_preContext___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_preContext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_AC_preContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_preContext___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_AC_preContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 251, 219, 24, 41, 141, 182, 243)}};
static const lean_object* l_Lean_Meta_AC_preContext___closed__2 = (const lean_object*)&l_Lean_Meta_AC_preContext___closed__2_value;
static const lean_string_object l_Lean_Meta_AC_preContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Commutative"};
static const lean_object* l_Lean_Meta_AC_preContext___closed__3 = (const lean_object*)&l_Lean_Meta_AC_preContext___closed__3_value;
static const lean_ctor_object l_Lean_Meta_AC_preContext___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_preContext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_AC_preContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_preContext___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_AC_preContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(106, 96, 18, 51, 62, 235, 64, 3)}};
static const lean_object* l_Lean_Meta_AC_preContext___closed__4 = (const lean_object*)&l_Lean_Meta_AC_preContext___closed__4_value;
static const lean_string_object l_Lean_Meta_AC_preContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "IdempotentOp"};
static const lean_object* l_Lean_Meta_AC_preContext___closed__5 = (const lean_object*)&l_Lean_Meta_AC_preContext___closed__5_value;
static const lean_ctor_object l_Lean_Meta_AC_preContext___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_preContext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_AC_preContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_preContext___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_AC_preContext___closed__5_value),LEAN_SCALAR_PTR_LITERAL(245, 219, 239, 145, 216, 232, 46, 228)}};
static const lean_object* l_Lean_Meta_AC_preContext___closed__6 = (const lean_object*)&l_Lean_Meta_AC_preContext___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_preContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_preContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_op_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_op_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_bin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_AC_toACExpr_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_AC_toACExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_toACExpr___closed__0;
static lean_once_cell_t l_Lean_Meta_AC_toACExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_toACExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LawfulIdentity"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_preContext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 22, 200, 99, 71, 159, 239, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_AC_abstractAtoms___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_AC_abstractAtoms___closed__0 = (const lean_object*)&l_Lean_Meta_AC_abstractAtoms___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_abstractAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_abstractAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PLift"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(199, 82, 227, 164, 10, 97, 128, 84)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Data"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Variable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(177, 67, 69, 230, 180, 62, 221, 131)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 163, 62, 223, 32, 165, 80, 222)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(146, 85, 23, 54, 227, 224, 149, 53)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(82, 172, 4, 99, 128, 254, 208, 227)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "up"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(199, 82, 227, 164, 10, 97, 128, 84)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(211, 38, 67, 163, 37, 91, 68, 134)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(177, 67, 69, 230, 180, 62, 221, 131)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 163, 62, 223, 32, 165, 80, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(146, 85, 23, 54, 227, 224, 149, 53)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Context"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(177, 67, 69, 230, 180, 62, 221, 131)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 163, 62, 223, 32, 165, 80, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 35, 224, 244, 170, 201, 45, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(188, 94, 192, 225, 248, 86, 206, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(177, 67, 69, 230, 180, 62, 221, 131)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 163, 62, 223, 32, 165, 80, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 183, 150, 226, 41, 85, 126, 57)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(61, 113, 133, 93, 37, 32, 75, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "op"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(177, 67, 69, 230, 180, 62, 221, 131)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 163, 62, 223, 32, 165, 80, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 183, 150, 226, 41, 85, 126, 57)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__4_value),LEAN_SCALAR_PTR_LITERAL(65, 217, 52, 98, 170, 249, 224, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_AC_buildNormProof___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_of_norm"};
static const lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(177, 67, 69, 230, 180, 62, 221, 131)}};
static const lean_ctor_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 163, 62, 223, 32, 165, 80, 222)}};
static const lean_ctor_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 35, 224, 244, 170, 201, 45, 1)}};
static const lean_ctor_object l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(150, 46, 99, 133, 28, 84, 99, 127)}};
static const lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_buildNormProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_AC_buildNormProof___closed__0 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___closed__0_value;
static const lean_ctor_object l_Lean_Meta_AC_buildNormProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_buildNormProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_AC_buildNormProof___closed__1 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___closed__1_value;
static const lean_string_object l_Lean_Meta_AC_buildNormProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Meta.Tactic.AC.Main"};
static const lean_object* l_Lean_Meta_AC_buildNormProof___closed__2 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___closed__2_value;
static const lean_string_object l_Lean_Meta_AC_buildNormProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.AC.buildNormProof"};
static const lean_object* l_Lean_Meta_AC_buildNormProof___closed__3 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___closed__3_value;
static const lean_string_object l_Lean_Meta_AC_buildNormProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected proof type"};
static const lean_object* l_Lean_Meta_AC_buildNormProof___closed__4 = (const lean_object*)&l_Lean_Meta_AC_buildNormProof___closed__4_value;
static lean_once_cell_t l_Lean_Meta_AC_buildNormProof___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_buildNormProof___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_AC_rewriteUnnormalized___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__0 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__0_value;
static const lean_closure_object l_Lean_Meta_AC_rewriteUnnormalized___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_rewriteUnnormalized___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__1 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__1_value;
static const lean_closure_object l_Lean_Meta_AC_rewriteUnnormalized___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_rewriteUnnormalized___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__2 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__2_value;
static const lean_closure_object l_Lean_Meta_AC_rewriteUnnormalized___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_rewriteUnnormalized___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__3 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__3_value;
static const lean_closure_object l_Lean_Meta_AC_rewriteUnnormalized___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_rewriteUnnormalized___lam__3___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__4 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__4_value;
static lean_once_cell_t l_Lean_Meta_AC_rewriteUnnormalized___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__5;
static lean_once_cell_t l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__6;
static lean_once_cell_t l_Lean_Meta_AC_rewriteUnnormalized___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__7;
static lean_once_cell_t l_Lean_Meta_AC_rewriteUnnormalized___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__8;
static lean_once_cell_t l_Lean_Meta_AC_rewriteUnnormalized___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__9;
static lean_once_cell_t l_Lean_Meta_AC_rewriteUnnormalized___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__10;
static lean_once_cell_t l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__11;
static const lean_closure_object l_Lean_Meta_AC_rewriteUnnormalized___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_post___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__12 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__12_value;
static const lean_ctor_object l_Lean_Meta_AC_rewriteUnnormalized___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 8, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__1_value),((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__12_value),((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__2_value),((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__3_value),((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__4_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__13 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value;
static const lean_string_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value;
static const lean_string_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "acRfl"};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2_value;
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 10, 210, 32, 196, 152, 20, 107)}};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value;
static const lean_string_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "acRflTactic"};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4_value;
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 50, 124, 4, 240, 103, 254, 60)}};
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 10, 211, 220, 137, 99, 157, 23)}};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(176) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2_value),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6 = (const lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_AC_acNfTargetTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_acNfTargetTactic___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_acNfTargetTactic___closed__0 = (const lean_object*)&l_Lean_Meta_AC_acNfTargetTactic___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_evalNf0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "acNf0"};
static const lean_object* l_Lean_Meta_AC_evalNf0___closed__0 = (const lean_object*)&l_Lean_Meta_AC_evalNf0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_evalNf0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_evalNf0___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_evalNf0___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_AC_evalNf0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 212, 39, 12, 162, 76, 172, 19)}};
static const lean_object* l_Lean_Meta_AC_evalNf0___closed__1 = (const lean_object*)&l_Lean_Meta_AC_evalNf0___closed__1_value;
static const lean_array_object l_Lean_Meta_AC_evalNf0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_AC_evalNf0___closed__2 = (const lean_object*)&l_Lean_Meta_AC_evalNf0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalNf0"};
static const lean_object* l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0 = (const lean_object*)&l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 50, 124, 4, 240, 103, 254, 60)}};
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 59, 59, 44, 240, 219, 207, 54)}};
static const lean_object* l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1 = (const lean_object*)&l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(28, 111, 207, 116, 89, 15, 82, 211)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 49, 252, 61, 32, 200, 184, 234)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(116, 91, 192, 92, 6, 101, 182, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 248, 126, 6, 203, 150, 165, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 240, 157, 130, 31, 26, 156, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 20, 105, 199, 19, 240, 24, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 13, 232, 254, 123, 0, 230, 165)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 103, 11, 232, 42, 82, 90, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 185, 207, 121, 5, 34, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 192, 238, 212, 45, 149, 167, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(146, 225, 162, 38, 239, 104, 56, 82)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 54, 152, 170, 137, 28, 225, 176)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 48, 206, 168, 183, 177, 173, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_AC_instInhabitedPreContext_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_box(0);
v___x_8_ = lean_obj_once(&l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2, &l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2_once, _init_l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v___x_7_);
lean_ctor_set(v___x_10_, 4, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_AC_instInhabitedPreContext_default(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3, &l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3_once, _init_l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Meta_AC_instInhabitedPreContext(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_AC_instInhabitedPreContext_default;
return v___x_12_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0(lean_object* v_ctx_13_){
_start:
{
lean_object* v_fst_14_; lean_object* v_comm_15_; 
v_fst_14_ = lean_ctor_get(v_ctx_13_, 0);
v_comm_15_ = lean_ctor_get(v_fst_14_, 3);
if (lean_obj_tag(v_comm_15_) == 0)
{
uint8_t v___x_16_; 
v___x_16_ = 0;
return v___x_16_;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = 1;
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0___boxed(lean_object* v_ctx_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0(v_ctx_18_);
lean_dec_ref(v_ctx_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1(lean_object* v_ctx_21_){
_start:
{
lean_object* v_fst_22_; lean_object* v_idem_23_; 
v_fst_22_ = lean_ctor_get(v_ctx_21_, 0);
v_idem_23_ = lean_ctor_get(v_fst_22_, 4);
if (lean_obj_tag(v_idem_23_) == 0)
{
uint8_t v___x_24_; 
v___x_24_ = 0;
return v___x_24_;
}
else
{
uint8_t v___x_25_; 
v___x_25_ = 1;
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1___boxed(lean_object* v_ctx_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1(v_ctx_26_);
lean_dec_ref(v_ctx_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2(uint8_t v___x_29_, lean_object* v_ctx_30_, lean_object* v_x_31_){
_start:
{
lean_object* v_snd_32_; lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_snd_32_ = lean_ctor_get(v_ctx_30_, 1);
v___x_33_ = lean_box(v___x_29_);
v___x_34_ = lean_array_get_borrowed(v___x_33_, v_snd_32_, v_x_31_);
v___x_35_ = lean_unbox(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2___boxed(lean_object* v___x_36_, lean_object* v_ctx_37_, lean_object* v_x_38_){
_start:
{
uint8_t v___x_53__boxed_39_; uint8_t v_res_40_; lean_object* v_r_41_; 
v___x_53__boxed_39_ = lean_unbox(v___x_36_);
v_res_40_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2(v___x_53__boxed_39_, v_ctx_37_, v_x_38_);
lean_dec(v_x_38_);
lean_dec_ref(v_ctx_37_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0(lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0));
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___boxed(lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0(v_x_56_);
lean_dec_ref(v_x_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1(lean_object* v_x_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___y_59_);
lean_ctor_set(v___x_61_, 1, v___y_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1___boxed(lean_object* v_x_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1(v_x_62_, v___y_63_, v___y_64_);
lean_dec_ref(v_x_62_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v_x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2___boxed(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2(v_x_69_, v_x_70_);
lean_dec_ref(v_x_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg(lean_object* v_cls_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_options_86_; uint8_t v_hasTrace_87_; 
v_options_86_ = lean_ctor_get(v___y_84_, 2);
v_hasTrace_87_ = lean_ctor_get_uint8(v_options_86_, sizeof(void*)*1);
if (v_hasTrace_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_cls_83_);
v___x_88_ = lean_box(v_hasTrace_87_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
else
{
lean_object* v_inheritedTraceOptions_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_inheritedTraceOptions_90_ = lean_ctor_get(v___y_84_, 13);
v___x_91_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___closed__1));
v___x_92_ = l_Lean_Name_append(v___x_91_, v_cls_83_);
v___x_93_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_90_, v_options_86_, v___x_92_);
lean_dec(v___x_92_);
v___x_94_ = lean_box(v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg___boxed(lean_object* v_cls_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg(v_cls_96_, v___y_97_);
lean_dec_ref(v___y_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0(lean_object* v_cls_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg(v_cls_100_, v___y_103_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___boxed(lean_object* v_cls_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0(v_cls_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1_spec__1(lean_object* v_msgData_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1_spec__1___boxed(lean_object* v_msgData_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1_spec__1(v_msgData_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_135_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__0(void){
_start:
{
lean_object* v___x_136_; double v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_float_of_nat(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1(lean_object* v_cls_141_, lean_object* v_msg_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_ref_148_; lean_object* v___x_149_; lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_194_; 
v_ref_148_ = lean_ctor_get(v___y_145_, 5);
v___x_149_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1_spec__1(v_msg_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_194_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_194_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_194_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v_traceState_155_; lean_object* v_env_156_; lean_object* v_nextMacroScope_157_; lean_object* v_ngen_158_; lean_object* v_auxDeclNGen_159_; lean_object* v_cache_160_; lean_object* v_messages_161_; lean_object* v_infoState_162_; lean_object* v_snapshotTasks_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_193_; 
v___x_154_ = lean_st_ref_take(v___y_146_);
v_traceState_155_ = lean_ctor_get(v___x_154_, 4);
v_env_156_ = lean_ctor_get(v___x_154_, 0);
v_nextMacroScope_157_ = lean_ctor_get(v___x_154_, 1);
v_ngen_158_ = lean_ctor_get(v___x_154_, 2);
v_auxDeclNGen_159_ = lean_ctor_get(v___x_154_, 3);
v_cache_160_ = lean_ctor_get(v___x_154_, 5);
v_messages_161_ = lean_ctor_get(v___x_154_, 6);
v_infoState_162_ = lean_ctor_get(v___x_154_, 7);
v_snapshotTasks_163_ = lean_ctor_get(v___x_154_, 8);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_193_ == 0)
{
v___x_165_ = v___x_154_;
v_isShared_166_ = v_isSharedCheck_193_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_snapshotTasks_163_);
lean_inc(v_infoState_162_);
lean_inc(v_messages_161_);
lean_inc(v_cache_160_);
lean_inc(v_traceState_155_);
lean_inc(v_auxDeclNGen_159_);
lean_inc(v_ngen_158_);
lean_inc(v_nextMacroScope_157_);
lean_inc(v_env_156_);
lean_dec(v___x_154_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_193_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
uint64_t v_tid_167_; lean_object* v_traces_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_192_; 
v_tid_167_ = lean_ctor_get_uint64(v_traceState_155_, sizeof(void*)*1);
v_traces_168_ = lean_ctor_get(v_traceState_155_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v_traceState_155_);
if (v_isSharedCheck_192_ == 0)
{
v___x_170_ = v_traceState_155_;
v_isShared_171_ = v_isSharedCheck_192_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_traces_168_);
lean_dec(v_traceState_155_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_192_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; double v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_172_ = lean_box(0);
v___x_173_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__0);
v___x_174_ = 0;
v___x_175_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__1));
v___x_176_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_176_, 0, v_cls_141_);
lean_ctor_set(v___x_176_, 1, v___x_172_);
lean_ctor_set(v___x_176_, 2, v___x_175_);
lean_ctor_set_float(v___x_176_, sizeof(void*)*3, v___x_173_);
lean_ctor_set_float(v___x_176_, sizeof(void*)*3 + 8, v___x_173_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*3 + 16, v___x_174_);
v___x_177_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___closed__2));
v___x_178_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v_a_150_);
lean_ctor_set(v___x_178_, 2, v___x_177_);
lean_inc(v_ref_148_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_ref_148_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = l_Lean_PersistentArray_push___redArg(v_traces_168_, v___x_179_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_180_);
v___x_182_ = v___x_170_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_180_);
lean_ctor_set_uint64(v_reuseFailAlloc_191_, sizeof(void*)*1, v_tid_167_);
v___x_182_ = v_reuseFailAlloc_191_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 4, v___x_182_);
v___x_184_ = v___x_165_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_env_156_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_nextMacroScope_157_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_ngen_158_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v_auxDeclNGen_159_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_190_, 5, v_cache_160_);
lean_ctor_set(v_reuseFailAlloc_190_, 6, v_messages_161_);
lean_ctor_set(v_reuseFailAlloc_190_, 7, v_infoState_162_);
lean_ctor_set(v_reuseFailAlloc_190_, 8, v_snapshotTasks_163_);
v___x_184_ = v_reuseFailAlloc_190_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_185_ = lean_st_ref_set(v___y_146_, v___x_184_);
v___x_186_ = lean_box(0);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_186_);
v___x_188_ = v___x_152_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1___boxed(lean_object* v_cls_195_, lean_object* v_msg_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1(v_cls_195_, v_msg_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v_res_202_;
}
}
static lean_object* _init_l_Lean_Meta_AC_getInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___lam__0___closed__0));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___lam__0(lean_object* v_a_206_, lean_object* v___x_207_, lean_object* v_____r_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_box(0);
lean_inc(v___y_212_);
lean_inc_ref(v___y_211_);
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
v___x_215_ = l_Lean_Meta_synthInstance(v_a_206_, v___x_214_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_239_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_239_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_239_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_239_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_226_; lean_object* v_a_227_; uint8_t v___x_228_; 
lean_inc(v___x_207_);
v___x_226_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg(v___x_207_, v___y_211_);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v___x_228_ = lean_unbox(v_a_227_);
lean_dec(v_a_227_);
if (v___x_228_ == 0)
{
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___x_207_);
goto v___jp_220_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_obj_once(&l_Lean_Meta_AC_getInstance___lam__0___closed__1, &l_Lean_Meta_AC_getInstance___lam__0___closed__1_once, _init_l_Lean_Meta_AC_getInstance___lam__0___closed__1);
v___x_230_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1(v___x_207_, v___x_229_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_dec_ref(v___x_230_);
goto v___jp_220_;
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_del_object(v___x_218_);
lean_dec(v_a_216_);
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
v___jp_220_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_a_216_);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_222_);
v___x_224_ = v___x_218_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___x_207_);
v_a_240_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_215_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_215_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___lam__0___boxed(lean_object* v_a_248_, lean_object* v___x_249_, lean_object* v_____r_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_248_, v___x_249_, v_____r_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
return v_res_256_;
}
}
static lean_object* _init_l_Lean_Meta_AC_getInstance___closed__4(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__3));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance(lean_object* v_cls_265_, lean_object* v_exprs_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___y_273_; uint8_t v___y_274_; lean_object* v_a_279_; lean_object* v___y_283_; lean_object* v___x_294_; 
lean_inc(v_a_270_);
lean_inc_ref(v_a_269_);
lean_inc(v_a_268_);
lean_inc_ref(v_a_267_);
v___x_294_ = l_Lean_Meta_mkAppM(v_cls_265_, v_exprs_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_a_298_; uint8_t v___x_299_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref(v___x_294_);
v___x_296_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__2));
v___x_297_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_AC_getInstance_spec__0___redArg(v___x_296_, v_a_269_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref(v___x_297_);
v___x_299_ = lean_unbox(v_a_298_);
lean_dec(v_a_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_box(0);
v___x_301_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_295_, v___x_296_, v___x_300_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
v___y_283_ = v___x_301_;
goto v___jp_282_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = lean_obj_once(&l_Lean_Meta_AC_getInstance___closed__4, &l_Lean_Meta_AC_getInstance___closed__4_once, _init_l_Lean_Meta_AC_getInstance___closed__4);
lean_inc(v_a_295_);
v___x_303_ = l_Lean_indentExpr(v_a_295_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__1(v___x_296_, v___x_304_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_307_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref(v___x_305_);
v___x_307_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_295_, v___x_296_, v_a_306_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
v___y_283_ = v___x_307_;
goto v___jp_282_;
}
else
{
lean_object* v_a_308_; 
lean_dec(v_a_295_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
v_a_308_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_305_);
v_a_279_ = v_a_308_;
goto v___jp_278_;
}
}
}
else
{
lean_object* v_a_309_; 
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
v_a_309_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_294_);
v_a_279_ = v_a_309_;
goto v___jp_278_;
}
v___jp_272_:
{
if (v___y_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec_ref(v___y_273_);
v___x_275_ = lean_box(0);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v___y_273_);
return v___x_277_;
}
}
v___jp_278_:
{
uint8_t v___x_280_; 
v___x_280_ = l_Lean_Exception_isInterrupt(v_a_279_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; 
lean_inc_ref(v_a_279_);
v___x_281_ = l_Lean_Exception_isRuntime(v_a_279_);
v___y_273_ = v_a_279_;
v___y_274_ = v___x_281_;
goto v___jp_272_;
}
else
{
v___y_273_ = v_a_279_;
v___y_274_ = v___x_280_;
goto v___jp_272_;
}
}
v___jp_282_:
{
if (lean_obj_tag(v___y_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_292_; 
v_a_284_ = lean_ctor_get(v___y_283_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___y_283_);
if (v_isSharedCheck_292_ == 0)
{
v___x_286_ = v___y_283_;
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___y_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_a_288_; lean_object* v___x_290_; 
v_a_288_ = lean_ctor_get(v_a_284_, 0);
lean_inc(v_a_288_);
lean_dec(v_a_284_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v_a_288_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v_a_293_; 
v_a_293_ = lean_ctor_get(v___y_283_, 0);
lean_inc(v_a_293_);
lean_dec_ref(v___y_283_);
v_a_279_ = v_a_293_;
goto v___jp_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___boxed(lean_object* v_cls_310_, lean_object* v_exprs_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_AC_getInstance(v_cls_310_, v_exprs_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_preContext(lean_object* v_expr_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_337_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__2));
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
lean_inc_ref(v_expr_331_);
v___x_340_ = lean_array_push(v___x_339_, v_expr_331_);
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc_ref(v___x_340_);
v___x_341_ = l_Lean_Meta_AC_getInstance(v___x_337_, v___x_340_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_389_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_389_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_389_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_389_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
if (lean_obj_tag(v_a_342_) == 1)
{
lean_object* v_val_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_384_; 
lean_del_object(v___x_344_);
v_val_346_ = lean_ctor_get(v_a_342_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_342_);
if (v_isSharedCheck_384_ == 0)
{
v___x_348_ = v_a_342_;
v_isShared_349_ = v_isSharedCheck_384_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_val_346_);
lean_dec(v_a_342_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_384_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__4));
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc_ref(v___x_340_);
v___x_351_ = l_Lean_Meta_AC_getInstance(v___x_350_, v___x_340_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref(v___x_351_);
v___x_353_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__6));
v___x_354_ = l_Lean_Meta_AC_getInstance(v___x_353_, v___x_340_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_367_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_367_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v_expr_331_);
lean_ctor_set(v___x_360_, 2, v_val_346_);
lean_ctor_set(v___x_360_, 3, v_a_352_);
lean_ctor_set(v___x_360_, 4, v_a_355_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_360_);
v___x_362_ = v___x_348_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_366_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_364_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_362_);
v___x_364_ = v___x_357_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_a_352_);
lean_del_object(v___x_348_);
lean_dec(v_val_346_);
lean_dec_ref(v_expr_331_);
v_a_368_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_354_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_354_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_del_object(v___x_348_);
lean_dec(v_val_346_);
lean_dec_ref(v___x_340_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_expr_331_);
v_a_376_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_351_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_351_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
else
{
lean_object* v___x_385_; lean_object* v___x_387_; 
lean_dec(v_a_342_);
lean_dec_ref(v___x_340_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_expr_331_);
v___x_385_ = lean_box(0);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_385_);
v___x_387_ = v___x_344_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v___x_340_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_expr_331_);
v_a_390_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_341_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_341_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_preContext___boxed(lean_object* v_expr_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_AC_preContext(v_expr_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx(lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_object* v___x_406_; 
v___x_406_ = lean_unsigned_to_nat(0u);
return v___x_406_;
}
else
{
lean_object* v___x_407_; 
v___x_407_ = lean_unsigned_to_nat(1u);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx___boxed(lean_object* v_x_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_AC_PreExpr_ctorIdx(v_x_408_);
lean_dec_ref(v_x_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim___redArg(lean_object* v_t_410_, lean_object* v_k_411_){
_start:
{
if (lean_obj_tag(v_t_410_) == 0)
{
lean_object* v_lhs_412_; lean_object* v_rhs_413_; lean_object* v___x_414_; 
v_lhs_412_ = lean_ctor_get(v_t_410_, 0);
lean_inc_ref(v_lhs_412_);
v_rhs_413_ = lean_ctor_get(v_t_410_, 1);
lean_inc_ref(v_rhs_413_);
lean_dec_ref(v_t_410_);
v___x_414_ = lean_apply_2(v_k_411_, v_lhs_412_, v_rhs_413_);
return v___x_414_;
}
else
{
lean_object* v_e_415_; lean_object* v___x_416_; 
v_e_415_ = lean_ctor_get(v_t_410_, 0);
lean_inc_ref(v_e_415_);
lean_dec_ref(v_t_410_);
v___x_416_ = lean_apply_1(v_k_411_, v_e_415_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim(lean_object* v_motive_417_, lean_object* v_ctorIdx_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_k_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_419_, v_k_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim___boxed(lean_object* v_motive_423_, lean_object* v_ctorIdx_424_, lean_object* v_t_425_, lean_object* v_h_426_, lean_object* v_k_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_AC_PreExpr_ctorElim(v_motive_423_, v_ctorIdx_424_, v_t_425_, v_h_426_, v_k_427_);
lean_dec(v_ctorIdx_424_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_op_elim___redArg(lean_object* v_t_429_, lean_object* v_op_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_429_, v_op_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_op_elim(lean_object* v_motive_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_op_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_433_, v_op_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_var_elim___redArg(lean_object* v_t_437_, lean_object* v_var_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_437_, v_var_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_var_elim(lean_object* v_motive_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_var_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_441_, v_var_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_bin(lean_object* v_op_445_, lean_object* v_l_446_, lean_object* v_r_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = l_Lean_Expr_app___override(v_op_445_, v_l_446_);
v___x_449_ = l_Lean_Expr_app___override(v___x_448_, v_r_447_);
return v___x_449_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
else
{
lean_object* v_key_453_; lean_object* v_tail_454_; uint8_t v___x_455_; 
v_key_453_ = lean_ctor_get(v_x_451_, 0);
v_tail_454_ = lean_ctor_get(v_x_451_, 2);
v___x_455_ = lean_expr_eqv(v_key_453_, v_a_450_);
if (v___x_455_ == 0)
{
v_x_451_ = v_tail_454_;
goto _start;
}
else
{
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg___boxed(lean_object* v_a_457_, lean_object* v_x_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_457_, v_x_458_);
lean_dec(v_x_458_);
lean_dec_ref(v_a_457_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
return v_x_461_;
}
else
{
lean_object* v_key_463_; lean_object* v_value_464_; lean_object* v_tail_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_488_; 
v_key_463_ = lean_ctor_get(v_x_462_, 0);
v_value_464_ = lean_ctor_get(v_x_462_, 1);
v_tail_465_ = lean_ctor_get(v_x_462_, 2);
v_isSharedCheck_488_ = !lean_is_exclusive(v_x_462_);
if (v_isSharedCheck_488_ == 0)
{
v___x_467_ = v_x_462_;
v_isShared_468_ = v_isSharedCheck_488_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_tail_465_);
lean_inc(v_value_464_);
lean_inc(v_key_463_);
lean_dec(v_x_462_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_488_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v_fold_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_469_ = lean_array_get_size(v_x_461_);
v___x_470_ = l_Lean_Expr_hash(v_key_463_);
v___x_471_ = 32ULL;
v___x_472_ = lean_uint64_shift_right(v___x_470_, v___x_471_);
v_fold_473_ = lean_uint64_xor(v___x_470_, v___x_472_);
v___x_474_ = 16ULL;
v___x_475_ = lean_uint64_shift_right(v_fold_473_, v___x_474_);
v___x_476_ = lean_uint64_xor(v_fold_473_, v___x_475_);
v___x_477_ = lean_uint64_to_usize(v___x_476_);
v___x_478_ = lean_usize_of_nat(v___x_469_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_sub(v___x_478_, v___x_479_);
v___x_481_ = lean_usize_land(v___x_477_, v___x_480_);
v___x_482_ = lean_array_uget_borrowed(v_x_461_, v___x_481_);
lean_inc(v___x_482_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 2, v___x_482_);
v___x_484_ = v___x_467_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_key_463_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_value_464_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v___x_482_);
v___x_484_ = v_reuseFailAlloc_487_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_485_; 
v___x_485_ = lean_array_uset(v_x_461_, v___x_481_, v___x_484_);
v_x_461_ = v___x_485_;
v_x_462_ = v_tail_465_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_489_, lean_object* v_source_490_, lean_object* v_target_491_){
_start:
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_array_get_size(v_source_490_);
v___x_493_ = lean_nat_dec_lt(v_i_489_, v___x_492_);
if (v___x_493_ == 0)
{
lean_dec_ref(v_source_490_);
lean_dec(v_i_489_);
return v_target_491_;
}
else
{
lean_object* v_es_494_; lean_object* v___x_495_; lean_object* v_source_496_; lean_object* v_target_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_es_494_ = lean_array_fget(v_source_490_, v_i_489_);
v___x_495_ = lean_box(0);
v_source_496_ = lean_array_fset(v_source_490_, v_i_489_, v___x_495_);
v_target_497_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_491_, v_es_494_);
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_add(v_i_489_, v___x_498_);
lean_dec(v_i_489_);
v_i_489_ = v___x_499_;
v_source_490_ = v_source_496_;
v_target_491_ = v_target_497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(lean_object* v_data_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_nbuckets_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_502_ = lean_array_get_size(v_data_501_);
v___x_503_ = lean_unsigned_to_nat(2u);
v_nbuckets_504_ = lean_nat_mul(v___x_502_, v___x_503_);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_box(0);
v___x_507_ = lean_mk_array(v_nbuckets_504_, v___x_506_);
v___x_508_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(v___x_505_, v_data_501_, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(lean_object* v_m_509_, lean_object* v_a_510_, lean_object* v_b_511_){
_start:
{
lean_object* v_size_512_; lean_object* v_buckets_513_; lean_object* v___x_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; uint64_t v_fold_518_; uint64_t v___x_519_; uint64_t v___x_520_; uint64_t v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; lean_object* v_bkt_527_; uint8_t v___x_528_; 
v_size_512_ = lean_ctor_get(v_m_509_, 0);
v_buckets_513_ = lean_ctor_get(v_m_509_, 1);
v___x_514_ = lean_array_get_size(v_buckets_513_);
v___x_515_ = l_Lean_Expr_hash(v_a_510_);
v___x_516_ = 32ULL;
v___x_517_ = lean_uint64_shift_right(v___x_515_, v___x_516_);
v_fold_518_ = lean_uint64_xor(v___x_515_, v___x_517_);
v___x_519_ = 16ULL;
v___x_520_ = lean_uint64_shift_right(v_fold_518_, v___x_519_);
v___x_521_ = lean_uint64_xor(v_fold_518_, v___x_520_);
v___x_522_ = lean_uint64_to_usize(v___x_521_);
v___x_523_ = lean_usize_of_nat(v___x_514_);
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_sub(v___x_523_, v___x_524_);
v___x_526_ = lean_usize_land(v___x_522_, v___x_525_);
v_bkt_527_ = lean_array_uget_borrowed(v_buckets_513_, v___x_526_);
v___x_528_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_510_, v_bkt_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_549_; 
lean_inc_ref(v_buckets_513_);
lean_inc(v_size_512_);
v_isSharedCheck_549_ = !lean_is_exclusive(v_m_509_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; lean_object* v_unused_551_; 
v_unused_550_ = lean_ctor_get(v_m_509_, 1);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_m_509_, 0);
lean_dec(v_unused_551_);
v___x_530_ = v_m_509_;
v_isShared_531_ = v_isSharedCheck_549_;
goto v_resetjp_529_;
}
else
{
lean_dec(v_m_509_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_549_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v_size_x27_533_; lean_object* v___x_534_; lean_object* v_buckets_x27_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_532_ = lean_unsigned_to_nat(1u);
v_size_x27_533_ = lean_nat_add(v_size_512_, v___x_532_);
lean_dec(v_size_512_);
lean_inc(v_bkt_527_);
v___x_534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_534_, 0, v_a_510_);
lean_ctor_set(v___x_534_, 1, v_b_511_);
lean_ctor_set(v___x_534_, 2, v_bkt_527_);
v_buckets_x27_535_ = lean_array_uset(v_buckets_513_, v___x_526_, v___x_534_);
v___x_536_ = lean_unsigned_to_nat(4u);
v___x_537_ = lean_nat_mul(v_size_x27_533_, v___x_536_);
v___x_538_ = lean_unsigned_to_nat(3u);
v___x_539_ = lean_nat_div(v___x_537_, v___x_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_array_get_size(v_buckets_x27_535_);
v___x_541_ = lean_nat_dec_le(v___x_539_, v___x_540_);
lean_dec(v___x_539_);
if (v___x_541_ == 0)
{
lean_object* v_val_542_; lean_object* v___x_544_; 
v_val_542_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_buckets_x27_535_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v_val_542_);
lean_ctor_set(v___x_530_, 0, v_size_x27_533_);
v___x_544_ = v___x_530_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_size_x27_533_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_val_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
else
{
lean_object* v___x_547_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v_buckets_x27_535_);
lean_ctor_set(v___x_530_, 0, v_size_x27_533_);
v___x_547_ = v___x_530_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_size_x27_533_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_buckets_x27_535_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
lean_dec(v_b_511_);
lean_dec_ref(v_a_510_);
return v_m_509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(lean_object* v_op_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_e_561_; lean_object* v___y_562_; 
if (lean_obj_tag(v_a_553_) == 5)
{
lean_object* v_fn_568_; 
v_fn_568_ = lean_ctor_get(v_a_553_, 0);
if (lean_obj_tag(v_fn_568_) == 5)
{
lean_object* v_arg_569_; lean_object* v_fn_570_; lean_object* v_arg_571_; lean_object* v___x_572_; 
v_arg_569_ = lean_ctor_get(v_a_553_, 1);
v_fn_570_ = lean_ctor_get(v_fn_568_, 0);
v_arg_571_ = lean_ctor_get(v_fn_568_, 1);
lean_inc(v_a_558_);
lean_inc_ref(v_a_557_);
lean_inc(v_a_556_);
lean_inc_ref(v_a_555_);
lean_inc_ref(v_fn_570_);
lean_inc_ref(v_op_552_);
v___x_572_ = l_Lean_Meta_isExprDefEq(v_op_552_, v_fn_570_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_614_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_614_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_614_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_614_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
uint8_t v___x_577_; 
v___x_577_ = lean_unbox(v_a_573_);
lean_dec(v_a_573_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec_ref(v_op_552_);
v___x_578_ = lean_box(0);
lean_inc_ref(v_a_553_);
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v_a_554_, v_a_553_, v___x_578_);
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v_a_553_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_581_);
v___x_583_ = v___x_575_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
else
{
lean_object* v___x_585_; 
lean_inc_ref(v_arg_571_);
lean_inc_ref(v_arg_569_);
lean_del_object(v___x_575_);
lean_dec_ref(v_a_553_);
lean_inc(v_a_558_);
lean_inc_ref(v_a_557_);
lean_inc(v_a_556_);
lean_inc_ref(v_a_555_);
lean_inc_ref(v_op_552_);
v___x_585_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_552_, v_arg_571_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_613_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref(v___x_585_);
v_fst_587_ = lean_ctor_get(v_a_586_, 0);
v_snd_588_ = lean_ctor_get(v_a_586_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_a_586_);
if (v_isSharedCheck_613_ == 0)
{
v___x_590_ = v_a_586_;
v_isShared_591_ = v_isSharedCheck_613_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_588_);
lean_inc(v_fst_587_);
lean_dec(v_a_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_613_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; 
v___x_592_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_552_, v_arg_569_, v_snd_588_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_612_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_612_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_612_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_612_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_611_; 
v_fst_597_ = lean_ctor_get(v_a_593_, 0);
v_snd_598_ = lean_ctor_get(v_a_593_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_a_593_);
if (v_isSharedCheck_611_ == 0)
{
v___x_600_ = v_a_593_;
v_isShared_601_ = v_isSharedCheck_611_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_snd_598_);
lean_inc(v_fst_597_);
lean_dec(v_a_593_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_611_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_fst_597_);
v___x_603_ = v___x_590_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_fst_587_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_fst_597_);
v___x_603_ = v_reuseFailAlloc_610_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_605_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_603_);
v___x_605_ = v___x_600_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_snd_598_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_605_);
v___x_607_ = v___x_595_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
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
else
{
lean_del_object(v___x_590_);
lean_dec(v_fst_587_);
return v___x_592_;
}
}
}
else
{
lean_dec_ref(v_arg_569_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec_ref(v_op_552_);
return v___x_585_;
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v_a_553_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec_ref(v_op_552_);
v_a_615_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_572_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_572_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec_ref(v_op_552_);
v_e_561_ = v_a_553_;
v___y_562_ = v_a_554_;
goto v___jp_560_;
}
}
else
{
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec_ref(v_op_552_);
v_e_561_ = v_a_553_;
v___y_562_ = v_a_554_;
goto v___jp_560_;
}
v___jp_560_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_563_ = lean_box(0);
lean_inc_ref(v_e_561_);
v___x_564_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v___y_562_, v_e_561_, v___x_563_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v_e_561_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_564_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr___boxed(lean_object* v_op_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0(lean_object* v_00_u03b2_632_, lean_object* v_m_633_, lean_object* v_a_634_, lean_object* v_b_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v_m_633_, v_a_634_, v_b_635_);
return v___x_636_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(lean_object* v_00_u03b2_637_, lean_object* v_a_638_, lean_object* v_x_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_638_, v_x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_641_, lean_object* v_a_642_, lean_object* v_x_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(v_00_u03b2_641_, v_a_642_, v_x_643_);
lean_dec(v_x_643_);
lean_dec_ref(v_a_642_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1(lean_object* v_00_u03b2_646_, lean_object* v_data_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_data_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_649_, lean_object* v_i_650_, lean_object* v_source_651_, lean_object* v_target_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(v_i_650_, v_source_651_, v_target_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(lean_object* v_varMap_658_, lean_object* v_a_659_){
_start:
{
if (lean_obj_tag(v_a_659_) == 0)
{
lean_object* v_lhs_660_; lean_object* v_rhs_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_670_; 
v_lhs_660_ = lean_ctor_get(v_a_659_, 0);
v_rhs_661_ = lean_ctor_get(v_a_659_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_a_659_);
if (v_isSharedCheck_670_ == 0)
{
v___x_663_ = v_a_659_;
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_rhs_661_);
lean_inc(v_lhs_660_);
lean_dec(v_a_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
lean_inc_ref(v_varMap_658_);
v___x_665_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(v_varMap_658_, v_lhs_660_);
v___x_666_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(v_varMap_658_, v_rhs_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
lean_ctor_set(v___x_663_, 1, v___x_666_);
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_e_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_e_671_ = lean_ctor_get(v_a_659_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v_a_659_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v_a_659_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_e_671_);
lean_dec(v_a_659_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_apply_1(v_varMap_658_, v_e_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 0);
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_683_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__2));
v___x_684_ = lean_unsigned_to_nat(11u);
v___x_685_ = lean_unsigned_to_nat(163u);
v___x_686_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__1));
v___x_687_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__0));
v___x_688_ = l_mkPanicMessageWithDecl(v___x_687_, v___x_686_, v___x_685_, v___x_684_, v___x_683_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg(lean_object* v_inst_689_, lean_object* v_a_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_691_) == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___closed__3);
v___x_693_ = lean_panic_fn(v_inst_689_, v___x_692_);
return v___x_693_;
}
else
{
lean_object* v_key_694_; lean_object* v_value_695_; lean_object* v_tail_696_; uint8_t v___x_697_; 
v_key_694_ = lean_ctor_get(v_x_691_, 0);
v_value_695_ = lean_ctor_get(v_x_691_, 1);
v_tail_696_ = lean_ctor_get(v_x_691_, 2);
v___x_697_ = lean_expr_eqv(v_key_694_, v_a_690_);
if (v___x_697_ == 0)
{
v_x_691_ = v_tail_696_;
goto _start;
}
else
{
lean_dec(v_inst_689_);
lean_inc(v_value_695_);
return v_value_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg___boxed(lean_object* v_inst_699_, lean_object* v_a_700_, lean_object* v_x_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg(v_inst_699_, v_a_700_, v_x_701_);
lean_dec(v_x_701_);
lean_dec_ref(v_a_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___redArg(lean_object* v_inst_703_, lean_object* v_m_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_buckets_706_; lean_object* v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v_fold_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_buckets_706_ = lean_ctor_get(v_m_704_, 1);
v___x_707_ = lean_array_get_size(v_buckets_706_);
v___x_708_ = l_Lean_Expr_hash(v_a_705_);
v___x_709_ = 32ULL;
v___x_710_ = lean_uint64_shift_right(v___x_708_, v___x_709_);
v_fold_711_ = lean_uint64_xor(v___x_708_, v___x_710_);
v___x_712_ = 16ULL;
v___x_713_ = lean_uint64_shift_right(v_fold_711_, v___x_712_);
v___x_714_ = lean_uint64_xor(v_fold_711_, v___x_713_);
v___x_715_ = lean_uint64_to_usize(v___x_714_);
v___x_716_ = lean_usize_of_nat(v___x_707_);
v___x_717_ = ((size_t)1ULL);
v___x_718_ = lean_usize_sub(v___x_716_, v___x_717_);
v___x_719_ = lean_usize_land(v___x_715_, v___x_718_);
v___x_720_ = lean_array_uget_borrowed(v_buckets_706_, v___x_719_);
v___x_721_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg(v_inst_703_, v_a_705_, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___redArg___boxed(lean_object* v_inst_722_, lean_object* v_m_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___redArg(v_inst_722_, v_m_723_, v_a_724_);
lean_dec_ref(v_a_724_);
lean_dec_ref(v_m_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0(lean_object* v___x_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___redArg(v___x_726_, v___y_727_, v___y_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0___boxed(lean_object* v___x_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_AC_toACExpr___lam__0(v___x_730_, v___y_731_, v___y_732_);
lean_dec_ref(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_AC_toACExpr_spec__4(lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
if (lean_obj_tag(v_x_735_) == 0)
{
return v_x_734_;
}
else
{
lean_object* v_key_736_; lean_object* v_tail_737_; lean_object* v___x_738_; 
v_key_736_ = lean_ctor_get(v_x_735_, 0);
lean_inc(v_key_736_);
v_tail_737_ = lean_ctor_get(v_x_735_, 2);
lean_inc(v_tail_737_);
lean_dec_ref(v_x_735_);
v___x_738_ = lean_array_push(v_x_734_, v_key_736_);
v_x_734_ = v___x_738_;
v_x_735_ = v_tail_737_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(lean_object* v_as_740_, size_t v_i_741_, size_t v_stop_742_, lean_object* v_b_743_){
_start:
{
uint8_t v___x_744_; 
v___x_744_ = lean_usize_dec_eq(v_i_741_, v_stop_742_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; size_t v___x_747_; size_t v___x_748_; 
v___x_745_ = lean_array_uget_borrowed(v_as_740_, v_i_741_);
lean_inc(v___x_745_);
v___x_746_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_AC_toACExpr_spec__4(v_b_743_, v___x_745_);
v___x_747_ = ((size_t)1ULL);
v___x_748_ = lean_usize_add(v_i_741_, v___x_747_);
v_i_741_ = v___x_748_;
v_b_743_ = v___x_746_;
goto _start;
}
else
{
return v_b_743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5___boxed(lean_object* v_as_750_, lean_object* v_i_751_, lean_object* v_stop_752_, lean_object* v_b_753_){
_start:
{
size_t v_i_boxed_754_; size_t v_stop_boxed_755_; lean_object* v_res_756_; 
v_i_boxed_754_ = lean_unbox_usize(v_i_751_);
lean_dec(v_i_751_);
v_stop_boxed_755_ = lean_unbox_usize(v_stop_752_);
lean_dec(v_stop_752_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_as_750_, v_i_boxed_754_, v_stop_boxed_755_, v_b_753_);
lean_dec_ref(v_as_750_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(lean_object* v_xs_757_, lean_object* v_j_758_){
_start:
{
lean_object* v_zero_759_; uint8_t v_isZero_760_; 
v_zero_759_ = lean_unsigned_to_nat(0u);
v_isZero_760_ = lean_nat_dec_eq(v_j_758_, v_zero_759_);
if (v_isZero_760_ == 1)
{
lean_dec(v_j_758_);
return v_xs_757_;
}
else
{
lean_object* v_one_761_; lean_object* v_n_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_one_761_ = lean_unsigned_to_nat(1u);
v_n_762_ = lean_nat_sub(v_j_758_, v_one_761_);
v___x_763_ = lean_array_fget_borrowed(v_xs_757_, v_j_758_);
v___x_764_ = lean_array_fget_borrowed(v_xs_757_, v_n_762_);
v___x_765_ = lean_expr_lt(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_dec(v_n_762_);
lean_dec(v_j_758_);
return v_xs_757_;
}
else
{
lean_object* v___x_766_; 
v___x_766_ = lean_array_fswap(v_xs_757_, v_j_758_, v_n_762_);
lean_dec(v_j_758_);
v_xs_757_ = v___x_766_;
v_j_758_ = v_n_762_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1(lean_object* v_xs_768_, lean_object* v_i_769_, lean_object* v_fuel_770_){
_start:
{
lean_object* v_zero_771_; uint8_t v_isZero_772_; 
v_zero_771_ = lean_unsigned_to_nat(0u);
v_isZero_772_ = lean_nat_dec_eq(v_fuel_770_, v_zero_771_);
if (v_isZero_772_ == 1)
{
lean_dec(v_fuel_770_);
lean_dec(v_i_769_);
return v_xs_768_;
}
else
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_array_get_size(v_xs_768_);
v___x_774_ = lean_nat_dec_lt(v_i_769_, v___x_773_);
if (v___x_774_ == 0)
{
lean_dec(v_fuel_770_);
lean_dec(v_i_769_);
return v_xs_768_;
}
else
{
lean_object* v_one_775_; lean_object* v_n_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_one_775_ = lean_unsigned_to_nat(1u);
v_n_776_ = lean_nat_sub(v_fuel_770_, v_one_775_);
lean_dec(v_fuel_770_);
lean_inc(v_i_769_);
v___x_777_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(v_xs_768_, v_i_769_);
v___x_778_ = lean_nat_add(v_i_769_, v_one_775_);
lean_dec(v_i_769_);
v_xs_768_ = v___x_777_;
v_i_769_ = v___x_778_;
v_fuel_770_ = v_n_776_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(lean_object* v_a_780_, lean_object* v_b_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_dec(v_b_781_);
lean_dec_ref(v_a_780_);
return v_x_782_;
}
else
{
lean_object* v_key_783_; lean_object* v_value_784_; lean_object* v_tail_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_797_; 
v_key_783_ = lean_ctor_get(v_x_782_, 0);
v_value_784_ = lean_ctor_get(v_x_782_, 1);
v_tail_785_ = lean_ctor_get(v_x_782_, 2);
v_isSharedCheck_797_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_797_ == 0)
{
v___x_787_ = v_x_782_;
v_isShared_788_ = v_isSharedCheck_797_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_tail_785_);
lean_inc(v_value_784_);
lean_inc(v_key_783_);
lean_dec(v_x_782_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_797_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
uint8_t v___x_789_; 
v___x_789_ = lean_expr_eqv(v_key_783_, v_a_780_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_780_, v_b_781_, v_tail_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v___x_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_key_783_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_value_784_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v___x_795_; 
lean_dec(v_value_784_);
lean_dec(v_key_783_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_b_781_);
lean_ctor_set(v___x_787_, 0, v_a_780_);
v___x_795_ = v___x_787_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_780_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_b_781_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_tail_785_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(lean_object* v_m_798_, lean_object* v_a_799_, lean_object* v_b_800_){
_start:
{
lean_object* v_size_801_; lean_object* v_buckets_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_845_; 
v_size_801_ = lean_ctor_get(v_m_798_, 0);
v_buckets_802_ = lean_ctor_get(v_m_798_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_m_798_);
if (v_isSharedCheck_845_ == 0)
{
v___x_804_ = v_m_798_;
v_isShared_805_ = v_isSharedCheck_845_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_buckets_802_);
lean_inc(v_size_801_);
lean_dec(v_m_798_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_845_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v_fold_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v_bkt_819_; uint8_t v___x_820_; 
v___x_806_ = lean_array_get_size(v_buckets_802_);
v___x_807_ = l_Lean_Expr_hash(v_a_799_);
v___x_808_ = 32ULL;
v___x_809_ = lean_uint64_shift_right(v___x_807_, v___x_808_);
v_fold_810_ = lean_uint64_xor(v___x_807_, v___x_809_);
v___x_811_ = 16ULL;
v___x_812_ = lean_uint64_shift_right(v_fold_810_, v___x_811_);
v___x_813_ = lean_uint64_xor(v_fold_810_, v___x_812_);
v___x_814_ = lean_uint64_to_usize(v___x_813_);
v___x_815_ = lean_usize_of_nat(v___x_806_);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_sub(v___x_815_, v___x_816_);
v___x_818_ = lean_usize_land(v___x_814_, v___x_817_);
v_bkt_819_ = lean_array_uget_borrowed(v_buckets_802_, v___x_818_);
v___x_820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_799_, v_bkt_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v_size_x27_822_; lean_object* v___x_823_; lean_object* v_buckets_x27_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v_size_x27_822_ = lean_nat_add(v_size_801_, v___x_821_);
lean_dec(v_size_801_);
lean_inc(v_bkt_819_);
v___x_823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_823_, 0, v_a_799_);
lean_ctor_set(v___x_823_, 1, v_b_800_);
lean_ctor_set(v___x_823_, 2, v_bkt_819_);
v_buckets_x27_824_ = lean_array_uset(v_buckets_802_, v___x_818_, v___x_823_);
v___x_825_ = lean_unsigned_to_nat(4u);
v___x_826_ = lean_nat_mul(v_size_x27_822_, v___x_825_);
v___x_827_ = lean_unsigned_to_nat(3u);
v___x_828_ = lean_nat_div(v___x_826_, v___x_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_array_get_size(v_buckets_x27_824_);
v___x_830_ = lean_nat_dec_le(v___x_828_, v___x_829_);
lean_dec(v___x_828_);
if (v___x_830_ == 0)
{
lean_object* v_val_831_; lean_object* v___x_833_; 
v_val_831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_buckets_x27_824_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v_val_831_);
lean_ctor_set(v___x_804_, 0, v_size_x27_822_);
v___x_833_ = v___x_804_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_size_x27_822_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_val_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v___x_836_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v_buckets_x27_824_);
lean_ctor_set(v___x_804_, 0, v_size_x27_822_);
v___x_836_ = v___x_804_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_size_x27_822_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_buckets_x27_824_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v___x_838_; lean_object* v_buckets_x27_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
lean_inc(v_bkt_819_);
v___x_838_ = lean_box(0);
v_buckets_x27_839_ = lean_array_uset(v_buckets_802_, v___x_818_, v___x_838_);
v___x_840_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_799_, v_b_800_, v_bkt_819_);
v___x_841_ = lean_array_uset(v_buckets_x27_839_, v___x_818_, v___x_840_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v___x_841_);
v___x_843_ = v___x_804_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_size_801_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(lean_object* v_as_846_, size_t v_i_847_, size_t v_stop_848_, lean_object* v_b_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = lean_usize_dec_eq(v_i_847_, v_stop_848_);
if (v___x_850_ == 0)
{
lean_object* v_size_851_; lean_object* v___x_852_; lean_object* v___x_853_; size_t v___x_854_; size_t v___x_855_; 
v_size_851_ = lean_ctor_get(v_b_849_, 0);
lean_inc(v_size_851_);
v___x_852_ = lean_array_uget_borrowed(v_as_846_, v_i_847_);
lean_inc(v___x_852_);
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(v_b_849_, v___x_852_, v_size_851_);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_i_847_, v___x_854_);
v_i_847_ = v___x_855_;
v_b_849_ = v___x_853_;
goto _start;
}
else
{
return v_b_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3___boxed(lean_object* v_as_857_, lean_object* v_i_858_, lean_object* v_stop_859_, lean_object* v_b_860_){
_start:
{
size_t v_i_boxed_861_; size_t v_stop_boxed_862_; lean_object* v_res_863_; 
v_i_boxed_861_ = lean_unbox_usize(v_i_858_);
lean_dec(v_i_858_);
v_stop_boxed_862_ = lean_unbox_usize(v_stop_859_);
lean_dec(v_stop_859_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v_as_857_, v_i_boxed_861_, v_stop_boxed_862_, v_b_860_);
lean_dec_ref(v_as_857_);
return v_res_863_;
}
}
static lean_object* _init_l_Lean_Meta_AC_toACExpr___closed__0(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_box(0);
v___x_865_ = lean_unsigned_to_nat(16u);
v___x_866_ = lean_mk_array(v___x_865_, v___x_864_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_Meta_AC_toACExpr___closed__1(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_obj_once(&l_Lean_Meta_AC_toACExpr___closed__0, &l_Lean_Meta_AC_toACExpr___closed__0_once, _init_l_Lean_Meta_AC_toACExpr___closed__0);
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr(lean_object* v_op_870_, lean_object* v_l_871_, lean_object* v_r_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_inc_ref(v_op_870_);
v___x_878_ = l_Lean_mkAppB(v_op_870_, v_l_871_, v_r_872_);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_obj_once(&l_Lean_Meta_AC_toACExpr___closed__1, &l_Lean_Meta_AC_toACExpr___closed__1_once, _init_l_Lean_Meta_AC_toACExpr___closed__1);
v___x_881_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_870_, v___x_878_, v___x_880_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_928_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_928_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_928_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_928_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_snd_886_; lean_object* v_fst_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_927_; 
v_snd_886_ = lean_ctor_get(v_a_882_, 1);
v_fst_887_ = lean_ctor_get(v_a_882_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v_a_882_);
if (v_isSharedCheck_927_ == 0)
{
v___x_889_ = v_a_882_;
v_isShared_890_ = v_isSharedCheck_927_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_snd_886_);
lean_inc(v_fst_887_);
lean_dec(v_a_882_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_927_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_size_891_; lean_object* v_buckets_892_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_905_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_size_891_ = lean_ctor_get(v_snd_886_, 0);
lean_inc(v_size_891_);
v_buckets_892_ = lean_ctor_get(v_snd_886_, 1);
lean_inc_ref(v_buckets_892_);
lean_dec(v_snd_886_);
v___x_917_ = lean_mk_empty_array_with_capacity(v_size_891_);
lean_dec(v_size_891_);
v___x_918_ = lean_array_get_size(v_buckets_892_);
v___x_919_ = lean_nat_dec_lt(v___x_879_, v___x_918_);
if (v___x_919_ == 0)
{
lean_dec_ref(v_buckets_892_);
v___y_905_ = v___x_917_;
goto v___jp_904_;
}
else
{
uint8_t v___x_920_; 
v___x_920_ = lean_nat_dec_le(v___x_918_, v___x_918_);
if (v___x_920_ == 0)
{
if (v___x_919_ == 0)
{
lean_dec_ref(v_buckets_892_);
v___y_905_ = v___x_917_;
goto v___jp_904_;
}
else
{
size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; 
v___x_921_ = ((size_t)0ULL);
v___x_922_ = lean_usize_of_nat(v___x_918_);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_buckets_892_, v___x_921_, v___x_922_, v___x_917_);
lean_dec_ref(v_buckets_892_);
v___y_905_ = v___x_923_;
goto v___jp_904_;
}
}
else
{
size_t v___x_924_; size_t v___x_925_; lean_object* v___x_926_; 
v___x_924_ = ((size_t)0ULL);
v___x_925_ = lean_usize_of_nat(v___x_918_);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_buckets_892_, v___x_924_, v___x_925_, v___x_917_);
lean_dec_ref(v_buckets_892_);
v___y_905_ = v___x_926_;
goto v___jp_904_;
}
}
v___jp_893_:
{
lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___f_896_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_toACExpr___lam__0___boxed), 3, 2);
lean_closure_set(v___f_896_, 0, v___x_879_);
lean_closure_set(v___f_896_, 1, v___y_895_);
v___x_897_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(v___f_896_, v_fst_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v___x_897_);
lean_ctor_set(v___x_889_, 0, v___y_894_);
v___x_899_ = v___x_889_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___y_894_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_897_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_899_);
v___x_901_ = v___x_884_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
v___jp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_906_ = lean_array_get_size(v___y_905_);
v___x_907_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1(v___y_905_, v___x_879_, v___x_906_);
v___x_908_ = lean_array_get_size(v___x_907_);
v___x_909_ = lean_nat_dec_lt(v___x_879_, v___x_908_);
if (v___x_909_ == 0)
{
v___y_894_ = v___x_907_;
v___y_895_ = v___x_880_;
goto v___jp_893_;
}
else
{
uint8_t v___x_910_; 
v___x_910_ = lean_nat_dec_le(v___x_908_, v___x_908_);
if (v___x_910_ == 0)
{
if (v___x_909_ == 0)
{
v___y_894_ = v___x_907_;
v___y_895_ = v___x_880_;
goto v___jp_893_;
}
else
{
size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((size_t)0ULL);
v___x_912_ = lean_usize_of_nat(v___x_908_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v___x_907_, v___x_911_, v___x_912_, v___x_880_);
v___y_894_ = v___x_907_;
v___y_895_ = v___x_913_;
goto v___jp_893_;
}
}
else
{
size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((size_t)0ULL);
v___x_915_ = lean_usize_of_nat(v___x_908_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v___x_907_, v___x_914_, v___x_915_, v___x_880_);
v___y_894_ = v___x_907_;
v___y_895_ = v___x_916_;
goto v___jp_893_;
}
}
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_881_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_881_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___boxed(lean_object* v_op_937_, lean_object* v_l_938_, lean_object* v_r_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_AC_toACExpr(v_op_937_, v_l_938_, v_r_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0(lean_object* v_00_u03b2_946_, lean_object* v_m_947_, lean_object* v_a_948_, lean_object* v_b_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(v_m_947_, v_a_948_, v_b_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(lean_object* v_00_u03b2_951_, lean_object* v_inst_952_, lean_object* v_m_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___redArg(v_inst_952_, v_m_953_, v_a_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___boxed(lean_object* v_00_u03b2_956_, lean_object* v_inst_957_, lean_object* v_m_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(v_00_u03b2_956_, v_inst_957_, v_m_958_, v_a_959_);
lean_dec_ref(v_a_959_);
lean_dec_ref(v_m_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0(lean_object* v_00_u03b2_961_, lean_object* v_a_962_, lean_object* v_b_963_, lean_object* v_x_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_962_, v_b_963_, v_x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2(lean_object* v_xs_966_, lean_object* v_j_967_, lean_object* v_h_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(v_xs_966_, v_j_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5___redArg(lean_object* v_inst_970_, lean_object* v_msg_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = lean_panic_fn(v_inst_970_, v_msg_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_973_, lean_object* v_inst_974_, lean_object* v_msg_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = lean_panic_fn(v_inst_974_, v_msg_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(lean_object* v_00_u03b2_977_, lean_object* v_inst_978_, lean_object* v_a_979_, lean_object* v_x_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___redArg(v_inst_978_, v_a_979_, v_x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___boxed(lean_object* v_00_u03b2_982_, lean_object* v_inst_983_, lean_object* v_a_984_, lean_object* v_x_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(v_00_u03b2_982_, v_inst_983_, v_a_984_, v_x_985_);
lean_dec(v_x_985_);
lean_dec_ref(v_a_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(lean_object* v_k_987_, lean_object* v_b_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = lean_apply_6(v_k_987_, v_b_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, lean_box(0));
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(v_k_995_, v_b_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(lean_object* v_name_1003_, uint8_t v_bi_1004_, lean_object* v_type_1005_, lean_object* v_k_1006_, uint8_t v_kind_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; 
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1013_, 0, v_k_1006_);
v___x_1014_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1003_, v_bi_1004_, v_type_1005_, v___f_1013_, v_kind_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1014_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1014_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___boxed(lean_object* v_name_1031_, lean_object* v_bi_1032_, lean_object* v_type_1033_, lean_object* v_k_1034_, lean_object* v_kind_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v_bi_boxed_1041_; uint8_t v_kind_boxed_1042_; lean_object* v_res_1043_; 
v_bi_boxed_1041_ = lean_unbox(v_bi_1032_);
v_kind_boxed_1042_ = lean_unbox(v_kind_1035_);
v_res_1043_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_1031_, v_bi_boxed_1041_, v_type_1033_, v_k_1034_, v_kind_boxed_1042_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(lean_object* v_name_1044_, lean_object* v_type_1045_, lean_object* v_k_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = 0;
v___x_1053_ = 0;
v___x_1054_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_1044_, v___x_1052_, v_type_1045_, v_k_1046_, v___x_1053_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg___boxed(lean_object* v_name_1055_, lean_object* v_type_1056_, lean_object* v_k_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v_name_1055_, v_type_1056_, v_k_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0___boxed(lean_object** _args){
lean_object* v_i_1068_ = _args[0];
lean_object* v_v_1069_ = _args[1];
lean_object* v_acc_1070_ = _args[2];
lean_object* v___x_1071_ = _args[3];
lean_object* v_vars_1072_ = _args[4];
lean_object* v___x_1073_ = _args[5];
lean_object* v_val_1074_ = _args[6];
lean_object* v_args_1075_ = _args[7];
lean_object* v_preContext_1076_ = _args[8];
lean_object* v_atoms_1077_ = _args[9];
lean_object* v_k_1078_ = _args[10];
lean_object* v_00_u03b1_1079_ = _args[11];
lean_object* v_u_1080_ = _args[12];
lean_object* v_iv_1081_ = _args[13];
lean_object* v___y_1082_ = _args[14];
lean_object* v___y_1083_ = _args[15];
lean_object* v___y_1084_ = _args[16];
lean_object* v___y_1085_ = _args[17];
lean_object* v___y_1086_ = _args[18];
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(v_i_1068_, v_v_1069_, v_acc_1070_, v___x_1071_, v_vars_1072_, v___x_1073_, v_val_1074_, v_args_1075_, v_preContext_1076_, v_atoms_1077_, v_k_1078_, v_00_u03b1_1079_, v_u_1080_, v_iv_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v_i_1068_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(lean_object* v_preContext_1091_, lean_object* v_atoms_1092_, lean_object* v_i_1093_, lean_object* v_acc_1094_, lean_object* v_vars_1095_, lean_object* v_args_1096_, lean_object* v_k_1097_, lean_object* v_00_u03b1_1098_, lean_object* v_u_1099_, lean_object* v_v_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_op_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_op_1106_ = lean_ctor_get(v_preContext_1091_, 1);
v___x_1107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1));
v___x_1108_ = lean_array_fget_borrowed(v_atoms_1092_, v_i_1093_);
v___x_1109_ = lean_unsigned_to_nat(2u);
v___x_1110_ = lean_mk_empty_array_with_capacity(v___x_1109_);
lean_inc_ref(v_op_1106_);
lean_inc_ref(v___x_1110_);
v___x_1111_ = lean_array_push(v___x_1110_, v_op_1106_);
lean_inc(v___x_1108_);
v___x_1112_ = lean_array_push(v___x_1111_, v___x_1108_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
v___x_1113_ = l_Lean_Meta_AC_getInstance(v___x_1107_, v___x_1112_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref(v___x_1113_);
if (lean_obj_tag(v_a_1114_) == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref(v___x_1110_);
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_add(v_i_1093_, v___x_1115_);
lean_dec(v_i_1093_);
lean_inc_ref(v_v_1100_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_v_1100_);
lean_ctor_set(v___x_1117_, 1, v_a_1114_);
v___x_1118_ = lean_array_push(v_acc_1094_, v___x_1117_);
v___x_1119_ = lean_array_push(v_vars_1095_, v_v_1100_);
lean_inc(v___x_1108_);
v___x_1120_ = lean_array_push(v_args_1096_, v___x_1108_);
v___x_1121_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1091_, v_atoms_1092_, v_k_1097_, v_00_u03b1_1098_, v_u_1099_, v___x_1116_, v___x_1118_, v___x_1119_, v___x_1120_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1121_;
}
else
{
lean_object* v_val_1122_; lean_object* v___f_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_inc(v___x_1108_);
lean_inc_ref(v_op_1106_);
v_val_1122_ = lean_ctor_get(v_a_1114_, 0);
lean_inc(v_val_1122_);
lean_dec_ref(v_a_1114_);
lean_inc(v_u_1099_);
lean_inc_ref(v_00_u03b1_1098_);
lean_inc_ref(v_v_1100_);
v___f_1123_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0___boxed), 19, 13);
lean_closure_set(v___f_1123_, 0, v_i_1093_);
lean_closure_set(v___f_1123_, 1, v_v_1100_);
lean_closure_set(v___f_1123_, 2, v_acc_1094_);
lean_closure_set(v___f_1123_, 3, v___x_1110_);
lean_closure_set(v___f_1123_, 4, v_vars_1095_);
lean_closure_set(v___f_1123_, 5, v___x_1108_);
lean_closure_set(v___f_1123_, 6, v_val_1122_);
lean_closure_set(v___f_1123_, 7, v_args_1096_);
lean_closure_set(v___f_1123_, 8, v_preContext_1091_);
lean_closure_set(v___f_1123_, 9, v_atoms_1092_);
lean_closure_set(v___f_1123_, 10, v_k_1097_);
lean_closure_set(v___f_1123_, 11, v_00_u03b1_1098_);
lean_closure_set(v___f_1123_, 12, v_u_1099_);
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3));
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_u_1099_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_mkConst(v___x_1107_, v___x_1126_);
v___x_1128_ = l_Lean_mkApp3(v___x_1127_, v_00_u03b1_1098_, v_op_1106_, v_v_1100_);
v___x_1129_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v___x_1124_, v___x_1128_, v___f_1123_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1129_;
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___x_1110_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec_ref(v_v_1100_);
lean_dec(v_u_1099_);
lean_dec_ref(v_00_u03b1_1098_);
lean_dec_ref(v_k_1097_);
lean_dec_ref(v_args_1096_);
lean_dec_ref(v_vars_1095_);
lean_dec_ref(v_acc_1094_);
lean_dec(v_i_1093_);
lean_dec_ref(v_atoms_1092_);
lean_dec_ref(v_preContext_1091_);
v_a_1130_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1113_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1113_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___boxed(lean_object* v_preContext_1138_, lean_object* v_atoms_1139_, lean_object* v_i_1140_, lean_object* v_acc_1141_, lean_object* v_vars_1142_, lean_object* v_args_1143_, lean_object* v_k_1144_, lean_object* v_00_u03b1_1145_, lean_object* v_u_1146_, lean_object* v_v_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(v_preContext_1138_, v_atoms_1139_, v_i_1140_, v_acc_1141_, v_vars_1142_, v_args_1143_, v_k_1144_, v_00_u03b1_1145_, v_u_1146_, v_v_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(lean_object* v_preContext_1157_, lean_object* v_atoms_1158_, lean_object* v_k_1159_, lean_object* v_00_u03b1_1160_, lean_object* v_u_1161_, lean_object* v_i_1162_, lean_object* v_acc_1163_, lean_object* v_vars_1164_, lean_object* v_args_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_array_get_size(v_atoms_1158_);
v___x_1172_ = lean_nat_dec_lt(v_i_1162_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec(v_i_1162_);
lean_dec(v_u_1161_);
lean_dec_ref(v_00_u03b1_1160_);
lean_dec_ref(v_atoms_1158_);
lean_dec_ref(v_preContext_1157_);
lean_inc(v_a_1169_);
lean_inc_ref(v_a_1168_);
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
v___x_1173_ = lean_apply_6(v_k_1159_, v_acc_1163_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, lean_box(0));
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; uint8_t v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = 1;
v___x_1176_ = 1;
v___x_1177_ = l_Lean_Meta_mkLambdaFVars(v_vars_1164_, v_a_1174_, v___x_1172_, v___x_1175_, v___x_1172_, v___x_1175_, v___x_1176_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec_ref(v_vars_1164_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1186_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_mkAppN(v_a_1178_, v_args_1165_);
lean_dec_ref(v_args_1165_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1184_ = v___x_1180_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_dec_ref(v_args_1165_);
return v___x_1177_;
}
}
else
{
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec_ref(v_args_1165_);
lean_dec_ref(v_vars_1164_);
return v___x_1173_;
}
}
else
{
lean_object* v___f_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_inc_ref(v_00_u03b1_1160_);
v___f_1187_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___boxed), 15, 9);
lean_closure_set(v___f_1187_, 0, v_preContext_1157_);
lean_closure_set(v___f_1187_, 1, v_atoms_1158_);
lean_closure_set(v___f_1187_, 2, v_i_1162_);
lean_closure_set(v___f_1187_, 3, v_acc_1163_);
lean_closure_set(v___f_1187_, 4, v_vars_1164_);
lean_closure_set(v___f_1187_, 5, v_args_1165_);
lean_closure_set(v___f_1187_, 6, v_k_1159_);
lean_closure_set(v___f_1187_, 7, v_00_u03b1_1160_);
lean_closure_set(v___f_1187_, 8, v_u_1161_);
v___x_1188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1));
v___x_1189_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v___x_1188_, v_00_u03b1_1160_, v___f_1187_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(lean_object* v_i_1190_, lean_object* v_v_1191_, lean_object* v_acc_1192_, lean_object* v___x_1193_, lean_object* v_vars_1194_, lean_object* v___x_1195_, lean_object* v_val_1196_, lean_object* v_args_1197_, lean_object* v_preContext_1198_, lean_object* v_atoms_1199_, lean_object* v_k_1200_, lean_object* v_00_u03b1_1201_, lean_object* v_u_1202_, lean_object* v_iv_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_nat_add(v_i_1190_, v___x_1209_);
lean_inc_ref(v_iv_1203_);
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_iv_1203_);
lean_inc_ref(v_v_1191_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v_v_1191_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_array_push(v_acc_1192_, v___x_1212_);
lean_inc_ref(v___x_1193_);
v___x_1214_ = lean_array_push(v___x_1193_, v_v_1191_);
v___x_1215_ = lean_array_push(v___x_1214_, v_iv_1203_);
v___x_1216_ = l_Array_append___redArg(v_vars_1194_, v___x_1215_);
lean_dec_ref(v___x_1215_);
v___x_1217_ = lean_array_push(v___x_1193_, v___x_1195_);
v___x_1218_ = lean_array_push(v___x_1217_, v_val_1196_);
v___x_1219_ = l_Array_append___redArg(v_args_1197_, v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1198_, v_atoms_1199_, v_k_1200_, v_00_u03b1_1201_, v_u_1202_, v___x_1210_, v___x_1213_, v___x_1216_, v___x_1219_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___boxed(lean_object* v_preContext_1221_, lean_object* v_atoms_1222_, lean_object* v_k_1223_, lean_object* v_00_u03b1_1224_, lean_object* v_u_1225_, lean_object* v_i_1226_, lean_object* v_acc_1227_, lean_object* v_vars_1228_, lean_object* v_args_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1221_, v_atoms_1222_, v_k_1223_, v_00_u03b1_1224_, v_u_1225_, v_i_1226_, v_acc_1227_, v_vars_1228_, v_args_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(lean_object* v_00_u03b1_1236_, lean_object* v_name_1237_, uint8_t v_bi_1238_, lean_object* v_type_1239_, lean_object* v_k_1240_, uint8_t v_kind_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_1237_, v_bi_1238_, v_type_1239_, v_k_1240_, v_kind_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_name_1249_, lean_object* v_bi_1250_, lean_object* v_type_1251_, lean_object* v_k_1252_, lean_object* v_kind_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
uint8_t v_bi_boxed_1259_; uint8_t v_kind_boxed_1260_; lean_object* v_res_1261_; 
v_bi_boxed_1259_ = lean_unbox(v_bi_1250_);
v_kind_boxed_1260_ = lean_unbox(v_kind_1253_);
v_res_1261_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(v_00_u03b1_1248_, v_name_1249_, v_bi_boxed_1259_, v_type_1251_, v_k_1252_, v_kind_boxed_1260_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(lean_object* v_00_u03b1_1262_, lean_object* v_name_1263_, lean_object* v_type_1264_, lean_object* v_k_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v_name_1263_, v_type_1264_, v_k_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_name_1273_, lean_object* v_type_1274_, lean_object* v_k_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(v_00_u03b1_1272_, v_name_1273_, v_type_1274_, v_k_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter___redArg(lean_object* v_____do__lift_1282_, lean_object* v_h__1_1283_, lean_object* v_h__2_1284_){
_start:
{
if (lean_obj_tag(v_____do__lift_1282_) == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec(v_h__2_1284_);
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_apply_1(v_h__1_1283_, v___x_1285_);
return v___x_1286_;
}
else
{
lean_object* v_val_1287_; lean_object* v___x_1288_; 
lean_dec(v_h__1_1283_);
v_val_1287_ = lean_ctor_get(v_____do__lift_1282_, 0);
lean_inc(v_val_1287_);
lean_dec_ref(v_____do__lift_1282_);
v___x_1288_ = lean_apply_1(v_h__2_1284_, v_val_1287_);
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter(lean_object* v_motive_1289_, lean_object* v_____do__lift_1290_, lean_object* v_h__1_1291_, lean_object* v_h__2_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter___redArg(v_____do__lift_1290_, v_h__1_1291_, v_h__2_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_abstractAtoms(lean_object* v_preContext_1296_, lean_object* v_atoms_1297_, lean_object* v_k_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = l_Lean_instInhabitedExpr;
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_array_get_borrowed(v___x_1304_, v_atoms_1297_, v___x_1305_);
lean_inc(v_a_1302_);
lean_inc_ref(v_a_1301_);
lean_inc(v_a_1300_);
lean_inc_ref(v_a_1299_);
lean_inc(v___x_1306_);
v___x_1307_ = lean_infer_type(v___x_1306_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1309_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref(v___x_1307_);
lean_inc(v_a_1302_);
lean_inc_ref(v_a_1301_);
lean_inc(v_a_1300_);
lean_inc_ref(v_a_1299_);
lean_inc(v_a_1308_);
v___x_1309_ = l_Lean_Meta_getLevel(v_a_1308_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = ((lean_object*)(l_Lean_Meta_AC_abstractAtoms___closed__0));
v___x_1312_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1296_, v_atoms_1297_, v_k_1298_, v_a_1308_, v_a_1310_, v___x_1305_, v___x_1311_, v___x_1311_, v___x_1311_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1312_;
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_a_1308_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_k_1298_);
lean_dec_ref(v_atoms_1297_);
lean_dec_ref(v_preContext_1296_);
v_a_1313_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1309_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1309_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_k_1298_);
lean_dec_ref(v_atoms_1297_);
lean_dec_ref(v_preContext_1296_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_abstractAtoms___boxed(lean_object* v_preContext_1321_, lean_object* v_atoms_1322_, lean_object* v_k_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Meta_AC_abstractAtoms(v_preContext_1321_, v_atoms_1322_, v_k_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(lean_object* v___x_1335_, lean_object* v___x_1336_, lean_object* v_tp_1337_){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2));
v___x_1339_ = l_Lean_mkConst(v___x_1338_, v___x_1335_);
v___x_1340_ = l_Lean_Expr_app___override(v___x_1336_, v_tp_1337_);
v___x_1341_ = l_Lean_Expr_app___override(v___x_1339_, v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(lean_object* v___x_1346_, lean_object* v___x_1347_, lean_object* v___x_1348_, lean_object* v_tp_1349_, lean_object* v_v_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1));
v___x_1352_ = l_Lean_mkConst(v___x_1351_, v___x_1346_);
lean_inc_ref(v_tp_1349_);
v___x_1353_ = l_Lean_Expr_app___override(v___x_1347_, v_tp_1349_);
v___x_1354_ = l_Lean_mkAppB(v___x_1348_, v_tp_1349_, v_v_1350_);
v___x_1355_ = l_Lean_mkAppB(v___x_1352_, v___x_1353_, v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2));
v___x_1364_ = l_Lean_mkConst(v___x_1363_, v___x_1362_);
return v___x_1364_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2));
v___x_1377_ = l_Lean_mkConst(v___x_1376_, v___x_1375_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11));
v___x_1384_ = l_Lean_mkConst(v___x_1383_, v___x_1382_);
return v___x_1384_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1));
v___x_1387_ = l_Lean_mkConst(v___x_1386_, v___x_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(lean_object* v_u_1388_, lean_object* v_preContext_1389_, lean_object* v_00_u03b1_1390_, size_t v_sz_1391_, size_t v_i_1392_, lean_object* v_bs_1393_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_usize_dec_lt(v_i_1392_, v_sz_1391_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref(v_00_u03b1_1390_);
lean_dec_ref(v_preContext_1389_);
lean_dec(v_u_1388_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_bs_1393_);
return v___x_1396_;
}
else
{
lean_object* v_v_1397_; lean_object* v_fst_1398_; lean_object* v_snd_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1432_; 
v_v_1397_ = lean_array_uget(v_bs_1393_, v_i_1392_);
v_fst_1398_ = lean_ctor_get(v_v_1397_, 0);
v_snd_1399_ = lean_ctor_get(v_v_1397_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_v_1397_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1401_ = v_v_1397_;
v_isShared_1402_ = v_isSharedCheck_1432_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_snd_1399_);
lean_inc(v_fst_1398_);
lean_dec(v_v_1397_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1432_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_op_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_bs_x27_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v_op_1403_ = lean_ctor_get(v_preContext_1389_, 1);
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
v___x_1406_ = lean_unsigned_to_nat(0u);
v_bs_x27_1407_ = lean_array_uset(v_bs_1393_, v_i_1392_, v___x_1406_);
v___x_1408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1));
lean_inc(v_u_1388_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 1);
lean_ctor_set(v___x_1401_, 1, v___x_1404_);
lean_ctor_set(v___x_1401_, 0, v_u_1388_);
v___x_1410_ = v___x_1401_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_u_1388_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1404_);
v___x_1410_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___y_1412_; lean_object* v___x_1420_; lean_object* v_isNeutralClass_1421_; 
lean_inc_ref(v___x_1410_);
v___x_1420_ = l_Lean_mkConst(v___x_1408_, v___x_1410_);
lean_inc(v_fst_1398_);
lean_inc_ref(v_op_1403_);
lean_inc_ref(v_00_u03b1_1390_);
v_isNeutralClass_1421_ = l_Lean_mkApp3(v___x_1420_, v_00_u03b1_1390_, v_op_1403_, v_fst_1398_);
if (lean_obj_tag(v_snd_1399_) == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9);
v___x_1423_ = l_Lean_Expr_app___override(v___x_1405_, v_isNeutralClass_1421_);
v___x_1424_ = l_Lean_Expr_app___override(v___x_1422_, v___x_1423_);
v___y_1412_ = v___x_1424_;
goto v___jp_1411_;
}
else
{
lean_object* v_val_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_val_1425_ = lean_ctor_get(v_snd_1399_, 0);
lean_inc(v_val_1425_);
lean_dec_ref(v_snd_1399_);
v___x_1426_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
v___x_1427_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13);
lean_inc_ref(v_isNeutralClass_1421_);
v___x_1428_ = l_Lean_Expr_app___override(v___x_1405_, v_isNeutralClass_1421_);
v___x_1429_ = l_Lean_mkAppB(v___x_1426_, v_isNeutralClass_1421_, v_val_1425_);
v___x_1430_ = l_Lean_mkAppB(v___x_1427_, v___x_1428_, v___x_1429_);
v___y_1412_ = v___x_1430_;
goto v___jp_1411_;
}
v___jp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8));
v___x_1414_ = l_Lean_mkConst(v___x_1413_, v___x_1410_);
lean_inc_ref(v_op_1403_);
lean_inc_ref(v_00_u03b1_1390_);
v___x_1415_ = l_Lean_mkApp4(v___x_1414_, v_00_u03b1_1390_, v_op_1403_, v_fst_1398_, v___y_1412_);
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = lean_usize_add(v_i_1392_, v___x_1416_);
v___x_1418_ = lean_array_uset(v_bs_x27_1407_, v_i_1392_, v___x_1415_);
v_i_1392_ = v___x_1417_;
v_bs_1393_ = v___x_1418_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___boxed(lean_object* v_u_1433_, lean_object* v_preContext_1434_, lean_object* v_00_u03b1_1435_, lean_object* v_sz_1436_, lean_object* v_i_1437_, lean_object* v_bs_1438_, lean_object* v___y_1439_){
_start:
{
size_t v_sz_boxed_1440_; size_t v_i_boxed_1441_; lean_object* v_res_1442_; 
v_sz_boxed_1440_ = lean_unbox_usize(v_sz_1436_);
lean_dec(v_sz_1436_);
v_i_boxed_1441_ = lean_unbox_usize(v_i_1437_);
lean_dec(v_i_1437_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1433_, v_preContext_1434_, v_00_u03b1_1435_, v_sz_boxed_1440_, v_i_boxed_1441_, v_bs_1438_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(lean_object* v_u_1443_, lean_object* v_preContext_1444_, lean_object* v_00_u03b1_1445_, size_t v_sz_1446_, size_t v_i_1447_, lean_object* v_bs_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_lt(v_i_1447_, v_sz_1446_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec_ref(v_00_u03b1_1445_);
lean_dec_ref(v_preContext_1444_);
lean_dec(v_u_1443_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_bs_1448_);
return v___x_1455_;
}
else
{
lean_object* v_v_1456_; lean_object* v_fst_1457_; lean_object* v_snd_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1491_; 
v_v_1456_ = lean_array_uget(v_bs_1448_, v_i_1447_);
v_fst_1457_ = lean_ctor_get(v_v_1456_, 0);
v_snd_1458_ = lean_ctor_get(v_v_1456_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_v_1456_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1460_ = v_v_1456_;
v_isShared_1461_ = v_isSharedCheck_1491_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_snd_1458_);
lean_inc(v_fst_1457_);
lean_dec(v_v_1456_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1491_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v_op_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_bs_x27_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
v_op_1462_ = lean_ctor_get(v_preContext_1444_, 1);
v___x_1463_ = lean_box(0);
v___x_1464_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
v___x_1465_ = lean_unsigned_to_nat(0u);
v_bs_x27_1466_ = lean_array_uset(v_bs_1448_, v_i_1447_, v___x_1465_);
v___x_1467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1));
lean_inc(v_u_1443_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 1);
lean_ctor_set(v___x_1460_, 1, v___x_1463_);
lean_ctor_set(v___x_1460_, 0, v_u_1443_);
v___x_1469_ = v___x_1460_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_u_1443_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1463_);
v___x_1469_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___y_1471_; lean_object* v___x_1479_; lean_object* v_isNeutralClass_1480_; 
lean_inc_ref(v___x_1469_);
v___x_1479_ = l_Lean_mkConst(v___x_1467_, v___x_1469_);
lean_inc(v_fst_1457_);
lean_inc_ref(v_op_1462_);
lean_inc_ref(v_00_u03b1_1445_);
v_isNeutralClass_1480_ = l_Lean_mkApp3(v___x_1479_, v_00_u03b1_1445_, v_op_1462_, v_fst_1457_);
if (lean_obj_tag(v_snd_1458_) == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9);
v___x_1482_ = l_Lean_Expr_app___override(v___x_1464_, v_isNeutralClass_1480_);
v___x_1483_ = l_Lean_Expr_app___override(v___x_1481_, v___x_1482_);
v___y_1471_ = v___x_1483_;
goto v___jp_1470_;
}
else
{
lean_object* v_val_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_val_1484_ = lean_ctor_get(v_snd_1458_, 0);
lean_inc(v_val_1484_);
lean_dec_ref(v_snd_1458_);
v___x_1485_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
v___x_1486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13);
lean_inc_ref(v_isNeutralClass_1480_);
v___x_1487_ = l_Lean_Expr_app___override(v___x_1464_, v_isNeutralClass_1480_);
v___x_1488_ = l_Lean_mkAppB(v___x_1485_, v_isNeutralClass_1480_, v_val_1484_);
v___x_1489_ = l_Lean_mkAppB(v___x_1486_, v___x_1487_, v___x_1488_);
v___y_1471_ = v___x_1489_;
goto v___jp_1470_;
}
v___jp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8));
v___x_1473_ = l_Lean_mkConst(v___x_1472_, v___x_1469_);
lean_inc_ref(v_op_1462_);
lean_inc_ref(v_00_u03b1_1445_);
v___x_1474_ = l_Lean_mkApp4(v___x_1473_, v_00_u03b1_1445_, v_op_1462_, v_fst_1457_, v___y_1471_);
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1447_, v___x_1475_);
v___x_1477_ = lean_array_uset(v_bs_x27_1466_, v_i_1447_, v___x_1474_);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1443_, v_preContext_1444_, v_00_u03b1_1445_, v_sz_1446_, v___x_1476_, v___x_1477_);
return v___x_1478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0___boxed(lean_object* v_u_1492_, lean_object* v_preContext_1493_, lean_object* v_00_u03b1_1494_, lean_object* v_sz_1495_, lean_object* v_i_1496_, lean_object* v_bs_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
size_t v_sz_boxed_1503_; size_t v_i_boxed_1504_; lean_object* v_res_1505_; 
v_sz_boxed_1503_ = lean_unbox_usize(v_sz_1495_);
lean_dec(v_sz_1495_);
v_i_boxed_1504_ = lean_unbox_usize(v_i_1496_);
lean_dec(v_i_1496_);
v_res_1505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(v_u_1492_, v_preContext_1493_, v_00_u03b1_1494_, v_sz_boxed_1503_, v_i_boxed_1504_, v_bs_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
return v_res_1505_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_box(0);
v___x_1507_ = l_Lean_instInhabitedExpr;
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___x_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(lean_object* v_preContext_1521_, lean_object* v_00_u03b1_1522_, lean_object* v_u_1523_, lean_object* v_vars_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; size_t v_sz_1533_; size_t v___x_1534_; lean_object* v___x_1535_; 
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0_once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0);
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = lean_array_get(v___x_1530_, v_vars_1524_, v___x_1531_);
v_sz_1533_ = lean_array_size(v_vars_1524_);
v___x_1534_ = ((size_t)0ULL);
lean_inc_ref(v_00_u03b1_1522_);
lean_inc_ref(v_preContext_1521_);
lean_inc(v_u_1523_);
v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(v_u_1523_, v_preContext_1521_, v_00_u03b1_1522_, v_sz_1533_, v___x_1534_, v_vars_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v_op_1537_; lean_object* v_assoc_1538_; lean_object* v_comm_1539_; lean_object* v_idem_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___x_1535_);
v_op_1537_ = lean_ctor_get(v_preContext_1521_, 1);
lean_inc_ref(v_op_1537_);
v_assoc_1538_ = lean_ctor_get(v_preContext_1521_, 2);
lean_inc_ref(v_assoc_1538_);
v_comm_1539_ = lean_ctor_get(v_preContext_1521_, 3);
lean_inc(v_comm_1539_);
v_idem_1540_ = lean_ctor_get(v_preContext_1521_, 4);
lean_inc(v_idem_1540_);
lean_dec_ref(v_preContext_1521_);
v___x_1541_ = lean_box(0);
v___x_1542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1543_ = lean_array_to_list(v_a_1536_);
v___x_1544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1));
v___x_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_u_1523_);
lean_ctor_set(v___x_1545_, 1, v___x_1541_);
lean_inc_ref(v___x_1545_);
v___x_1546_ = l_Lean_mkConst(v___x_1544_, v___x_1545_);
lean_inc_ref(v_op_1537_);
lean_inc_ref(v_00_u03b1_1522_);
v___x_1547_ = l_Lean_mkAppB(v___x_1546_, v_00_u03b1_1522_, v_op_1537_);
v___x_1548_ = l_Lean_Meta_mkListLit(v___x_1547_, v___x_1543_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1579_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1579_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1579_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_fst_1553_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___y_1566_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_fst_1553_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_fst_1553_);
lean_dec(v___x_1532_);
v___x_1563_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
v___x_1564_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
v___x_1573_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__4));
lean_inc_ref(v___x_1545_);
v___x_1574_ = l_Lean_mkConst(v___x_1573_, v___x_1545_);
lean_inc_ref(v_op_1537_);
lean_inc_ref(v_00_u03b1_1522_);
v___x_1575_ = l_Lean_mkAppB(v___x_1574_, v_00_u03b1_1522_, v_op_1537_);
if (lean_obj_tag(v_comm_1539_) == 0)
{
lean_object* v___x_1576_; 
v___x_1576_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(v___x_1542_, v___x_1563_, v___x_1575_);
v___y_1566_ = v___x_1576_;
goto v___jp_1565_;
}
else
{
lean_object* v_val_1577_; lean_object* v___x_1578_; 
v_val_1577_ = lean_ctor_get(v_comm_1539_, 0);
lean_inc(v_val_1577_);
lean_dec_ref(v_comm_1539_);
v___x_1578_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(v___x_1542_, v___x_1563_, v___x_1564_, v___x_1575_, v_val_1577_);
v___y_1566_ = v___x_1578_;
goto v___jp_1565_;
}
v___jp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3));
v___x_1558_ = l_Lean_mkConst(v___x_1557_, v___x_1545_);
v___x_1559_ = l_Lean_mkApp7(v___x_1558_, v_00_u03b1_1522_, v_op_1537_, v_assoc_1538_, v___y_1555_, v___y_1556_, v_a_1549_, v_fst_1553_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1559_);
v___x_1561_ = v___x_1551_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
v___jp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__6));
lean_inc_ref(v___x_1545_);
v___x_1568_ = l_Lean_mkConst(v___x_1567_, v___x_1545_);
lean_inc_ref(v_op_1537_);
lean_inc_ref(v_00_u03b1_1522_);
v___x_1569_ = l_Lean_mkAppB(v___x_1568_, v_00_u03b1_1522_, v_op_1537_);
if (lean_obj_tag(v_idem_1540_) == 0)
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(v___x_1542_, v___x_1563_, v___x_1569_);
v___y_1555_ = v___y_1566_;
v___y_1556_ = v___x_1570_;
goto v___jp_1554_;
}
else
{
lean_object* v_val_1571_; lean_object* v___x_1572_; 
v_val_1571_ = lean_ctor_get(v_idem_1540_, 0);
lean_inc(v_val_1571_);
lean_dec_ref(v_idem_1540_);
v___x_1572_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(v___x_1542_, v___x_1563_, v___x_1564_, v___x_1569_, v_val_1571_);
v___y_1555_ = v___y_1566_;
v___y_1556_ = v___x_1572_;
goto v___jp_1554_;
}
}
}
}
else
{
lean_dec_ref(v___x_1545_);
lean_dec(v_idem_1540_);
lean_dec(v_comm_1539_);
lean_dec_ref(v_assoc_1538_);
lean_dec_ref(v_op_1537_);
lean_dec(v___x_1532_);
lean_dec_ref(v_00_u03b1_1522_);
return v___x_1548_;
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v___x_1532_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_u_1523_);
lean_dec_ref(v_00_u03b1_1522_);
lean_dec_ref(v_preContext_1521_);
v_a_1580_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1535_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1535_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___boxed(lean_object* v_preContext_1588_, lean_object* v_00_u03b1_1589_, lean_object* v_u_1590_, lean_object* v_vars_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(v_preContext_1588_, v_00_u03b1_1589_, v_u_1590_, v_vars_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(lean_object* v_u_1598_, lean_object* v_preContext_1599_, lean_object* v_00_u03b1_1600_, size_t v_sz_1601_, size_t v_i_1602_, lean_object* v_bs_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1598_, v_preContext_1599_, v_00_u03b1_1600_, v_sz_1601_, v_i_1602_, v_bs_1603_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___boxed(lean_object* v_u_1610_, lean_object* v_preContext_1611_, lean_object* v_00_u03b1_1612_, lean_object* v_sz_1613_, lean_object* v_i_1614_, lean_object* v_bs_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
size_t v_sz_boxed_1621_; size_t v_i_boxed_1622_; lean_object* v_res_1623_; 
v_sz_boxed_1621_ = lean_unbox_usize(v_sz_1613_);
lean_dec(v_sz_1613_);
v_i_boxed_1622_ = lean_unbox_usize(v_i_1614_);
lean_dec(v_i_1614_);
v_res_1623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(v_u_1610_, v_preContext_1611_, v_00_u03b1_1612_, v_sz_boxed_1621_, v_i_boxed_1622_, v_bs_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1623_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = lean_box(0);
v___x_1633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2));
v___x_1634_ = l_Lean_mkConst(v___x_1633_, v___x_1632_);
return v___x_1634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = lean_box(0);
v___x_1643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5));
v___x_1644_ = l_Lean_mkConst(v___x_1643_, v___x_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(lean_object* v_a_1645_){
_start:
{
if (lean_obj_tag(v_a_1645_) == 0)
{
lean_object* v_x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_x_1646_ = lean_ctor_get(v_a_1645_, 0);
lean_inc(v_x_1646_);
lean_dec_ref(v_a_1645_);
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3_once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3);
v___x_1648_ = l_Lean_mkNatLit(v_x_1646_);
v___x_1649_ = l_Lean_Expr_app___override(v___x_1647_, v___x_1648_);
return v___x_1649_;
}
else
{
lean_object* v_lhs_1650_; lean_object* v_rhs_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_lhs_1650_ = lean_ctor_get(v_a_1645_, 0);
lean_inc_ref(v_lhs_1650_);
v_rhs_1651_ = lean_ctor_get(v_a_1645_, 1);
lean_inc_ref(v_rhs_1651_);
lean_dec_ref(v_a_1645_);
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6_once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6);
v___x_1653_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v_lhs_1650_);
v___x_1654_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v_rhs_1651_);
v___x_1655_ = l_Lean_mkAppB(v___x_1652_, v___x_1653_, v___x_1654_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(lean_object* v_preContext_1656_, lean_object* v_vars_1657_, lean_object* v_a_1658_){
_start:
{
if (lean_obj_tag(v_a_1658_) == 0)
{
lean_object* v_x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec_ref(v_preContext_1656_);
v_x_1659_ = lean_ctor_get(v_a_1658_, 0);
v___x_1660_ = l_Lean_instInhabitedExpr;
v___x_1661_ = lean_array_get_borrowed(v___x_1660_, v_vars_1657_, v_x_1659_);
lean_inc(v___x_1661_);
return v___x_1661_;
}
else
{
lean_object* v_lhs_1662_; lean_object* v_rhs_1663_; lean_object* v_op_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_lhs_1662_ = lean_ctor_get(v_a_1658_, 0);
v_rhs_1663_ = lean_ctor_get(v_a_1658_, 1);
v_op_1664_ = lean_ctor_get(v_preContext_1656_, 1);
lean_inc_ref(v_op_1664_);
lean_inc_ref(v_preContext_1656_);
v___x_1665_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1656_, v_vars_1657_, v_lhs_1662_);
v___x_1666_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1656_, v_vars_1657_, v_rhs_1663_);
v___x_1667_ = l_Lean_mkAppB(v_op_1664_, v___x_1665_, v___x_1666_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget___boxed(lean_object* v_preContext_1668_, lean_object* v_vars_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1668_, v_vars_1669_, v_a_1670_);
lean_dec_ref(v_a_1670_);
lean_dec_ref(v_vars_1669_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(lean_object* v_msg_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___f_1679_; lean_object* v___x_2080__overap_1680_; lean_object* v___x_1681_; 
v___f_1679_ = ((lean_object*)(l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0));
v___x_2080__overap_1680_ = lean_panic_fn(v___f_1679_, v_msg_1673_);
v___x_1681_ = lean_apply_5(v___x_2080__overap_1680_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___boxed(lean_object* v_msg_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(v_msg_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(lean_object* v_x_1689_){
_start:
{
if (lean_obj_tag(v_x_1689_) == 0)
{
lean_object* v___x_1690_; 
v___x_1690_ = ((lean_object*)(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0));
return v___x_1690_;
}
else
{
lean_object* v_tail_1691_; 
v_tail_1691_ = lean_ctor_get(v_x_1689_, 1);
if (lean_obj_tag(v_tail_1691_) == 0)
{
lean_object* v_head_1692_; lean_object* v___x_1693_; 
v_head_1692_ = lean_ctor_get(v_x_1689_, 0);
lean_inc(v_head_1692_);
lean_dec_ref(v_x_1689_);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_head_1692_);
return v___x_1693_;
}
else
{
lean_object* v_head_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1703_; 
lean_inc(v_tail_1691_);
v_head_1694_ = lean_ctor_get(v_x_1689_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1689_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; 
v_unused_1704_ = lean_ctor_get(v_x_1689_, 1);
lean_dec(v_unused_1704_);
v___x_1696_ = v_x_1689_;
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_head_1694_);
lean_dec(v_x_1689_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_head_1694_);
v___x_1699_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v_tail_1691_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 1, v___x_1699_);
lean_ctor_set(v___x_1696_, 0, v___x_1698_);
v___x_1701_ = v___x_1696_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_bs_1707_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_lt(v_i_1706_, v_sz_1705_);
if (v___x_1708_ == 0)
{
return v_bs_1707_;
}
else
{
lean_object* v_v_1709_; lean_object* v_fst_1710_; lean_object* v___x_1711_; lean_object* v_bs_x27_1712_; size_t v___x_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v_v_1709_ = lean_array_uget_borrowed(v_bs_1707_, v_i_1706_);
v_fst_1710_ = lean_ctor_get(v_v_1709_, 0);
lean_inc(v_fst_1710_);
v___x_1711_ = lean_unsigned_to_nat(0u);
v_bs_x27_1712_ = lean_array_uset(v_bs_1707_, v_i_1706_, v___x_1711_);
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1706_, v___x_1713_);
v___x_1715_ = lean_array_uset(v_bs_x27_1712_, v_i_1706_, v_fst_1710_);
v_i_1706_ = v___x_1714_;
v_bs_1707_ = v___x_1715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2___boxed(lean_object* v_sz_1717_, lean_object* v_i_1718_, lean_object* v_bs_1719_){
_start:
{
size_t v_sz_boxed_1720_; size_t v_i_boxed_1721_; lean_object* v_res_1722_; 
v_sz_boxed_1720_ = lean_unbox_usize(v_sz_1717_);
lean_dec(v_sz_1717_);
v_i_boxed_1721_ = lean_unbox_usize(v_i_1718_);
lean_dec(v_i_1718_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(v_sz_boxed_1720_, v_i_boxed_1721_, v_bs_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(size_t v_sz_1723_, size_t v_i_1724_, lean_object* v_bs_1725_){
_start:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_usize_dec_lt(v_i_1724_, v_sz_1723_);
if (v___x_1726_ == 0)
{
return v_bs_1725_;
}
else
{
lean_object* v_v_1727_; lean_object* v_snd_1728_; lean_object* v___x_1729_; lean_object* v_bs_x27_1730_; uint8_t v___y_1732_; 
v_v_1727_ = lean_array_uget_borrowed(v_bs_1725_, v_i_1724_);
v_snd_1728_ = lean_ctor_get(v_v_1727_, 1);
lean_inc(v_snd_1728_);
v___x_1729_ = lean_unsigned_to_nat(0u);
v_bs_x27_1730_ = lean_array_uset(v_bs_1725_, v_i_1724_, v___x_1729_);
if (lean_obj_tag(v_snd_1728_) == 0)
{
uint8_t v___x_1738_; 
v___x_1738_ = 0;
v___y_1732_ = v___x_1738_;
goto v___jp_1731_;
}
else
{
lean_dec_ref(v_snd_1728_);
v___y_1732_ = v___x_1726_;
goto v___jp_1731_;
}
v___jp_1731_:
{
size_t v___x_1733_; size_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1733_ = ((size_t)1ULL);
v___x_1734_ = lean_usize_add(v_i_1724_, v___x_1733_);
v___x_1735_ = lean_box(v___y_1732_);
v___x_1736_ = lean_array_uset(v_bs_x27_1730_, v_i_1724_, v___x_1735_);
v_i_1724_ = v___x_1734_;
v_bs_1725_ = v___x_1736_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0___boxed(lean_object* v_sz_1739_, lean_object* v_i_1740_, lean_object* v_bs_1741_){
_start:
{
size_t v_sz_boxed_1742_; size_t v_i_boxed_1743_; lean_object* v_res_1744_; 
v_sz_boxed_1742_ = lean_unbox_usize(v_sz_1739_);
lean_dec(v_sz_1739_);
v_i_boxed_1743_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_res_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(v_sz_boxed_1742_, v_i_boxed_1743_, v_bs_1741_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(lean_object* v_ctx_1745_, lean_object* v_a_1746_){
_start:
{
if (lean_obj_tag(v_a_1746_) == 0)
{
return v_a_1746_;
}
else
{
lean_object* v_head_1747_; lean_object* v_tail_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1762_; 
v_head_1747_ = lean_ctor_get(v_a_1746_, 0);
v_tail_1748_ = lean_ctor_get(v_a_1746_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_a_1746_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1750_ = v_a_1746_;
v_isShared_1751_ = v_isSharedCheck_1762_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_tail_1748_);
lean_inc(v_head_1747_);
lean_dec(v_a_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1762_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v_snd_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_snd_1752_ = lean_ctor_get(v_ctx_1745_, 1);
v___x_1753_ = 0;
v___x_1754_ = lean_box(v___x_1753_);
v___x_1755_ = lean_array_get_borrowed(v___x_1754_, v_snd_1752_, v_head_1747_);
v___x_1756_ = lean_unbox(v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(v_ctx_1745_, v_tail_1748_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1757_);
v___x_1759_ = v___x_1750_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_head_1747_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
else
{
lean_del_object(v___x_1750_);
lean_dec(v_head_1747_);
v_a_1746_ = v_tail_1748_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3___boxed(lean_object* v_ctx_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(v_ctx_1763_, v_a_1764_);
lean_dec_ref(v_ctx_1763_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(lean_object* v_ctx_1766_, lean_object* v_x_1767_){
_start:
{
if (lean_obj_tag(v_x_1767_) == 0)
{
return v_x_1767_;
}
else
{
lean_object* v_head_1768_; lean_object* v___x_1769_; 
v_head_1768_ = lean_ctor_get(v_x_1767_, 0);
lean_inc(v_head_1768_);
v___x_1769_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(v_ctx_1766_, v_x_1767_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1770_, 0, v_head_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
return v___x_1770_;
}
else
{
lean_dec(v_head_1768_);
return v___x_1769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1___boxed(lean_object* v_ctx_1771_, lean_object* v_x_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(v_ctx_1771_, v_x_1772_);
lean_dec_ref(v_ctx_1771_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(lean_object* v_ctx_1774_, lean_object* v_e_1775_){
_start:
{
lean_object* v_fst_1776_; lean_object* v_comm_1777_; lean_object* v_idem_1778_; lean_object* v___y_1780_; lean_object* v_xs_1782_; lean_object* v_xs_1783_; 
v_fst_1776_ = lean_ctor_get(v_ctx_1774_, 0);
v_comm_1777_ = lean_ctor_get(v_fst_1776_, 3);
v_idem_1778_ = lean_ctor_get(v_fst_1776_, 4);
v_xs_1782_ = l_Lean_Data_AC_Expr_toList(v_e_1775_);
v_xs_1783_ = l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(v_ctx_1774_, v_xs_1782_);
if (lean_obj_tag(v_comm_1777_) == 0)
{
v___y_1780_ = v_xs_1783_;
goto v___jp_1779_;
}
else
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Data_AC_sort(v_xs_1783_);
v___y_1780_ = v___x_1784_;
goto v___jp_1779_;
}
v___jp_1779_:
{
if (lean_obj_tag(v_idem_1778_) == 0)
{
return v___y_1780_;
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Data_AC_mergeIdem(v___y_1780_);
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1___boxed(lean_object* v_ctx_1785_, lean_object* v_e_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(v_ctx_1785_, v_e_1786_);
lean_dec_ref(v_e_1786_);
lean_dec_ref(v_ctx_1785_);
return v_res_1787_;
}
}
static lean_object* _init_l_Lean_Meta_AC_buildNormProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_box(0);
v___x_1794_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___lam__0___closed__2));
v___x_1795_ = l_Lean_mkConst(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___lam__0(lean_object* v___x_1803_, lean_object* v_fst_1804_, lean_object* v_preContext_1805_, lean_object* v_snd_1806_, lean_object* v_varsData_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_array_get_borrowed(v___x_1803_, v_fst_1804_, v___x_1813_);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
lean_inc(v___x_1814_);
v___x_1815_ = lean_infer_type(v___x_1814_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1817_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v___x_1815_);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
lean_inc(v_a_1816_);
v___x_1817_ = l_Lean_Meta_getLevel(v_a_1816_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref(v___x_1817_);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
lean_inc_ref(v_varsData_1807_);
lean_inc(v_a_1818_);
lean_inc(v_a_1816_);
lean_inc_ref(v_preContext_1805_);
v___x_1819_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(v_preContext_1805_, v_a_1816_, v_a_1818_, v_varsData_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1819_);
v___x_1821_ = lean_box(0);
v___x_1822_ = lean_obj_once(&l_Lean_Meta_AC_buildNormProof___lam__0___closed__3, &l_Lean_Meta_AC_buildNormProof___lam__0___closed__3_once, _init_l_Lean_Meta_AC_buildNormProof___lam__0___closed__3);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
v___x_1823_ = l_Lean_Meta_mkEqRefl(v___x_1822_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; size_t v_sz_1825_; size_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1823_);
v_sz_1825_ = lean_array_size(v_varsData_1807_);
v___x_1826_ = ((size_t)0ULL);
lean_inc_ref(v_varsData_1807_);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(v_sz_1825_, v___x_1826_, v_varsData_1807_);
lean_inc_ref(v_preContext_1805_);
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_preContext_1805_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(v___x_1828_, v_snd_1806_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(v_sz_1825_, v___x_1826_, v_varsData_1807_);
v___x_1831_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v___x_1829_);
lean_inc_ref(v_preContext_1805_);
v___x_1832_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1805_, v___x_1830_, v_snd_1806_);
v___x_1833_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1805_, v___x_1830_, v___x_1831_);
lean_dec_ref(v___x_1830_);
v___x_1834_ = l_Lean_Meta_mkEq(v___x_1832_, v___x_1833_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1856_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1856_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1856_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1839_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v_snd_1806_);
v___x_1840_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v___x_1831_);
v___x_1841_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___lam__0___closed__5));
v___x_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_a_1818_);
lean_ctor_set(v___x_1842_, 1, v___x_1821_);
v___x_1843_ = l_Lean_mkConst(v___x_1841_, v___x_1842_);
v___x_1844_ = lean_unsigned_to_nat(5u);
v___x_1845_ = lean_mk_empty_array_with_capacity(v___x_1844_);
v___x_1846_ = lean_array_push(v___x_1845_, v_a_1816_);
v___x_1847_ = lean_array_push(v___x_1846_, v_a_1820_);
v___x_1848_ = lean_array_push(v___x_1847_, v___x_1839_);
v___x_1849_ = lean_array_push(v___x_1848_, v___x_1840_);
v___x_1850_ = lean_array_push(v___x_1849_, v_a_1824_);
v___x_1851_ = l_Lean_mkAppN(v___x_1843_, v___x_1850_);
lean_dec_ref(v___x_1850_);
v___x_1852_ = l_Lean_Meta_mkExpectedPropHint(v___x_1851_, v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1852_);
v___x_1854_ = v___x_1837_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_dec_ref(v___x_1831_);
lean_dec(v_a_1824_);
lean_dec(v_a_1820_);
lean_dec(v_a_1818_);
lean_dec(v_a_1816_);
lean_dec_ref(v_snd_1806_);
return v___x_1834_;
}
}
else
{
lean_dec(v_a_1820_);
lean_dec(v_a_1818_);
lean_dec(v_a_1816_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_varsData_1807_);
lean_dec_ref(v_snd_1806_);
lean_dec_ref(v_preContext_1805_);
return v___x_1823_;
}
}
else
{
lean_dec(v_a_1818_);
lean_dec(v_a_1816_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_varsData_1807_);
lean_dec_ref(v_snd_1806_);
lean_dec_ref(v_preContext_1805_);
return v___x_1819_;
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1816_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_varsData_1807_);
lean_dec_ref(v_snd_1806_);
lean_dec_ref(v_preContext_1805_);
v_a_1857_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1817_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1817_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_varsData_1807_);
lean_dec_ref(v_snd_1806_);
lean_dec_ref(v_preContext_1805_);
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___boxed(lean_object* v___x_1865_, lean_object* v_fst_1866_, lean_object* v_preContext_1867_, lean_object* v_snd_1868_, lean_object* v_varsData_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Meta_AC_buildNormProof___lam__0(v___x_1865_, v_fst_1866_, v_preContext_1867_, v_snd_1868_, v_varsData_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec_ref(v_fst_1866_);
return v_res_1875_;
}
}
static lean_object* _init_l_Lean_Meta_AC_buildNormProof___closed__5(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1882_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__4));
v___x_1883_ = lean_unsigned_to_nat(52u);
v___x_1884_ = lean_unsigned_to_nat(132u);
v___x_1885_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__3));
v___x_1886_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__2));
v___x_1887_ = l_mkPanicMessageWithDecl(v___x_1886_, v___x_1885_, v___x_1884_, v___x_1883_, v___x_1882_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof(lean_object* v_preContext_1888_, lean_object* v_l_1889_, lean_object* v_r_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_op_1896_; lean_object* v___x_1897_; 
v_op_1896_ = lean_ctor_get(v_preContext_1888_, 1);
lean_inc(v_a_1894_);
lean_inc_ref(v_a_1893_);
lean_inc(v_a_1892_);
lean_inc_ref(v_a_1891_);
lean_inc_ref(v_op_1896_);
v___x_1897_ = l_Lean_Meta_AC_toACExpr(v_op_1896_, v_l_1889_, v_r_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v_fst_1899_; lean_object* v_snd_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1942_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v_fst_1899_ = lean_ctor_get(v_a_1898_, 0);
v_snd_1900_ = lean_ctor_get(v_a_1898_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_a_1898_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1902_ = v_a_1898_;
v_isShared_1903_ = v_isSharedCheck_1942_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_snd_1900_);
lean_inc(v_fst_1899_);
lean_dec(v_a_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1942_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___f_1905_; lean_object* v___x_1906_; 
v___x_1904_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_preContext_1888_);
lean_inc(v_fst_1899_);
v___f_1905_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_buildNormProof___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1905_, 0, v___x_1904_);
lean_closure_set(v___f_1905_, 1, v_fst_1899_);
lean_closure_set(v___f_1905_, 2, v_preContext_1888_);
lean_closure_set(v___f_1905_, 3, v_snd_1900_);
lean_inc(v_a_1894_);
lean_inc_ref(v_a_1893_);
lean_inc(v_a_1892_);
lean_inc_ref(v_a_1891_);
v___x_1906_ = l_Lean_Meta_AC_abstractAtoms(v_preContext_1888_, v_fst_1899_, v___f_1905_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v___x_1906_);
lean_inc(v_a_1894_);
lean_inc_ref(v_a_1893_);
lean_inc(v_a_1892_);
lean_inc_ref(v_a_1891_);
lean_inc(v_a_1907_);
v___x_1908_ = lean_infer_type(v_a_1907_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1925_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1925_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1925_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1913_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__1));
v___x_1914_ = lean_unsigned_to_nat(3u);
v___x_1915_ = l_Lean_Expr_isAppOfArity(v_a_1909_, v___x_1913_, v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_del_object(v___x_1911_);
lean_dec(v_a_1909_);
lean_dec(v_a_1907_);
lean_del_object(v___x_1902_);
v___x_1916_ = lean_obj_once(&l_Lean_Meta_AC_buildNormProof___closed__5, &l_Lean_Meta_AC_buildNormProof___closed__5_once, _init_l_Lean_Meta_AC_buildNormProof___closed__5);
v___x_1917_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(v___x_1916_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
v___x_1918_ = l_Lean_Expr_appArg_x21(v_a_1909_);
lean_dec(v_a_1909_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v___x_1918_);
lean_ctor_set(v___x_1902_, 0, v_a_1907_);
v___x_1920_ = v___x_1902_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1907_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1922_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1920_);
v___x_1922_ = v___x_1911_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v_a_1907_);
lean_del_object(v___x_1902_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
v_a_1926_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1908_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1908_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_del_object(v___x_1902_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
v_a_1934_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1906_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1906_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec_ref(v_preContext_1888_);
v_a_1943_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1897_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1897_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___boxed(lean_object* v_preContext_1951_, lean_object* v_l_1952_, lean_object* v_r_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Meta_AC_buildNormProof(v_preContext_1951_, v_l_1952_, v_r_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3(lean_object* v_ctx_1960_, lean_object* v_x_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v_x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___boxed(lean_object* v_ctx_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3(v_ctx_1963_, v_x_1964_);
lean_dec_ref(v_ctx_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___redArg(lean_object* v_e_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_e_1974_; lean_object* v_op_1981_; lean_object* v_l_1982_; lean_object* v_r_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; 
if (lean_obj_tag(v_e_1966_) == 5)
{
lean_object* v_fn_2039_; 
v_fn_2039_ = lean_ctor_get(v_e_1966_, 0);
if (lean_obj_tag(v_fn_2039_) == 5)
{
lean_object* v_parent_x3f_2040_; 
v_parent_x3f_2040_ = lean_ctor_get(v_a_1967_, 7);
lean_inc(v_parent_x3f_2040_);
lean_dec_ref(v_a_1967_);
if (lean_obj_tag(v_parent_x3f_2040_) == 1)
{
lean_object* v_val_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2133_; 
v_val_2041_ = lean_ctor_get(v_parent_x3f_2040_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_parent_x3f_2040_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2043_ = v_parent_x3f_2040_;
v_isShared_2044_ = v_isSharedCheck_2133_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_val_2041_);
lean_dec(v_parent_x3f_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2133_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
if (lean_obj_tag(v_val_2041_) == 5)
{
lean_object* v_fn_2045_; 
v_fn_2045_ = lean_ctor_get(v_val_2041_, 0);
lean_inc_ref(v_fn_2045_);
lean_dec_ref(v_val_2041_);
if (lean_obj_tag(v_fn_2045_) == 5)
{
lean_object* v_arg_2046_; lean_object* v_fn_2047_; lean_object* v_arg_2048_; lean_object* v_fn_2049_; lean_object* v___x_2050_; 
v_arg_2046_ = lean_ctor_get(v_e_1966_, 1);
v_fn_2047_ = lean_ctor_get(v_fn_2039_, 0);
v_arg_2048_ = lean_ctor_get(v_fn_2039_, 1);
v_fn_2049_ = lean_ctor_get(v_fn_2045_, 0);
lean_inc_ref(v_fn_2049_);
lean_dec_ref(v_fn_2045_);
lean_inc(v_a_1971_);
lean_inc_ref(v_a_1970_);
lean_inc(v_a_1969_);
lean_inc_ref(v_a_1968_);
lean_inc_ref(v_fn_2047_);
v___x_2050_ = l_Lean_Meta_isExprDefEq(v_fn_2047_, v_fn_2049_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2118_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2118_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2118_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
uint8_t v___x_2055_; uint8_t v___x_2056_; 
v___x_2055_ = 1;
v___x_2056_ = lean_unbox(v_a_2051_);
lean_dec(v_a_2051_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; 
lean_del_object(v___x_2053_);
lean_inc(v_a_1971_);
lean_inc_ref(v_a_1970_);
lean_inc(v_a_1969_);
lean_inc_ref(v_a_1968_);
lean_inc_ref(v_fn_2047_);
v___x_2057_ = l_Lean_Meta_AC_preContext(v_fn_2047_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2101_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2101_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2101_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
if (lean_obj_tag(v_a_2058_) == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
v___x_2062_ = lean_box(0);
v___x_2063_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2063_, 0, v_e_1966_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
lean_ctor_set_uint8(v___x_2063_, sizeof(void*)*2, v___x_2055_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2063_);
v___x_2065_ = v___x_2043_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2065_);
v___x_2067_ = v___x_2060_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
else
{
lean_object* v_val_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2100_; 
lean_inc_ref(v_arg_2048_);
lean_inc_ref(v_arg_2046_);
lean_del_object(v___x_2060_);
lean_dec_ref(v_e_1966_);
v_val_2070_ = lean_ctor_get(v_a_2058_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_a_2058_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2072_ = v_a_2058_;
v_isShared_2073_ = v_isSharedCheck_2100_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_val_2070_);
lean_dec(v_a_2058_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2100_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_Meta_AC_buildNormProof(v_val_2070_, v_arg_2048_, v_arg_2046_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2091_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2091_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2091_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_fst_2079_; lean_object* v_snd_2080_; lean_object* v___x_2082_; 
v_fst_2079_ = lean_ctor_get(v_a_2075_, 0);
lean_inc(v_fst_2079_);
v_snd_2080_ = lean_ctor_get(v_a_2075_, 1);
lean_inc(v_snd_2080_);
lean_dec(v_a_2075_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v_fst_2079_);
v___x_2082_ = v___x_2072_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_fst_2079_);
v___x_2082_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2083_, 0, v_snd_2080_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*2, v___x_2055_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2083_);
v___x_2085_ = v___x_2043_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2087_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2085_);
v___x_2087_ = v___x_2077_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
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
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_del_object(v___x_2072_);
lean_del_object(v___x_2043_);
v_a_2092_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2074_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2074_);
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
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_del_object(v___x_2043_);
lean_dec_ref(v_e_1966_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
v_a_2102_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2057_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2057_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
v___x_2110_ = lean_box(0);
v___x_2111_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2111_, 0, v_e_1966_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*2, v___x_2055_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2111_);
v___x_2113_ = v___x_2043_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2113_);
v___x_2115_ = v___x_2053_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_del_object(v___x_2043_);
lean_dec_ref(v_e_1966_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
v_a_2119_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2050_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2050_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_arg_2127_; lean_object* v_fn_2128_; lean_object* v_arg_2129_; 
lean_dec_ref(v_fn_2045_);
lean_del_object(v___x_2043_);
v_arg_2127_ = lean_ctor_get(v_e_1966_, 1);
v_fn_2128_ = lean_ctor_get(v_fn_2039_, 0);
v_arg_2129_ = lean_ctor_get(v_fn_2039_, 1);
lean_inc_ref(v_arg_2127_);
lean_inc_ref(v_arg_2129_);
lean_inc_ref(v_fn_2128_);
v_op_1981_ = v_fn_2128_;
v_l_1982_ = v_arg_2129_;
v_r_1983_ = v_arg_2127_;
v___y_1984_ = v_a_1968_;
v___y_1985_ = v_a_1969_;
v___y_1986_ = v_a_1970_;
v___y_1987_ = v_a_1971_;
goto v___jp_1980_;
}
}
else
{
lean_object* v_arg_2130_; lean_object* v_fn_2131_; lean_object* v_arg_2132_; 
lean_del_object(v___x_2043_);
lean_dec(v_val_2041_);
v_arg_2130_ = lean_ctor_get(v_e_1966_, 1);
v_fn_2131_ = lean_ctor_get(v_fn_2039_, 0);
v_arg_2132_ = lean_ctor_get(v_fn_2039_, 1);
lean_inc_ref(v_arg_2130_);
lean_inc_ref(v_arg_2132_);
lean_inc_ref(v_fn_2131_);
v_op_1981_ = v_fn_2131_;
v_l_1982_ = v_arg_2132_;
v_r_1983_ = v_arg_2130_;
v___y_1984_ = v_a_1968_;
v___y_1985_ = v_a_1969_;
v___y_1986_ = v_a_1970_;
v___y_1987_ = v_a_1971_;
goto v___jp_1980_;
}
}
}
else
{
lean_object* v_arg_2134_; lean_object* v_fn_2135_; lean_object* v_arg_2136_; 
lean_dec(v_parent_x3f_2040_);
v_arg_2134_ = lean_ctor_get(v_e_1966_, 1);
v_fn_2135_ = lean_ctor_get(v_fn_2039_, 0);
v_arg_2136_ = lean_ctor_get(v_fn_2039_, 1);
lean_inc_ref(v_arg_2134_);
lean_inc_ref(v_arg_2136_);
lean_inc_ref(v_fn_2135_);
v_op_1981_ = v_fn_2135_;
v_l_1982_ = v_arg_2136_;
v_r_1983_ = v_arg_2134_;
v___y_1984_ = v_a_1968_;
v___y_1985_ = v_a_1969_;
v___y_1986_ = v_a_1970_;
v___y_1987_ = v_a_1971_;
goto v___jp_1980_;
}
}
else
{
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_a_1967_);
v_e_1974_ = v_e_1966_;
goto v___jp_1973_;
}
}
else
{
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_a_1967_);
v_e_1974_ = v_e_1966_;
goto v___jp_1973_;
}
v___jp_1973_:
{
lean_object* v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1975_ = lean_box(0);
v___x_1976_ = 1;
v___x_1977_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1977_, 0, v_e_1974_);
lean_ctor_set(v___x_1977_, 1, v___x_1975_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*2, v___x_1976_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
v___jp_1980_:
{
lean_object* v___x_1988_; 
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v___y_1985_);
lean_inc_ref(v___y_1984_);
v___x_1988_ = l_Lean_Meta_AC_preContext(v_op_1981_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2030_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2030_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2030_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
if (lean_obj_tag(v_a_1989_) == 0)
{
lean_object* v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_r_1983_);
lean_dec_ref(v_l_1982_);
v___x_1993_ = lean_box(0);
v___x_1994_ = 1;
v___x_1995_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1995_, 0, v_e_1966_);
lean_ctor_set(v___x_1995_, 1, v___x_1993_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*2, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1996_);
v___x_1998_ = v___x_1991_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
else
{
lean_object* v_val_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2029_; 
lean_del_object(v___x_1991_);
lean_dec_ref(v_e_1966_);
v_val_2000_ = lean_ctor_get(v_a_1989_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_a_1989_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2002_ = v_a_1989_;
v_isShared_2003_ = v_isSharedCheck_2029_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_val_2000_);
lean_dec(v_a_1989_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2029_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_Meta_AC_buildNormProof(v_val_2000_, v_l_1982_, v_r_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2020_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2020_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2020_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_fst_2009_; lean_object* v_snd_2010_; lean_object* v___x_2012_; 
v_fst_2009_ = lean_ctor_get(v_a_2005_, 0);
lean_inc(v_fst_2009_);
v_snd_2010_ = lean_ctor_get(v_a_2005_, 1);
lean_inc(v_snd_2010_);
lean_dec(v_a_2005_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v_fst_2009_);
v___x_2012_ = v___x_2002_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_fst_2009_);
v___x_2012_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2013_ = 1;
v___x_2014_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2014_, 0, v_snd_2010_);
lean_ctor_set(v___x_2014_, 1, v___x_2012_);
lean_ctor_set_uint8(v___x_2014_, sizeof(void*)*2, v___x_2013_);
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2015_);
v___x_2017_ = v___x_2007_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_del_object(v___x_2002_);
v_a_2021_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2004_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2004_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_r_1983_);
lean_dec_ref(v_l_1982_);
lean_dec_ref(v_e_1966_);
v_a_2031_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_1988_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_1988_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___redArg___boxed(lean_object* v_e_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Meta_AC_post___redArg(v_e_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post(lean_object* v_e_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Meta_AC_post___redArg(v_e_2145_, v_a_2147_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___boxed(lean_object* v_e_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Meta_AC_post(v_e_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2158_);
lean_dec(v_a_2156_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(lean_object* v_e_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v___x_2168_; 
v___x_2168_ = l_Lean_Expr_hasMVar(v_e_2165_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_e_2165_);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; lean_object* v_mctx_2171_; lean_object* v___x_2172_; lean_object* v_fst_2173_; lean_object* v_snd_2174_; lean_object* v___x_2175_; lean_object* v_cache_2176_; lean_object* v_zetaDeltaFVarIds_2177_; lean_object* v_postponed_2178_; lean_object* v_diag_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2188_; 
v___x_2170_ = lean_st_ref_get(v___y_2166_);
v_mctx_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc_ref(v_mctx_2171_);
lean_dec(v___x_2170_);
v___x_2172_ = l_Lean_instantiateMVarsCore(v_mctx_2171_, v_e_2165_);
v_fst_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_fst_2173_);
v_snd_2174_ = lean_ctor_get(v___x_2172_, 1);
lean_inc(v_snd_2174_);
lean_dec_ref(v___x_2172_);
v___x_2175_ = lean_st_ref_take(v___y_2166_);
v_cache_2176_ = lean_ctor_get(v___x_2175_, 1);
v_zetaDeltaFVarIds_2177_ = lean_ctor_get(v___x_2175_, 2);
v_postponed_2178_ = lean_ctor_get(v___x_2175_, 3);
v_diag_2179_ = lean_ctor_get(v___x_2175_, 4);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v___x_2175_, 0);
lean_dec(v_unused_2189_);
v___x_2181_ = v___x_2175_;
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_diag_2179_);
lean_inc(v_postponed_2178_);
lean_inc(v_zetaDeltaFVarIds_2177_);
lean_inc(v_cache_2176_);
lean_dec(v___x_2175_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v_snd_2174_);
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_snd_2174_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_cache_2176_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_zetaDeltaFVarIds_2177_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_postponed_2178_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v_diag_2179_);
v___x_2184_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_st_ref_set(v___y_2166_, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_fst_2173_);
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg___boxed(lean_object* v_e_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_e_2190_, v___y_2191_);
lean_dec(v___y_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(lean_object* v_e_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_e_2194_, v___y_2196_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___boxed(lean_object* v_e_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(v_e_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__0(lean_object* v_x_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0));
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__0___boxed(lean_object* v_x_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__0(v_x_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v_x_2221_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__1(lean_object* v_x_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0));
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__1___boxed(lean_object* v_x_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__1(v_x_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v_x_2244_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__2(lean_object* v_e_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v_e_2254_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__2___boxed(lean_object* v_e_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__2(v_e_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__3(lean_object* v_x_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_box(0);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__3___boxed(lean_object* v_x_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__3(v_x_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v_x_2286_);
return v_res_2295_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__5(void){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2302_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__5, &l_Lean_Meta_AC_rewriteUnnormalized___closed__5_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__5);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__7(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__6, &l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v___x_2305_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__8(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = lean_unsigned_to_nat(32u);
v___x_2309_ = lean_mk_empty_array_with_capacity(v___x_2308_);
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__9(void){
_start:
{
size_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2311_ = ((size_t)5ULL);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_unsigned_to_nat(32u);
v___x_2314_ = lean_mk_empty_array_with_capacity(v___x_2313_);
v___x_2315_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__8, &l_Lean_Meta_AC_rewriteUnnormalized___closed__8_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__8);
v___x_2316_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v___x_2314_);
lean_ctor_set(v___x_2316_, 2, v___x_2312_);
lean_ctor_set(v___x_2316_, 3, v___x_2312_);
lean_ctor_set_usize(v___x_2316_, 4, v___x_2311_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__10(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__9, &l_Lean_Meta_AC_rewriteUnnormalized___closed__9_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__9);
v___x_2318_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__6, &l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6);
v___x_2319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
lean_ctor_set(v___x_2319_, 2, v___x_2318_);
lean_ctor_set(v___x_2319_, 3, v___x_2317_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__10, &l_Lean_Meta_AC_rewriteUnnormalized___closed__10_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__10);
v___x_2321_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__7, &l_Lean_Meta_AC_rewriteUnnormalized___closed__7_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__7);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v___x_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized(lean_object* v_mvarId_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_2335_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
v___x_2339_ = l_Lean_Meta_Simp_neutralConfig;
v___x_2340_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__0));
v___x_2341_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2339_, v___x_2340_, v_a_2338_, v_a_2332_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref(v___x_2341_);
lean_inc(v_mvarId_2331_);
v___x_2343_ = l_Lean_MVarId_getType(v_mvarId_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; lean_object* v_a_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref(v___x_2343_);
v___x_2345_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_a_2344_, v_a_2333_);
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__11, &l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11);
v___x_2348_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__13));
lean_inc(v_a_2335_);
lean_inc_ref(v_a_2334_);
lean_inc(v_a_2333_);
lean_inc_ref(v_a_2332_);
lean_inc(v_a_2346_);
v___x_2349_ = l_Lean_Meta_Simp_main(v_a_2346_, v_a_2342_, v___x_2347_, v___x_2348_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v_fst_2351_; lean_object* v___x_2352_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v_fst_2351_ = lean_ctor_get(v_a_2350_, 0);
lean_inc(v_fst_2351_);
lean_dec(v_a_2350_);
v___x_2352_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_2331_, v_a_2346_, v_fst_2351_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2346_);
return v___x_2352_;
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec(v_a_2346_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_mvarId_2331_);
v_a_2353_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2349_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2349_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec(v_a_2342_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_mvarId_2331_);
v_a_2361_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2343_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2343_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_mvarId_2331_);
v_a_2369_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2341_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2341_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_mvarId_2331_);
v_a_2377_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2337_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2337_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___boxed(lean_object* v_mvarId_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Meta_AC_rewriteUnnormalized(v_mvarId_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object* v_goal_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___x_2398_; 
lean_inc(v_a_2396_);
lean_inc_ref(v_a_2395_);
lean_inc(v_a_2394_);
lean_inc_ref(v_a_2393_);
v___x_2398_ = l_Lean_Meta_AC_rewriteUnnormalized(v_goal_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref(v___x_2398_);
v___x_2400_ = 1;
v___x_2401_ = l_Lean_MVarId_refl(v_a_2399_, v___x_2400_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2401_;
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
v_a_2402_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2398_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2398_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl___boxed(lean_object* v_goal_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v_goal_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(lean_object* v_x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_apply_9(v_x_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, lean_box(0));
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0___boxed(lean_object* v_x_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(v_x_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(lean_object* v_mvarId_2439_, lean_object* v_x_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___f_2450_; lean_object* v___x_2451_; 
v___f_2450_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2450_, 0, v_x_2440_);
lean_closure_set(v___f_2450_, 1, v___y_2441_);
lean_closure_set(v___f_2450_, 2, v___y_2442_);
lean_closure_set(v___f_2450_, 3, v___y_2443_);
lean_closure_set(v___f_2450_, 4, v___y_2444_);
v___x_2451_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2439_, v___f_2450_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2451_) == 0)
{
return v___x_2451_;
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___boxed(lean_object* v_mvarId_2460_, lean_object* v_x_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_mvarId_2460_, v_x_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(lean_object* v_00_u03b1_2472_, lean_object* v_mvarId_2473_, lean_object* v_x_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_mvarId_2473_, v_x_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___boxed(lean_object* v_00_u03b1_2485_, lean_object* v_mvarId_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(v_00_u03b1_2485_, v_mvarId_2486_, v_x_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___lam__0(lean_object* v_a_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v_a_2498_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___lam__0___boxed(lean_object* v_a_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Meta_AC_acRflTactic___redArg___lam__0(v_a_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg(lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_2521_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref(v___x_2529_);
lean_inc(v_a_2530_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acRflTactic___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2531_, 0, v_a_2530_);
v___x_2532_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_a_2530_, v___f_2531_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
return v___x_2532_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
v_a_2533_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2529_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2529_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___boxed(lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_Meta_AC_acRflTactic___redArg(v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic(lean_object* v_x_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_Meta_AC_acRflTactic___redArg(v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___boxed(lean_object* v_x_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_Meta_AC_acRflTactic(v_x_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
lean_dec(v_x_2562_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1(){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2588_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2589_ = ((lean_object*)(l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3));
v___x_2590_ = ((lean_object*)(l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5));
v___x_2591_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acRflTactic___boxed), 10, 0);
v___x_2592_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2588_, v___x_2589_, v___x_2590_, v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___boxed(lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3(){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = ((lean_object*)(l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5));
v___x_2622_ = ((lean_object*)(l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6));
v___x_2623_ = l_Lean_addBuiltinDeclarationRanges(v___x_2621_, v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___boxed(lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(lean_object* v_mvarId_2626_, lean_object* v_x_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2626_, v_x_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
v_a_2642_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2633_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2633_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg___boxed(lean_object* v_mvarId_2650_, lean_object* v_x_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_mvarId_2650_, v_x_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(lean_object* v_00_u03b1_2658_, lean_object* v_mvarId_2659_, lean_object* v_x_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_mvarId_2659_, v_x_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___boxed(lean_object* v_00_u03b1_2667_, lean_object* v_mvarId_2668_, lean_object* v_x_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(v_00_u03b1_2667_, v_mvarId_2668_, v_x_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___lam__4(lean_object* v_fvarId_2676_, lean_object* v___f_2677_, lean_object* v___f_2678_, lean_object* v___f_2679_, lean_object* v___f_2680_, lean_object* v_goal_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2685_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref(v___x_2687_);
v___x_2689_ = l_Lean_Meta_Simp_neutralConfig;
v___x_2690_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__0));
v___x_2691_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2689_, v___x_2690_, v_a_2688_, v___y_2682_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
lean_inc_ref(v___y_2682_);
lean_inc(v_fvarId_2676_);
v___x_2693_ = l_Lean_FVarId_getType___redArg(v_fvarId_2676_, v___y_2682_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; lean_object* v_a_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2693_);
v___x_2695_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_a_2694_, v___y_2683_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = lean_unsigned_to_nat(32u);
v___x_2698_ = lean_mk_empty_array_with_capacity(v___x_2697_);
lean_dec_ref(v___x_2698_);
v___x_2699_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__11, &l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11);
v___x_2700_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__12));
v___x_2701_ = 1;
v___x_2702_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2702_, 0, v___f_2677_);
lean_ctor_set(v___x_2702_, 1, v___x_2700_);
lean_ctor_set(v___x_2702_, 2, v___f_2678_);
lean_ctor_set(v___x_2702_, 3, v___f_2679_);
lean_ctor_set(v___x_2702_, 4, v___f_2680_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*5, v___x_2701_);
lean_inc(v___y_2685_);
lean_inc_ref(v___y_2684_);
lean_inc(v___y_2683_);
lean_inc_ref(v___y_2682_);
v___x_2703_ = l_Lean_Meta_Simp_main(v_a_2696_, v_a_2692_, v___x_2699_, v___x_2702_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v_fst_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref(v___x_2703_);
v_fst_2705_ = lean_ctor_get(v_a_2704_, 0);
lean_inc(v_fst_2705_);
lean_dec(v_a_2704_);
v___x_2706_ = 0;
v___x_2707_ = l_Lean_Meta_applySimpResultToLocalDecl(v_goal_2681_, v_fvarId_2676_, v_fst_2705_, v___x_2706_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2728_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2728_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2728_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
if (lean_obj_tag(v_a_2708_) == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2712_ = lean_box(0);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2712_);
v___x_2714_ = v___x_2710_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
else
{
lean_object* v_val_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2727_; 
v_val_2716_ = lean_ctor_get(v_a_2708_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_a_2708_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2718_ = v_a_2708_;
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_val_2716_);
lean_dec(v_a_2708_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v_snd_2720_; lean_object* v___x_2722_; 
v_snd_2720_ = lean_ctor_get(v_val_2716_, 1);
lean_inc(v_snd_2720_);
lean_dec(v_val_2716_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_snd_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_snd_2720_);
v___x_2722_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2724_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2722_);
v___x_2724_ = v___x_2710_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
v_a_2729_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2707_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2707_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v_goal_2681_);
lean_dec(v_fvarId_2676_);
v_a_2737_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2703_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2703_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_a_2692_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v_goal_2681_);
lean_dec_ref(v___f_2680_);
lean_dec_ref(v___f_2679_);
lean_dec_ref(v___f_2678_);
lean_dec_ref(v___f_2677_);
lean_dec(v_fvarId_2676_);
v_a_2745_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2693_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2693_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v_goal_2681_);
lean_dec_ref(v___f_2680_);
lean_dec_ref(v___f_2679_);
lean_dec_ref(v___f_2678_);
lean_dec_ref(v___f_2677_);
lean_dec(v_fvarId_2676_);
v_a_2753_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2691_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2691_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v_goal_2681_);
lean_dec_ref(v___f_2680_);
lean_dec_ref(v___f_2679_);
lean_dec_ref(v___f_2678_);
lean_dec_ref(v___f_2677_);
lean_dec(v_fvarId_2676_);
v_a_2761_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2687_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2687_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___lam__4___boxed(lean_object* v_fvarId_2769_, lean_object* v___f_2770_, lean_object* v___f_2771_, lean_object* v___f_2772_, lean_object* v___f_2773_, lean_object* v_goal_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_Meta_AC_acNfHypMeta___lam__4(v_fvarId_2769_, v___f_2770_, v___f_2771_, v___f_2772_, v___f_2773_, v_goal_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta(lean_object* v_goal_2781_, lean_object* v_fvarId_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v___f_2788_; lean_object* v___f_2789_; lean_object* v___f_2790_; lean_object* v___f_2791_; lean_object* v___f_2792_; lean_object* v___x_2793_; 
v___f_2788_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__4));
v___f_2789_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__3));
v___f_2790_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__2));
v___f_2791_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__1));
lean_inc(v_goal_2781_);
v___f_2792_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acNfHypMeta___lam__4___boxed), 11, 6);
lean_closure_set(v___f_2792_, 0, v_fvarId_2782_);
lean_closure_set(v___f_2792_, 1, v___f_2791_);
lean_closure_set(v___f_2792_, 2, v___f_2790_);
lean_closure_set(v___f_2792_, 3, v___f_2789_);
lean_closure_set(v___f_2792_, 4, v___f_2788_);
lean_closure_set(v___f_2792_, 5, v_goal_2781_);
v___x_2793_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_goal_2781_, v___f_2792_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___boxed(lean_object* v_goal_2794_, lean_object* v_fvarId_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Meta_AC_acNfHypMeta(v_goal_2794_, v_fvarId_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___lam__0(lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2803_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref(v___x_2811_);
lean_inc(v___y_2809_);
lean_inc_ref(v___y_2808_);
lean_inc(v___y_2807_);
lean_inc_ref(v___y_2806_);
v___x_2813_ = l_Lean_Meta_AC_rewriteUnnormalized(v_a_2812_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref(v___x_2813_);
v___x_2815_ = lean_box(0);
v___x_2816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2816_, 0, v_a_2814_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2816_, v___y_2803_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
return v___x_2817_;
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
v_a_2818_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2813_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2813_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
v_a_2826_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2811_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2811_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___lam__0___boxed(lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Meta_AC_acNfTargetTactic___lam__0(v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic(lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v___f_2854_; lean_object* v___x_2855_; 
v___f_2854_ = ((lean_object*)(l_Lean_Meta_AC_acNfTargetTactic___closed__0));
v___x_2855_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2854_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___boxed(lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Meta_AC_acNfTargetTactic(v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___lam__0(lean_object* v_fvarId_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2868_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v___x_2876_);
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_2878_ = l_Lean_Meta_AC_acNfHypMeta(v_a_2877_, v_fvarId_2866_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref(v___x_2878_);
if (lean_obj_tag(v_a_2879_) == 1)
{
lean_object* v_val_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v_val_2880_ = lean_ctor_get(v_a_2879_, 0);
lean_inc(v_val_2880_);
lean_dec_ref(v_a_2879_);
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2882_, 0, v_val_2880_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2882_, v___y_2868_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
return v___x_2883_;
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_dec(v_a_2879_);
v___x_2884_ = lean_box(0);
v___x_2885_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2884_, v___y_2868_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
return v___x_2885_;
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
v_a_2886_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2878_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2878_);
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
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v_fvarId_2866_);
v_a_2894_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2876_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2876_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___lam__0___boxed(lean_object* v_fvarId_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Meta_AC_acNfHypTactic___lam__0(v_fvarId_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic(lean_object* v_fvarId_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___f_2923_; lean_object* v___x_2924_; 
v___f_2923_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acNfHypTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2923_, 0, v_fvarId_2913_);
v___x_2924_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2923_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___boxed(lean_object* v_fvarId_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Meta_AC_acNfHypTactic(v_fvarId_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
return v_res_2935_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_box(0);
v___x_2937_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg(){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___boxed(lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(lean_object* v_00_u03b1_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___boxed(lean_object* v_00_u03b1_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(v_00_u03b1_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(lean_object* v_as_2966_, size_t v_i_2967_, size_t v_stop_2968_, lean_object* v_b_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v___x_2979_; 
v___x_2979_ = lean_usize_dec_eq(v_i_2967_, v_stop_2968_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2980_ = lean_array_uget_borrowed(v_as_2966_, v_i_2967_);
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
lean_inc(v___y_2975_);
lean_inc_ref(v___y_2974_);
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
lean_inc(v___x_2980_);
v___x_2981_ = l_Lean_Meta_AC_acNfHypTactic(v___x_2980_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; size_t v___x_2983_; size_t v___x_2984_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref(v___x_2981_);
v___x_2983_ = ((size_t)1ULL);
v___x_2984_ = lean_usize_add(v_i_2967_, v___x_2983_);
v_i_2967_ = v___x_2984_;
v_b_2969_ = v_a_2982_;
goto _start;
}
else
{
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
return v___x_2981_;
}
}
else
{
lean_object* v___x_2986_; 
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_b_2969_);
return v___x_2986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1___boxed(lean_object* v_as_2987_, lean_object* v_i_2988_, lean_object* v_stop_2989_, lean_object* v_b_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
size_t v_i_boxed_3000_; size_t v_stop_boxed_3001_; lean_object* v_res_3002_; 
v_i_boxed_3000_ = lean_unbox_usize(v_i_2988_);
lean_dec(v_i_2988_);
v_stop_boxed_3001_ = lean_unbox_usize(v_stop_2989_);
lean_dec(v_stop_2989_);
v_res_3002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_as_2987_, v_i_boxed_3000_, v_stop_boxed_3001_, v_b_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec_ref(v_as_2987_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___lam__0(lean_object* v___y_3003_, lean_object* v___x_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
if (lean_obj_tag(v___y_3003_) == 0)
{
lean_object* v___x_3014_; 
lean_inc(v___y_3012_);
lean_inc_ref(v___y_3011_);
lean_inc(v___y_3010_);
lean_inc_ref(v___y_3009_);
lean_inc(v___y_3008_);
lean_inc_ref(v___y_3007_);
lean_inc(v___y_3006_);
lean_inc_ref(v___y_3005_);
v___x_3014_ = l_Lean_Meta_AC_acNfTargetTactic(v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v___x_3015_; 
lean_dec_ref(v___x_3014_);
v___x_3015_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3006_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref(v___x_3015_);
lean_inc(v___y_3012_);
lean_inc_ref(v___y_3011_);
lean_inc(v___y_3010_);
lean_inc_ref(v___y_3009_);
v___x_3017_ = l_Lean_MVarId_getNondepPropHyps(v_a_3016_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3038_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3038_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3038_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3022_ = lean_array_get_size(v_a_3018_);
v___x_3023_ = lean_box(0);
v___x_3024_ = lean_nat_dec_lt(v___x_3004_, v___x_3022_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3026_; 
lean_dec(v_a_3018_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3023_);
v___x_3026_ = v___x_3020_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3023_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
else
{
uint8_t v___x_3028_; 
v___x_3028_ = lean_nat_dec_le(v___x_3022_, v___x_3022_);
if (v___x_3028_ == 0)
{
if (v___x_3024_ == 0)
{
lean_object* v___x_3030_; 
lean_dec(v_a_3018_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3023_);
v___x_3030_ = v___x_3020_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3023_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
else
{
size_t v___x_3032_; size_t v___x_3033_; lean_object* v___x_3034_; 
lean_del_object(v___x_3020_);
v___x_3032_ = ((size_t)0ULL);
v___x_3033_ = lean_usize_of_nat(v___x_3022_);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3018_, v___x_3032_, v___x_3033_, v___x_3023_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v_a_3018_);
return v___x_3034_;
}
}
else
{
size_t v___x_3035_; size_t v___x_3036_; lean_object* v___x_3037_; 
lean_del_object(v___x_3020_);
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = lean_usize_of_nat(v___x_3022_);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3018_, v___x_3035_, v___x_3036_, v___x_3023_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v_a_3018_);
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
v_a_3039_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3017_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3017_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
v_a_3047_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3015_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3015_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v___x_3014_;
}
}
else
{
lean_object* v_hypotheses_3055_; uint8_t v_type_3056_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; 
v_hypotheses_3055_ = lean_ctor_get(v___y_3003_, 0);
lean_inc_ref(v_hypotheses_3055_);
v_type_3056_ = lean_ctor_get_uint8(v___y_3003_, sizeof(void*)*1);
lean_dec_ref(v___y_3003_);
if (v_type_3056_ == 0)
{
v___y_3058_ = v___y_3005_;
v___y_3059_ = v___y_3006_;
v___y_3060_ = v___y_3007_;
v___y_3061_ = v___y_3008_;
v___y_3062_ = v___y_3009_;
v___y_3063_ = v___y_3010_;
v___y_3064_ = v___y_3011_;
v___y_3065_ = v___y_3012_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3096_; 
lean_inc(v___y_3012_);
lean_inc_ref(v___y_3011_);
lean_inc(v___y_3010_);
lean_inc_ref(v___y_3009_);
lean_inc(v___y_3008_);
lean_inc_ref(v___y_3007_);
lean_inc(v___y_3006_);
lean_inc_ref(v___y_3005_);
v___x_3096_ = l_Lean_Meta_AC_acNfTargetTactic(v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_dec_ref(v___x_3096_);
v___y_3058_ = v___y_3005_;
v___y_3059_ = v___y_3006_;
v___y_3060_ = v___y_3007_;
v___y_3061_ = v___y_3008_;
v___y_3062_ = v___y_3009_;
v___y_3063_ = v___y_3010_;
v___y_3064_ = v___y_3011_;
v___y_3065_ = v___y_3012_;
goto v___jp_3057_;
}
else
{
lean_dec_ref(v_hypotheses_3055_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v___x_3096_;
}
}
v___jp_3057_:
{
lean_object* v___x_3066_; 
lean_inc(v___y_3065_);
lean_inc_ref(v___y_3064_);
lean_inc(v___y_3063_);
lean_inc_ref(v___y_3062_);
lean_inc(v___y_3061_);
lean_inc_ref(v___y_3060_);
lean_inc(v___y_3059_);
lean_inc_ref(v___y_3058_);
v___x_3066_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3055_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3087_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3087_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3087_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3071_ = lean_array_get_size(v_a_3067_);
v___x_3072_ = lean_box(0);
v___x_3073_ = lean_nat_dec_lt(v___x_3004_, v___x_3071_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3075_; 
lean_dec(v_a_3067_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3072_);
v___x_3075_ = v___x_3069_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3072_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
else
{
uint8_t v___x_3077_; 
v___x_3077_ = lean_nat_dec_le(v___x_3071_, v___x_3071_);
if (v___x_3077_ == 0)
{
if (v___x_3073_ == 0)
{
lean_object* v___x_3079_; 
lean_dec(v_a_3067_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3072_);
v___x_3079_ = v___x_3069_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3072_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
else
{
size_t v___x_3081_; size_t v___x_3082_; lean_object* v___x_3083_; 
lean_del_object(v___x_3069_);
v___x_3081_ = ((size_t)0ULL);
v___x_3082_ = lean_usize_of_nat(v___x_3071_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3067_, v___x_3081_, v___x_3082_, v___x_3072_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v_a_3067_);
return v___x_3083_;
}
}
else
{
size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
lean_del_object(v___x_3069_);
v___x_3084_ = ((size_t)0ULL);
v___x_3085_ = lean_usize_of_nat(v___x_3071_);
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3067_, v___x_3084_, v___x_3085_, v___x_3072_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v_a_3067_);
return v___x_3086_;
}
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
v_a_3088_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3066_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3066_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___lam__0___boxed(lean_object* v___y_3097_, lean_object* v___x_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Meta_AC_evalNf0___lam__0(v___y_3097_, v___x_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___x_3098_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0(lean_object* v_stx_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3127_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___closed__1));
lean_inc(v_stx_3117_);
v___x_3128_ = l_Lean_Syntax_isOfKind(v_stx_3117_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; 
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
lean_dec(v_a_3121_);
lean_dec_ref(v_a_3120_);
lean_dec(v_a_3119_);
lean_dec_ref(v_a_3118_);
lean_dec(v_stx_3117_);
v___x_3129_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v___x_3129_;
}
else
{
lean_object* v___x_3130_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___x_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v___x_3130_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_unsigned_to_nat(1u);
v___x_3144_ = l_Lean_Syntax_getArg(v_stx_3117_, v___x_3143_);
lean_dec(v_stx_3117_);
v___x_3145_ = l_Lean_Syntax_isNone(v___x_3144_);
if (v___x_3145_ == 0)
{
uint8_t v___x_3146_; 
lean_inc(v___x_3144_);
v___x_3146_ = l_Lean_Syntax_matchesNull(v___x_3144_, v___x_3143_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_dec(v___x_3144_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
lean_dec(v_a_3121_);
lean_dec_ref(v_a_3120_);
lean_dec(v_a_3119_);
lean_dec_ref(v_a_3118_);
v___x_3147_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v___x_3147_;
}
else
{
lean_object* v_loc_x3f_3148_; lean_object* v___x_3149_; 
v_loc_x3f_3148_ = l_Lean_Syntax_getArg(v___x_3144_, v___x_3130_);
lean_dec(v___x_3144_);
v___x_3149_ = l_Lean_Elab_Tactic_expandLocation(v_loc_x3f_3148_);
lean_dec(v_loc_x3f_3148_);
v___y_3132_ = v_a_3119_;
v___y_3133_ = v_a_3125_;
v___y_3134_ = v_a_3124_;
v___y_3135_ = v_a_3123_;
v___y_3136_ = v_a_3121_;
v___y_3137_ = v_a_3122_;
v___y_3138_ = v_a_3120_;
v___y_3139_ = v_a_3118_;
v___y_3140_ = v___x_3149_;
goto v___jp_3131_;
}
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec(v___x_3144_);
v___x_3150_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___closed__2));
v___x_3151_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*1, v___x_3128_);
v___y_3132_ = v_a_3119_;
v___y_3133_ = v_a_3125_;
v___y_3134_ = v_a_3124_;
v___y_3135_ = v_a_3123_;
v___y_3136_ = v_a_3121_;
v___y_3137_ = v_a_3122_;
v___y_3138_ = v_a_3120_;
v___y_3139_ = v_a_3118_;
v___y_3140_ = v___x_3151_;
goto v___jp_3131_;
}
v___jp_3131_:
{
lean_object* v___y_3141_; lean_object* v___x_3142_; 
v___y_3141_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_evalNf0___lam__0___boxed), 11, 2);
lean_closure_set(v___y_3141_, 0, v___y_3140_);
lean_closure_set(v___y_3141_, 1, v___x_3130_);
v___x_3142_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_3141_, v___y_3139_, v___y_3132_, v___y_3138_, v___y_3136_, v___y_3137_, v___y_3135_, v___y_3134_, v___y_3133_);
return v___x_3142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___boxed(lean_object* v_stx_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_Meta_AC_evalNf0(v_stx_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1(){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3170_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3171_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___closed__1));
v___x_3172_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1));
v___x_3173_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_evalNf0___boxed), 10, 0);
v___x_3174_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3170_, v___x_3171_, v___x_3172_, v___x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___boxed(lean_object* v_a_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
return v_res_3176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_unsigned_to_nat(4236260923u);
v___x_3233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_));
v___x_3234_ = l_Lean_Name_num___override(v___x_3233_, v___x_3232_);
return v___x_3234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_));
v___x_3237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3238_ = l_Lean_Name_str___override(v___x_3237_, v___x_3236_);
return v___x_3238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_));
v___x_3241_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3242_ = l_Lean_Name_str___override(v___x_3241_, v___x_3240_);
return v___x_3242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = lean_unsigned_to_nat(2u);
v___x_3244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3245_ = l_Lean_Name_num___override(v___x_3244_, v___x_3243_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3247_; uint8_t v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3247_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__2));
v___x_3248_ = 0;
v___x_3249_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3250_ = l_Lean_registerTraceClass(v___x_3247_, v___x_3248_, v___x_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2____boxed(lean_object* v_a_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_();
return v_res_3252_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_AC_instInhabitedPreContext_default = _init_l_Lean_Meta_AC_instInhabitedPreContext_default();
lean_mark_persistent(l_Lean_Meta_AC_instInhabitedPreContext_default);
l_Lean_Meta_AC_instInhabitedPreContext = _init_l_Lean_Meta_AC_instInhabitedPreContext();
lean_mark_persistent(l_Lean_Meta_AC_instInhabitedPreContext);
res = l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_AC_Main(builtin);
}
#ifdef __cplusplus
}
#endif
