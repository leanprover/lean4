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
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_getInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_AC_getInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_AC_getInstance___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_AC_getInstance___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_getInstance___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_AC_getInstance___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_AC_getInstance___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_AC_getInstance___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "got instance"};
static const lean_object* l_Lean_Meta_AC_getInstance___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_AC_getInstance___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_AC_getInstance___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_getInstance___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AC_getInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_AC_getInstance___closed__0 = (const lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value;
static const lean_string_object l_Lean_Meta_AC_getInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AC"};
static const lean_object* l_Lean_Meta_AC_getInstance___closed__1 = (const lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value;
static const lean_ctor_object l_Lean_Meta_AC_getInstance___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_AC_getInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_getInstance___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 102, 180, 37, 89, 238, 212, 46)}};
static const lean_object* l_Lean_Meta_AC_getInstance___closed__2 = (const lean_object*)&l_Lean_Meta_AC_getInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_AC_getInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_getInstance___closed__3;
static const lean_string_object l_Lean_Meta_AC_getInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "trying: "};
static const lean_object* l_Lean_Meta_AC_getInstance___closed__4 = (const lean_object*)&l_Lean_Meta_AC_getInstance___closed__4_value;
static lean_once_cell_t l_Lean_Meta_AC_getInstance___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AC_getInstance___closed__5;
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
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "acRfl"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 10, 210, 32, 196, 152, 20, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "acRflTactic"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 50, 124, 4, 240, 103, 254, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 10, 211, 220, 137, 99, 157, 23)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(176) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_evalNf0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_evalNf0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_AC_evalNf0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_evalNf0___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_AC_evalNf0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 212, 39, 12, 162, 76, 172, 19)}};
static const lean_object* l_Lean_Meta_AC_evalNf0___closed__1 = (const lean_object*)&l_Lean_Meta_AC_evalNf0___closed__1_value;
static const lean_array_object l_Lean_Meta_AC_evalNf0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_AC_evalNf0___closed__2 = (const lean_object*)&l_Lean_Meta_AC_evalNf0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalNf0"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 50, 124, 4, 240, 103, 254, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 59, 59, 44, 240, 219, 207, 54)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_AC_getInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(146, 225, 162, 38, 239, 104, 56, 82)}};
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
v___x_34_ = lean_array_get(v___x_33_, v_snd_32_, v_x_31_);
lean_dec(v___x_33_);
v___x_35_ = lean_unbox(v___x_34_);
lean_dec(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2___boxed(lean_object* v___x_36_, lean_object* v_ctx_37_, lean_object* v_x_38_){
_start:
{
uint8_t v___x_54__boxed_39_; uint8_t v_res_40_; lean_object* v_r_41_; 
v___x_54__boxed_39_ = lean_unbox(v___x_36_);
v_res_40_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2(v___x_54__boxed_39_, v_ctx_37_, v_x_38_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(lean_object* v_msgData_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; lean_object* v_env_87_; lean_object* v___x_88_; lean_object* v_mctx_89_; lean_object* v_lctx_90_; lean_object* v_options_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_86_ = lean_st_ref_get(v___y_84_);
v_env_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc_ref(v_env_87_);
lean_dec(v___x_86_);
v___x_88_ = lean_st_ref_get(v___y_82_);
v_mctx_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_ref(v_mctx_89_);
lean_dec(v___x_88_);
v_lctx_90_ = lean_ctor_get(v___y_81_, 2);
v_options_91_ = lean_ctor_get(v___y_83_, 2);
lean_inc_ref(v_options_91_);
lean_inc_ref(v_lctx_90_);
v___x_92_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_92_, 0, v_env_87_);
lean_ctor_set(v___x_92_, 1, v_mctx_89_);
lean_ctor_set(v___x_92_, 2, v_lctx_90_);
lean_ctor_set(v___x_92_, 3, v_options_91_);
v___x_93_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v_msgData_80_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0___boxed(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(v_msgData_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_101_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0(void){
_start:
{
lean_object* v___x_102_; double v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_float_of_nat(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(lean_object* v_cls_107_, lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_ref_114_; lean_object* v___x_115_; lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_160_; 
v_ref_114_ = lean_ctor_get(v___y_111_, 5);
v___x_115_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(v_msg_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_160_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_160_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_160_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v_traceState_121_; lean_object* v_env_122_; lean_object* v_nextMacroScope_123_; lean_object* v_ngen_124_; lean_object* v_auxDeclNGen_125_; lean_object* v_cache_126_; lean_object* v_messages_127_; lean_object* v_infoState_128_; lean_object* v_snapshotTasks_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_159_; 
v___x_120_ = lean_st_ref_take(v___y_112_);
v_traceState_121_ = lean_ctor_get(v___x_120_, 4);
v_env_122_ = lean_ctor_get(v___x_120_, 0);
v_nextMacroScope_123_ = lean_ctor_get(v___x_120_, 1);
v_ngen_124_ = lean_ctor_get(v___x_120_, 2);
v_auxDeclNGen_125_ = lean_ctor_get(v___x_120_, 3);
v_cache_126_ = lean_ctor_get(v___x_120_, 5);
v_messages_127_ = lean_ctor_get(v___x_120_, 6);
v_infoState_128_ = lean_ctor_get(v___x_120_, 7);
v_snapshotTasks_129_ = lean_ctor_get(v___x_120_, 8);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_159_ == 0)
{
v___x_131_ = v___x_120_;
v_isShared_132_ = v_isSharedCheck_159_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_snapshotTasks_129_);
lean_inc(v_infoState_128_);
lean_inc(v_messages_127_);
lean_inc(v_cache_126_);
lean_inc(v_traceState_121_);
lean_inc(v_auxDeclNGen_125_);
lean_inc(v_ngen_124_);
lean_inc(v_nextMacroScope_123_);
lean_inc(v_env_122_);
lean_dec(v___x_120_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_159_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
uint64_t v_tid_133_; lean_object* v_traces_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_158_; 
v_tid_133_ = lean_ctor_get_uint64(v_traceState_121_, sizeof(void*)*1);
v_traces_134_ = lean_ctor_get(v_traceState_121_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_traceState_121_);
if (v_isSharedCheck_158_ == 0)
{
v___x_136_ = v_traceState_121_;
v_isShared_137_ = v_isSharedCheck_158_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_traces_134_);
lean_dec(v_traceState_121_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_158_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; double v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_138_ = lean_box(0);
v___x_139_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0);
v___x_140_ = 0;
v___x_141_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__1));
v___x_142_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_142_, 0, v_cls_107_);
lean_ctor_set(v___x_142_, 1, v___x_138_);
lean_ctor_set(v___x_142_, 2, v___x_141_);
lean_ctor_set_float(v___x_142_, sizeof(void*)*3, v___x_139_);
lean_ctor_set_float(v___x_142_, sizeof(void*)*3 + 8, v___x_139_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*3 + 16, v___x_140_);
v___x_143_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__2));
v___x_144_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v_a_116_);
lean_ctor_set(v___x_144_, 2, v___x_143_);
lean_inc(v_ref_114_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v_ref_114_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = l_Lean_PersistentArray_push___redArg(v_traces_134_, v___x_145_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_146_);
v___x_148_ = v___x_136_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_146_);
lean_ctor_set_uint64(v_reuseFailAlloc_157_, sizeof(void*)*1, v_tid_133_);
v___x_148_ = v_reuseFailAlloc_157_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_150_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v___x_148_);
v___x_150_ = v___x_131_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_env_122_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_nextMacroScope_123_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_ngen_124_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_auxDeclNGen_125_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_156_, 5, v_cache_126_);
lean_ctor_set(v_reuseFailAlloc_156_, 6, v_messages_127_);
lean_ctor_set(v_reuseFailAlloc_156_, 7, v_infoState_128_);
lean_ctor_set(v_reuseFailAlloc_156_, 8, v_snapshotTasks_129_);
v___x_150_ = v_reuseFailAlloc_156_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_151_ = lean_st_ref_put(v___y_112_, v___x_150_);
v___x_152_ = lean_box(0);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_152_);
v___x_154_ = v___x_118_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___boxed(lean_object* v_cls_161_, lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(v_cls_161_, v_msg_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Meta_AC_getInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___lam__0___closed__2));
v___x_174_ = l_Lean_stringToMessageData(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___lam__0(lean_object* v_a_175_, lean_object* v___x_176_, lean_object* v_____r_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_box(0);
v___x_184_ = l_Lean_Meta_synthInstance(v_a_175_, v___x_183_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_211_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_211_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_211_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_211_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_options_195_; uint8_t v_hasTrace_196_; 
v_options_195_ = lean_ctor_get(v___y_180_, 2);
v_hasTrace_196_ = lean_ctor_get_uint8(v_options_195_, sizeof(void*)*1);
if (v_hasTrace_196_ == 0)
{
lean_dec(v___x_176_);
goto v___jp_189_;
}
else
{
lean_object* v_inheritedTraceOptions_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_inheritedTraceOptions_197_ = lean_ctor_get(v___y_180_, 13);
v___x_198_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___lam__0___closed__1));
lean_inc(v___x_176_);
v___x_199_ = l_Lean_Name_append(v___x_198_, v___x_176_);
v___x_200_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_197_, v_options_195_, v___x_199_);
lean_dec(v___x_199_);
if (v___x_200_ == 0)
{
lean_dec(v___x_176_);
goto v___jp_189_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_obj_once(&l_Lean_Meta_AC_getInstance___lam__0___closed__3, &l_Lean_Meta_AC_getInstance___lam__0___closed__3_once, _init_l_Lean_Meta_AC_getInstance___lam__0___closed__3);
v___x_202_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(v___x_176_, v___x_201_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_dec_ref_known(v___x_202_, 1);
goto v___jp_189_;
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_del_object(v___x_187_);
lean_dec(v_a_185_);
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
v___jp_189_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_a_185_);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_191_);
v___x_193_ = v___x_187_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
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
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v___x_176_);
v_a_212_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_184_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_184_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___lam__0___boxed(lean_object* v_a_220_, lean_object* v___x_221_, lean_object* v_____r_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_220_, v___x_221_, v_____r_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_228_;
}
}
static lean_object* _init_l_Lean_Meta_AC_getInstance___closed__3(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__2));
v___x_235_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___lam__0___closed__1));
v___x_236_ = l_Lean_Name_append(v___x_235_, v___x_234_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Meta_AC_getInstance___closed__5(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__4));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance(lean_object* v_cls_240_, lean_object* v_exprs_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___y_248_; uint8_t v___y_249_; lean_object* v_a_254_; lean_object* v___y_258_; lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_mkAppM(v_cls_240_, v_exprs_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_options_270_; lean_object* v_a_271_; lean_object* v_inheritedTraceOptions_272_; uint8_t v_hasTrace_273_; lean_object* v___x_274_; 
v_options_270_ = lean_ctor_get(v_a_244_, 2);
v_a_271_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_269_, 1);
v_inheritedTraceOptions_272_ = lean_ctor_get(v_a_244_, 13);
v_hasTrace_273_ = lean_ctor_get_uint8(v_options_270_, sizeof(void*)*1);
v___x_274_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__2));
if (v_hasTrace_273_ == 0)
{
goto v___jp_275_;
}
else
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_obj_once(&l_Lean_Meta_AC_getInstance___closed__3, &l_Lean_Meta_AC_getInstance___closed__3_once, _init_l_Lean_Meta_AC_getInstance___closed__3);
v___x_279_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_272_, v_options_270_, v___x_278_);
if (v___x_279_ == 0)
{
goto v___jp_275_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = lean_obj_once(&l_Lean_Meta_AC_getInstance___closed__5, &l_Lean_Meta_AC_getInstance___closed__5_once, _init_l_Lean_Meta_AC_getInstance___closed__5);
lean_inc(v_a_271_);
v___x_281_ = l_Lean_indentExpr(v_a_271_);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(v___x_274_, v___x_282_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_283_, 1);
v___x_285_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_271_, v___x_274_, v_a_284_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
v___y_258_ = v___x_285_;
goto v___jp_257_;
}
else
{
lean_object* v_a_286_; 
lean_dec(v_a_271_);
v_a_286_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_283_, 1);
v_a_254_ = v_a_286_;
goto v___jp_253_;
}
}
}
v___jp_275_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(0);
v___x_277_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_271_, v___x_274_, v___x_276_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
v___y_258_ = v___x_277_;
goto v___jp_257_;
}
}
else
{
lean_object* v_a_287_; 
v_a_287_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___x_269_, 1);
v_a_254_ = v_a_287_;
goto v___jp_253_;
}
v___jp_247_:
{
if (v___y_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref(v___y_248_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___y_248_);
return v___x_252_;
}
}
v___jp_253_:
{
uint8_t v___x_255_; 
v___x_255_ = l_Lean_Exception_isInterrupt(v_a_254_);
if (v___x_255_ == 0)
{
uint8_t v___x_256_; 
lean_inc_ref(v_a_254_);
v___x_256_ = l_Lean_Exception_isRuntime(v_a_254_);
v___y_248_ = v_a_254_;
v___y_249_ = v___x_256_;
goto v___jp_247_;
}
else
{
v___y_248_ = v_a_254_;
v___y_249_ = v___x_255_;
goto v___jp_247_;
}
}
v___jp_257_:
{
if (lean_obj_tag(v___y_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v_a_259_ = lean_ctor_get(v___y_258_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___y_258_);
if (v_isSharedCheck_267_ == 0)
{
v___x_261_ = v___y_258_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___y_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v_a_263_; lean_object* v___x_265_; 
v_a_263_ = lean_ctor_get(v_a_259_, 0);
lean_inc(v_a_263_);
lean_dec(v_a_259_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v_a_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___y_258_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___y_258_, 1);
v_a_254_ = v_a_268_;
goto v___jp_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___boxed(lean_object* v_cls_288_, lean_object* v_exprs_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_AC_getInstance(v_cls_288_, v_exprs_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_preContext(lean_object* v_expr_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_315_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__2));
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_mk_empty_array_with_capacity(v___x_316_);
lean_inc_ref(v_expr_309_);
v___x_318_ = lean_array_push(v___x_317_, v_expr_309_);
lean_inc_ref(v___x_318_);
v___x_319_ = l_Lean_Meta_AC_getInstance(v___x_315_, v___x_318_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_367_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_367_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_367_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_367_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
if (lean_obj_tag(v_a_320_) == 1)
{
lean_object* v_val_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_362_; 
lean_del_object(v___x_322_);
v_val_324_ = lean_ctor_get(v_a_320_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v_a_320_);
if (v_isSharedCheck_362_ == 0)
{
v___x_326_ = v_a_320_;
v_isShared_327_ = v_isSharedCheck_362_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_val_324_);
lean_dec(v_a_320_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_362_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__4));
lean_inc_ref(v___x_318_);
v___x_329_ = l_Lean_Meta_AC_getInstance(v___x_328_, v___x_318_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__6));
v___x_332_ = l_Lean_Meta_AC_getInstance(v___x_331_, v___x_318_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_345_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_345_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_345_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_345_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_expr_309_);
lean_ctor_set(v___x_338_, 2, v_val_324_);
lean_ctor_set(v___x_338_, 3, v_a_330_);
lean_ctor_set(v___x_338_, 4, v_a_333_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_338_);
v___x_340_ = v___x_326_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_340_);
v___x_342_ = v___x_335_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_a_330_);
lean_del_object(v___x_326_);
lean_dec(v_val_324_);
lean_dec_ref(v_expr_309_);
v_a_346_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_332_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_332_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_del_object(v___x_326_);
lean_dec(v_val_324_);
lean_dec_ref(v___x_318_);
lean_dec_ref(v_expr_309_);
v_a_354_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_329_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_329_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_365_; 
lean_dec(v_a_320_);
lean_dec_ref(v___x_318_);
lean_dec_ref(v_expr_309_);
v___x_363_ = lean_box(0);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_363_);
v___x_365_ = v___x_322_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v___x_318_);
lean_dec_ref(v_expr_309_);
v_a_368_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_319_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_319_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_preContext___boxed(lean_object* v_expr_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_AC_preContext(v_expr_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx(lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(0u);
return v___x_384_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(1u);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx___boxed(lean_object* v_x_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_AC_PreExpr_ctorIdx(v_x_386_);
lean_dec_ref(v_x_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim___redArg(lean_object* v_t_388_, lean_object* v_k_389_){
_start:
{
if (lean_obj_tag(v_t_388_) == 0)
{
lean_object* v_lhs_390_; lean_object* v_rhs_391_; lean_object* v___x_392_; 
v_lhs_390_ = lean_ctor_get(v_t_388_, 0);
lean_inc_ref(v_lhs_390_);
v_rhs_391_ = lean_ctor_get(v_t_388_, 1);
lean_inc_ref(v_rhs_391_);
lean_dec_ref_known(v_t_388_, 2);
v___x_392_ = lean_apply_2(v_k_389_, v_lhs_390_, v_rhs_391_);
return v___x_392_;
}
else
{
lean_object* v_e_393_; lean_object* v___x_394_; 
v_e_393_ = lean_ctor_get(v_t_388_, 0);
lean_inc_ref(v_e_393_);
lean_dec_ref_known(v_t_388_, 1);
v___x_394_ = lean_apply_1(v_k_389_, v_e_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim(lean_object* v_motive_395_, lean_object* v_ctorIdx_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_k_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_397_, v_k_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim___boxed(lean_object* v_motive_401_, lean_object* v_ctorIdx_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_k_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_AC_PreExpr_ctorElim(v_motive_401_, v_ctorIdx_402_, v_t_403_, v_h_404_, v_k_405_);
lean_dec(v_ctorIdx_402_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_op_elim___redArg(lean_object* v_t_407_, lean_object* v_op_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_407_, v_op_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_op_elim(lean_object* v_motive_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_op_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_411_, v_op_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_var_elim___redArg(lean_object* v_t_415_, lean_object* v_var_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_415_, v_var_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_var_elim(lean_object* v_motive_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_var_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_419_, v_var_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_bin(lean_object* v_op_423_, lean_object* v_l_424_, lean_object* v_r_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_Lean_Expr_app___override(v_op_423_, v_l_424_);
v___x_427_ = l_Lean_Expr_app___override(v___x_426_, v_r_425_);
return v___x_427_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(lean_object* v_a_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
else
{
lean_object* v_key_431_; lean_object* v_tail_432_; uint8_t v___x_433_; 
v_key_431_ = lean_ctor_get(v_x_429_, 0);
v_tail_432_ = lean_ctor_get(v_x_429_, 2);
v___x_433_ = lean_expr_eqv(v_key_431_, v_a_428_);
if (v___x_433_ == 0)
{
v_x_429_ = v_tail_432_;
goto _start;
}
else
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg___boxed(lean_object* v_a_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_435_, v_x_436_);
lean_dec(v_x_436_);
lean_dec_ref(v_a_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
return v_x_439_;
}
else
{
lean_object* v_key_441_; lean_object* v_value_442_; lean_object* v_tail_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_466_; 
v_key_441_ = lean_ctor_get(v_x_440_, 0);
v_value_442_ = lean_ctor_get(v_x_440_, 1);
v_tail_443_ = lean_ctor_get(v_x_440_, 2);
v_isSharedCheck_466_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_466_ == 0)
{
v___x_445_ = v_x_440_;
v_isShared_446_ = v_isSharedCheck_466_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_tail_443_);
lean_inc(v_value_442_);
lean_inc(v_key_441_);
lean_dec(v_x_440_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_466_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v_fold_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; size_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_447_ = lean_array_get_size(v_x_439_);
v___x_448_ = l_Lean_Expr_hash(v_key_441_);
v___x_449_ = 32ULL;
v___x_450_ = lean_uint64_shift_right(v___x_448_, v___x_449_);
v_fold_451_ = lean_uint64_xor(v___x_448_, v___x_450_);
v___x_452_ = 16ULL;
v___x_453_ = lean_uint64_shift_right(v_fold_451_, v___x_452_);
v___x_454_ = lean_uint64_xor(v_fold_451_, v___x_453_);
v___x_455_ = lean_uint64_to_usize(v___x_454_);
v___x_456_ = lean_usize_of_nat(v___x_447_);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_sub(v___x_456_, v___x_457_);
v___x_459_ = lean_usize_land(v___x_455_, v___x_458_);
v___x_460_ = lean_array_uget_borrowed(v_x_439_, v___x_459_);
lean_inc(v___x_460_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 2, v___x_460_);
v___x_462_ = v___x_445_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_key_441_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_value_442_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v___x_460_);
v___x_462_ = v_reuseFailAlloc_465_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; 
v___x_463_ = lean_array_uset(v_x_439_, v___x_459_, v___x_462_);
v_x_439_ = v___x_463_;
v_x_440_ = v_tail_443_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_467_, lean_object* v_source_468_, lean_object* v_target_469_){
_start:
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_array_get_size(v_source_468_);
v___x_471_ = lean_nat_dec_lt(v_i_467_, v___x_470_);
if (v___x_471_ == 0)
{
lean_dec_ref(v_source_468_);
lean_dec(v_i_467_);
return v_target_469_;
}
else
{
lean_object* v_es_472_; lean_object* v___x_473_; lean_object* v_source_474_; lean_object* v_target_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_es_472_ = lean_array_fget(v_source_468_, v_i_467_);
v___x_473_ = lean_box(0);
v_source_474_ = lean_array_fset(v_source_468_, v_i_467_, v___x_473_);
v_target_475_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_469_, v_es_472_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_i_467_, v___x_476_);
lean_dec(v_i_467_);
v_i_467_ = v___x_477_;
v_source_468_ = v_source_474_;
v_target_469_ = v_target_475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(lean_object* v_data_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_nbuckets_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_480_ = lean_array_get_size(v_data_479_);
v___x_481_ = lean_unsigned_to_nat(2u);
v_nbuckets_482_ = lean_nat_mul(v___x_480_, v___x_481_);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_box(0);
v___x_485_ = lean_mk_array(v_nbuckets_482_, v___x_484_);
v___x_486_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(v___x_483_, v_data_479_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(lean_object* v_m_487_, lean_object* v_a_488_, lean_object* v_b_489_){
_start:
{
lean_object* v_size_490_; lean_object* v_buckets_491_; lean_object* v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v_fold_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v_bkt_505_; uint8_t v___x_506_; 
v_size_490_ = lean_ctor_get(v_m_487_, 0);
v_buckets_491_ = lean_ctor_get(v_m_487_, 1);
v___x_492_ = lean_array_get_size(v_buckets_491_);
v___x_493_ = l_Lean_Expr_hash(v_a_488_);
v___x_494_ = 32ULL;
v___x_495_ = lean_uint64_shift_right(v___x_493_, v___x_494_);
v_fold_496_ = lean_uint64_xor(v___x_493_, v___x_495_);
v___x_497_ = 16ULL;
v___x_498_ = lean_uint64_shift_right(v_fold_496_, v___x_497_);
v___x_499_ = lean_uint64_xor(v_fold_496_, v___x_498_);
v___x_500_ = lean_uint64_to_usize(v___x_499_);
v___x_501_ = lean_usize_of_nat(v___x_492_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_sub(v___x_501_, v___x_502_);
v___x_504_ = lean_usize_land(v___x_500_, v___x_503_);
v_bkt_505_ = lean_array_uget_borrowed(v_buckets_491_, v___x_504_);
v___x_506_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_488_, v_bkt_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_527_; 
lean_inc_ref(v_buckets_491_);
lean_inc(v_size_490_);
v_isSharedCheck_527_ = !lean_is_exclusive(v_m_487_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; lean_object* v_unused_529_; 
v_unused_528_ = lean_ctor_get(v_m_487_, 1);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_m_487_, 0);
lean_dec(v_unused_529_);
v___x_508_ = v_m_487_;
v_isShared_509_ = v_isSharedCheck_527_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_m_487_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_527_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v_size_x27_511_; lean_object* v___x_512_; lean_object* v_buckets_x27_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v_size_x27_511_ = lean_nat_add(v_size_490_, v___x_510_);
lean_dec(v_size_490_);
lean_inc(v_bkt_505_);
v___x_512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_512_, 0, v_a_488_);
lean_ctor_set(v___x_512_, 1, v_b_489_);
lean_ctor_set(v___x_512_, 2, v_bkt_505_);
v_buckets_x27_513_ = lean_array_uset(v_buckets_491_, v___x_504_, v___x_512_);
v___x_514_ = lean_unsigned_to_nat(4u);
v___x_515_ = lean_nat_mul(v_size_x27_511_, v___x_514_);
v___x_516_ = lean_unsigned_to_nat(3u);
v___x_517_ = lean_nat_div(v___x_515_, v___x_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_array_get_size(v_buckets_x27_513_);
v___x_519_ = lean_nat_dec_le(v___x_517_, v___x_518_);
lean_dec(v___x_517_);
if (v___x_519_ == 0)
{
lean_object* v_val_520_; lean_object* v___x_522_; 
v_val_520_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_buckets_x27_513_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_val_520_);
lean_ctor_set(v___x_508_, 0, v_size_x27_511_);
v___x_522_ = v___x_508_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_size_x27_511_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_val_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_object* v___x_525_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_buckets_x27_513_);
lean_ctor_set(v___x_508_, 0, v_size_x27_511_);
v___x_525_ = v___x_508_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_size_x27_511_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_buckets_x27_513_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_dec(v_b_489_);
lean_dec_ref(v_a_488_);
return v_m_487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(lean_object* v_op_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_e_539_; lean_object* v___y_540_; 
if (lean_obj_tag(v_a_531_) == 5)
{
lean_object* v_fn_546_; 
v_fn_546_ = lean_ctor_get(v_a_531_, 0);
if (lean_obj_tag(v_fn_546_) == 5)
{
lean_object* v_arg_547_; lean_object* v_fn_548_; lean_object* v_arg_549_; lean_object* v___x_550_; 
v_arg_547_ = lean_ctor_get(v_a_531_, 1);
v_fn_548_ = lean_ctor_get(v_fn_546_, 0);
v_arg_549_ = lean_ctor_get(v_fn_546_, 1);
lean_inc_ref(v_fn_548_);
lean_inc_ref(v_op_530_);
v___x_550_ = l_Lean_Meta_isExprDefEq(v_op_530_, v_fn_548_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_592_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_592_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_592_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_592_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
uint8_t v___x_555_; 
v___x_555_ = lean_unbox(v_a_551_);
lean_dec(v_a_551_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec_ref(v_op_530_);
v___x_556_ = lean_box(0);
lean_inc_ref(v_a_531_);
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v_a_532_, v_a_531_, v___x_556_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v_a_531_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_559_);
v___x_561_ = v___x_553_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
else
{
lean_object* v___x_563_; 
lean_inc_ref(v_arg_549_);
lean_inc_ref(v_arg_547_);
lean_del_object(v___x_553_);
lean_dec_ref_known(v_a_531_, 2);
lean_inc_ref(v_op_530_);
v___x_563_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_530_, v_arg_549_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_591_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v_fst_565_ = lean_ctor_get(v_a_564_, 0);
v_snd_566_ = lean_ctor_get(v_a_564_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_a_564_);
if (v_isSharedCheck_591_ == 0)
{
v___x_568_ = v_a_564_;
v_isShared_569_ = v_isSharedCheck_591_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snd_566_);
lean_inc(v_fst_565_);
lean_dec(v_a_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_591_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; 
v___x_570_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_530_, v_arg_547_, v_snd_566_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_590_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_590_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_590_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_590_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_589_; 
v_fst_575_ = lean_ctor_get(v_a_571_, 0);
v_snd_576_ = lean_ctor_get(v_a_571_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_a_571_);
if (v_isSharedCheck_589_ == 0)
{
v___x_578_ = v_a_571_;
v_isShared_579_ = v_isSharedCheck_589_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snd_576_);
lean_inc(v_fst_575_);
lean_dec(v_a_571_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_589_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 1, v_fst_575_);
v___x_581_ = v___x_568_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_fst_565_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_fst_575_);
v___x_581_ = v_reuseFailAlloc_588_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_581_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_snd_576_);
v___x_583_ = v_reuseFailAlloc_587_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_585_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_583_);
v___x_585_ = v___x_573_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
return v___x_570_;
}
}
}
else
{
lean_dec_ref(v_arg_547_);
lean_dec_ref(v_op_530_);
return v___x_563_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref_known(v_a_531_, 2);
lean_dec_ref(v_a_532_);
lean_dec_ref(v_op_530_);
v_a_593_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_550_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_550_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_dec_ref(v_op_530_);
v_e_539_ = v_a_531_;
v___y_540_ = v_a_532_;
goto v___jp_538_;
}
}
else
{
lean_dec_ref(v_op_530_);
v_e_539_ = v_a_531_;
v___y_540_ = v_a_532_;
goto v___jp_538_;
}
v___jp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_541_ = lean_box(0);
lean_inc_ref(v_e_539_);
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v___y_540_, v_e_539_, v___x_541_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_e_539_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_542_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr___boxed(lean_object* v_op_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0(lean_object* v_00_u03b2_610_, lean_object* v_m_611_, lean_object* v_a_612_, lean_object* v_b_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v_m_611_, v_a_612_, v_b_613_);
return v___x_614_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(lean_object* v_00_u03b2_615_, lean_object* v_a_616_, lean_object* v_x_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_616_, v_x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_619_, lean_object* v_a_620_, lean_object* v_x_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(v_00_u03b2_619_, v_a_620_, v_x_621_);
lean_dec(v_x_621_);
lean_dec_ref(v_a_620_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1(lean_object* v_00_u03b2_624_, lean_object* v_data_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_data_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_627_, lean_object* v_i_628_, lean_object* v_source_629_, lean_object* v_target_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(v_i_628_, v_source_629_, v_target_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_633_, v_x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(lean_object* v_varMap_636_, lean_object* v_a_637_){
_start:
{
if (lean_obj_tag(v_a_637_) == 0)
{
lean_object* v_lhs_638_; lean_object* v_rhs_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_648_; 
v_lhs_638_ = lean_ctor_get(v_a_637_, 0);
v_rhs_639_ = lean_ctor_get(v_a_637_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_a_637_);
if (v_isSharedCheck_648_ == 0)
{
v___x_641_ = v_a_637_;
v_isShared_642_ = v_isSharedCheck_648_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_rhs_639_);
lean_inc(v_lhs_638_);
lean_dec(v_a_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_648_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
lean_inc_ref(v_varMap_636_);
v___x_643_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(v_varMap_636_, v_lhs_638_);
v___x_644_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(v_varMap_636_, v_rhs_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 1);
lean_ctor_set(v___x_641_, 1, v___x_644_);
lean_ctor_set(v___x_641_, 0, v___x_643_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
else
{
lean_object* v_e_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
v_e_649_ = lean_ctor_get(v_a_637_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_a_637_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v_a_637_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_e_649_);
lean_dec(v_a_637_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_apply_1(v_varMap_636_, v_e_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 0);
lean_ctor_set(v___x_651_, 0, v___x_653_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5(lean_object* v_msg_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_panic_fn_borrowed(v___x_659_, v_msg_658_);
return v___x_660_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_664_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__2));
v___x_665_ = lean_unsigned_to_nat(11u);
v___x_666_ = lean_unsigned_to_nat(163u);
v___x_667_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__1));
v___x_668_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__0));
v___x_669_ = l_mkPanicMessageWithDecl(v___x_668_, v___x_667_, v___x_666_, v___x_665_, v___x_664_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(lean_object* v_a_670_, lean_object* v_x_671_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3);
v___x_673_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5(v___x_672_);
return v___x_673_;
}
else
{
lean_object* v_key_674_; lean_object* v_value_675_; lean_object* v_tail_676_; uint8_t v___x_677_; 
v_key_674_ = lean_ctor_get(v_x_671_, 0);
v_value_675_ = lean_ctor_get(v_x_671_, 1);
v_tail_676_ = lean_ctor_get(v_x_671_, 2);
v___x_677_ = lean_expr_eqv(v_key_674_, v_a_670_);
if (v___x_677_ == 0)
{
v_x_671_ = v_tail_676_;
goto _start;
}
else
{
lean_inc(v_value_675_);
return v_value_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___boxed(lean_object* v_a_679_, lean_object* v_x_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(v_a_679_, v_x_680_);
lean_dec(v_x_680_);
lean_dec_ref(v_a_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(lean_object* v_m_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_buckets_684_; lean_object* v___x_685_; uint64_t v___x_686_; uint64_t v___x_687_; uint64_t v___x_688_; uint64_t v_fold_689_; uint64_t v___x_690_; uint64_t v___x_691_; uint64_t v___x_692_; size_t v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_buckets_684_ = lean_ctor_get(v_m_682_, 1);
v___x_685_ = lean_array_get_size(v_buckets_684_);
v___x_686_ = l_Lean_Expr_hash(v_a_683_);
v___x_687_ = 32ULL;
v___x_688_ = lean_uint64_shift_right(v___x_686_, v___x_687_);
v_fold_689_ = lean_uint64_xor(v___x_686_, v___x_688_);
v___x_690_ = 16ULL;
v___x_691_ = lean_uint64_shift_right(v_fold_689_, v___x_690_);
v___x_692_ = lean_uint64_xor(v_fold_689_, v___x_691_);
v___x_693_ = lean_uint64_to_usize(v___x_692_);
v___x_694_ = lean_usize_of_nat(v___x_685_);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_sub(v___x_694_, v___x_695_);
v___x_697_ = lean_usize_land(v___x_693_, v___x_696_);
v___x_698_ = lean_array_uget_borrowed(v_buckets_684_, v___x_697_);
v___x_699_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(v_a_683_, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___boxed(lean_object* v_m_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(v_m_700_, v_a_701_);
lean_dec_ref(v_a_701_);
lean_dec_ref(v_m_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0(lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(v___y_703_, v___y_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0___boxed(lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Meta_AC_toACExpr___lam__0(v___y_706_, v___y_707_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_AC_toACExpr_spec__4(lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 0)
{
return v_x_709_;
}
else
{
lean_object* v_key_711_; lean_object* v_tail_712_; lean_object* v___x_713_; 
v_key_711_ = lean_ctor_get(v_x_710_, 0);
lean_inc(v_key_711_);
v_tail_712_ = lean_ctor_get(v_x_710_, 2);
lean_inc(v_tail_712_);
lean_dec_ref_known(v_x_710_, 3);
v___x_713_ = lean_array_push(v_x_709_, v_key_711_);
v_x_709_ = v___x_713_;
v_x_710_ = v_tail_712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(lean_object* v_as_715_, size_t v_i_716_, size_t v_stop_717_, lean_object* v_b_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_eq(v_i_716_, v_stop_717_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; size_t v___x_722_; size_t v___x_723_; 
v___x_720_ = lean_array_uget_borrowed(v_as_715_, v_i_716_);
lean_inc(v___x_720_);
v___x_721_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_AC_toACExpr_spec__4(v_b_718_, v___x_720_);
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_716_, v___x_722_);
v_i_716_ = v___x_723_;
v_b_718_ = v___x_721_;
goto _start;
}
else
{
return v_b_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5___boxed(lean_object* v_as_725_, lean_object* v_i_726_, lean_object* v_stop_727_, lean_object* v_b_728_){
_start:
{
size_t v_i_boxed_729_; size_t v_stop_boxed_730_; lean_object* v_res_731_; 
v_i_boxed_729_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_stop_boxed_730_ = lean_unbox_usize(v_stop_727_);
lean_dec(v_stop_727_);
v_res_731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_as_725_, v_i_boxed_729_, v_stop_boxed_730_, v_b_728_);
lean_dec_ref(v_as_725_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(lean_object* v_xs_732_, lean_object* v_j_733_){
_start:
{
lean_object* v_zero_734_; uint8_t v_isZero_735_; 
v_zero_734_ = lean_unsigned_to_nat(0u);
v_isZero_735_ = lean_nat_dec_eq(v_j_733_, v_zero_734_);
if (v_isZero_735_ == 1)
{
lean_dec(v_j_733_);
return v_xs_732_;
}
else
{
lean_object* v_one_736_; lean_object* v_n_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_one_736_ = lean_unsigned_to_nat(1u);
v_n_737_ = lean_nat_sub(v_j_733_, v_one_736_);
v___x_738_ = lean_array_fget_borrowed(v_xs_732_, v_j_733_);
v___x_739_ = lean_array_fget_borrowed(v_xs_732_, v_n_737_);
v___x_740_ = lean_expr_lt(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec(v_n_737_);
lean_dec(v_j_733_);
return v_xs_732_;
}
else
{
lean_object* v___x_741_; 
v___x_741_ = lean_array_fswap(v_xs_732_, v_j_733_, v_n_737_);
lean_dec(v_j_733_);
v_xs_732_ = v___x_741_;
v_j_733_ = v_n_737_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1(lean_object* v_xs_743_, lean_object* v_i_744_, lean_object* v_fuel_745_){
_start:
{
lean_object* v_zero_746_; uint8_t v_isZero_747_; 
v_zero_746_ = lean_unsigned_to_nat(0u);
v_isZero_747_ = lean_nat_dec_eq(v_fuel_745_, v_zero_746_);
if (v_isZero_747_ == 1)
{
lean_dec(v_fuel_745_);
lean_dec(v_i_744_);
return v_xs_743_;
}
else
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_array_get_size(v_xs_743_);
v___x_749_ = lean_nat_dec_lt(v_i_744_, v___x_748_);
if (v___x_749_ == 0)
{
lean_dec(v_fuel_745_);
lean_dec(v_i_744_);
return v_xs_743_;
}
else
{
lean_object* v_one_750_; lean_object* v_n_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_one_750_ = lean_unsigned_to_nat(1u);
v_n_751_ = lean_nat_sub(v_fuel_745_, v_one_750_);
lean_dec(v_fuel_745_);
lean_inc(v_i_744_);
v___x_752_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(v_xs_743_, v_i_744_);
v___x_753_ = lean_nat_add(v_i_744_, v_one_750_);
lean_dec(v_i_744_);
v_xs_743_ = v___x_752_;
v_i_744_ = v___x_753_;
v_fuel_745_ = v_n_751_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(lean_object* v_a_755_, lean_object* v_b_756_, lean_object* v_x_757_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
lean_dec(v_b_756_);
lean_dec_ref(v_a_755_);
return v_x_757_;
}
else
{
lean_object* v_key_758_; lean_object* v_value_759_; lean_object* v_tail_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_772_; 
v_key_758_ = lean_ctor_get(v_x_757_, 0);
v_value_759_ = lean_ctor_get(v_x_757_, 1);
v_tail_760_ = lean_ctor_get(v_x_757_, 2);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_772_ == 0)
{
v___x_762_ = v_x_757_;
v_isShared_763_ = v_isSharedCheck_772_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_tail_760_);
lean_inc(v_value_759_);
lean_inc(v_key_758_);
lean_dec(v_x_757_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_772_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; 
v___x_764_ = lean_expr_eqv(v_key_758_, v_a_755_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_755_, v_b_756_, v_tail_760_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 2, v___x_765_);
v___x_767_ = v___x_762_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_key_758_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_value_759_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
lean_object* v___x_770_; 
lean_dec(v_value_759_);
lean_dec(v_key_758_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v_b_756_);
lean_ctor_set(v___x_762_, 0, v_a_755_);
v___x_770_ = v___x_762_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_755_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_b_756_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_tail_760_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(lean_object* v_m_773_, lean_object* v_a_774_, lean_object* v_b_775_){
_start:
{
lean_object* v_size_776_; lean_object* v_buckets_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_820_; 
v_size_776_ = lean_ctor_get(v_m_773_, 0);
v_buckets_777_ = lean_ctor_get(v_m_773_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_m_773_);
if (v_isSharedCheck_820_ == 0)
{
v___x_779_ = v_m_773_;
v_isShared_780_ = v_isSharedCheck_820_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_buckets_777_);
lean_inc(v_size_776_);
lean_dec(v_m_773_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_820_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; uint64_t v___x_784_; uint64_t v_fold_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v_bkt_794_; uint8_t v___x_795_; 
v___x_781_ = lean_array_get_size(v_buckets_777_);
v___x_782_ = l_Lean_Expr_hash(v_a_774_);
v___x_783_ = 32ULL;
v___x_784_ = lean_uint64_shift_right(v___x_782_, v___x_783_);
v_fold_785_ = lean_uint64_xor(v___x_782_, v___x_784_);
v___x_786_ = 16ULL;
v___x_787_ = lean_uint64_shift_right(v_fold_785_, v___x_786_);
v___x_788_ = lean_uint64_xor(v_fold_785_, v___x_787_);
v___x_789_ = lean_uint64_to_usize(v___x_788_);
v___x_790_ = lean_usize_of_nat(v___x_781_);
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_sub(v___x_790_, v___x_791_);
v___x_793_ = lean_usize_land(v___x_789_, v___x_792_);
v_bkt_794_ = lean_array_uget_borrowed(v_buckets_777_, v___x_793_);
v___x_795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_774_, v_bkt_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v_size_x27_797_; lean_object* v___x_798_; lean_object* v_buckets_x27_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v_size_x27_797_ = lean_nat_add(v_size_776_, v___x_796_);
lean_dec(v_size_776_);
lean_inc(v_bkt_794_);
v___x_798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_798_, 0, v_a_774_);
lean_ctor_set(v___x_798_, 1, v_b_775_);
lean_ctor_set(v___x_798_, 2, v_bkt_794_);
v_buckets_x27_799_ = lean_array_uset(v_buckets_777_, v___x_793_, v___x_798_);
v___x_800_ = lean_unsigned_to_nat(4u);
v___x_801_ = lean_nat_mul(v_size_x27_797_, v___x_800_);
v___x_802_ = lean_unsigned_to_nat(3u);
v___x_803_ = lean_nat_div(v___x_801_, v___x_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_array_get_size(v_buckets_x27_799_);
v___x_805_ = lean_nat_dec_le(v___x_803_, v___x_804_);
lean_dec(v___x_803_);
if (v___x_805_ == 0)
{
lean_object* v_val_806_; lean_object* v___x_808_; 
v_val_806_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_buckets_x27_799_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_val_806_);
lean_ctor_set(v___x_779_, 0, v_size_x27_797_);
v___x_808_ = v___x_779_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_size_x27_797_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_val_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v___x_811_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_buckets_x27_799_);
lean_ctor_set(v___x_779_, 0, v_size_x27_797_);
v___x_811_ = v___x_779_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_size_x27_797_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_buckets_x27_799_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v___x_813_; lean_object* v_buckets_x27_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
lean_inc(v_bkt_794_);
v___x_813_ = lean_box(0);
v_buckets_x27_814_ = lean_array_uset(v_buckets_777_, v___x_793_, v___x_813_);
v___x_815_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_774_, v_b_775_, v_bkt_794_);
v___x_816_ = lean_array_uset(v_buckets_x27_814_, v___x_793_, v___x_815_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_816_);
v___x_818_ = v___x_779_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_size_776_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(lean_object* v_as_821_, size_t v_i_822_, size_t v_stop_823_, lean_object* v_b_824_){
_start:
{
uint8_t v___x_825_; 
v___x_825_ = lean_usize_dec_eq(v_i_822_, v_stop_823_);
if (v___x_825_ == 0)
{
lean_object* v_size_826_; lean_object* v___x_827_; lean_object* v___x_828_; size_t v___x_829_; size_t v___x_830_; 
v_size_826_ = lean_ctor_get(v_b_824_, 0);
lean_inc(v_size_826_);
v___x_827_ = lean_array_uget_borrowed(v_as_821_, v_i_822_);
lean_inc(v___x_827_);
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(v_b_824_, v___x_827_, v_size_826_);
v___x_829_ = ((size_t)1ULL);
v___x_830_ = lean_usize_add(v_i_822_, v___x_829_);
v_i_822_ = v___x_830_;
v_b_824_ = v___x_828_;
goto _start;
}
else
{
return v_b_824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3___boxed(lean_object* v_as_832_, lean_object* v_i_833_, lean_object* v_stop_834_, lean_object* v_b_835_){
_start:
{
size_t v_i_boxed_836_; size_t v_stop_boxed_837_; lean_object* v_res_838_; 
v_i_boxed_836_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_stop_boxed_837_ = lean_unbox_usize(v_stop_834_);
lean_dec(v_stop_834_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v_as_832_, v_i_boxed_836_, v_stop_boxed_837_, v_b_835_);
lean_dec_ref(v_as_832_);
return v_res_838_;
}
}
static lean_object* _init_l_Lean_Meta_AC_toACExpr___closed__0(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_box(0);
v___x_840_ = lean_unsigned_to_nat(16u);
v___x_841_ = lean_mk_array(v___x_840_, v___x_839_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_Meta_AC_toACExpr___closed__1(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = lean_obj_once(&l_Lean_Meta_AC_toACExpr___closed__0, &l_Lean_Meta_AC_toACExpr___closed__0_once, _init_l_Lean_Meta_AC_toACExpr___closed__0);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v___x_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr(lean_object* v_op_845_, lean_object* v_l_846_, lean_object* v_r_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
lean_inc_ref(v_op_845_);
v___x_853_ = l_Lean_mkAppB(v_op_845_, v_l_846_, v_r_847_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_obj_once(&l_Lean_Meta_AC_toACExpr___closed__1, &l_Lean_Meta_AC_toACExpr___closed__1_once, _init_l_Lean_Meta_AC_toACExpr___closed__1);
v___x_856_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_845_, v___x_853_, v___x_855_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_899_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_899_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_899_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_899_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_fst_861_; lean_object* v_snd_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_898_; 
v_fst_861_ = lean_ctor_get(v_a_857_, 0);
v_snd_862_ = lean_ctor_get(v_a_857_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_857_);
if (v_isSharedCheck_898_ == 0)
{
v___x_864_ = v_a_857_;
v_isShared_865_ = v_isSharedCheck_898_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_snd_862_);
lean_inc(v_fst_861_);
lean_dec(v_a_857_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_898_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_878_; lean_object* v_size_890_; lean_object* v_buckets_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_size_890_ = lean_ctor_get(v_snd_862_, 0);
lean_inc(v_size_890_);
v_buckets_891_ = lean_ctor_get(v_snd_862_, 1);
lean_inc_ref(v_buckets_891_);
lean_dec(v_snd_862_);
v___x_892_ = lean_mk_empty_array_with_capacity(v_size_890_);
lean_dec(v_size_890_);
v___x_893_ = lean_array_get_size(v_buckets_891_);
v___x_894_ = lean_nat_dec_lt(v___x_854_, v___x_893_);
if (v___x_894_ == 0)
{
lean_dec_ref(v_buckets_891_);
v___y_878_ = v___x_892_;
goto v___jp_877_;
}
else
{
size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
v___x_895_ = ((size_t)0ULL);
v___x_896_ = lean_usize_of_nat(v___x_893_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_buckets_891_, v___x_895_, v___x_896_, v___x_892_);
lean_dec_ref(v_buckets_891_);
v___y_878_ = v___x_897_;
goto v___jp_877_;
}
v___jp_866_:
{
lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_toACExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_869_, 0, v___y_868_);
v___x_870_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(v___f_869_, v_fst_861_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_870_);
lean_ctor_set(v___x_864_, 0, v___y_867_);
v___x_872_ = v___x_864_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___y_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_872_);
v___x_874_ = v___x_859_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
v___jp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_879_ = lean_array_get_size(v___y_878_);
v___x_880_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1(v___y_878_, v___x_854_, v___x_879_);
v___x_881_ = lean_array_get_size(v___x_880_);
v___x_882_ = lean_nat_dec_lt(v___x_854_, v___x_881_);
if (v___x_882_ == 0)
{
v___y_867_ = v___x_880_;
v___y_868_ = v___x_855_;
goto v___jp_866_;
}
else
{
uint8_t v___x_883_; 
v___x_883_ = lean_nat_dec_le(v___x_881_, v___x_881_);
if (v___x_883_ == 0)
{
if (v___x_882_ == 0)
{
v___y_867_ = v___x_880_;
v___y_868_ = v___x_855_;
goto v___jp_866_;
}
else
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((size_t)0ULL);
v___x_885_ = lean_usize_of_nat(v___x_881_);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v___x_880_, v___x_884_, v___x_885_, v___x_855_);
v___y_867_ = v___x_880_;
v___y_868_ = v___x_886_;
goto v___jp_866_;
}
}
else
{
size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = ((size_t)0ULL);
v___x_888_ = lean_usize_of_nat(v___x_881_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v___x_880_, v___x_887_, v___x_888_, v___x_855_);
v___y_867_ = v___x_880_;
v___y_868_ = v___x_889_;
goto v___jp_866_;
}
}
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_a_900_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_856_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_856_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___boxed(lean_object* v_op_908_, lean_object* v_l_909_, lean_object* v_r_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Meta_AC_toACExpr(v_op_908_, v_l_909_, v_r_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0(lean_object* v_00_u03b2_917_, lean_object* v_m_918_, lean_object* v_a_919_, lean_object* v_b_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(v_m_918_, v_a_919_, v_b_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0(lean_object* v_00_u03b2_922_, lean_object* v_a_923_, lean_object* v_b_924_, lean_object* v_x_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_923_, v_b_924_, v_x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2(lean_object* v_xs_927_, lean_object* v_j_928_, lean_object* v_h_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(v_xs_927_, v_j_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(lean_object* v_k_931_, lean_object* v_b_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; 
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
v___x_938_ = lean_apply_6(v_k_931_, v_b_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, lean_box(0));
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(v_k_939_, v_b_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(lean_object* v_name_947_, uint8_t v_bi_948_, lean_object* v_type_949_, lean_object* v_k_950_, uint8_t v_kind_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___f_957_; lean_object* v___x_958_; 
v___f_957_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_957_, 0, v_k_950_);
v___x_958_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_947_, v_bi_948_, v_type_949_, v___f_957_, v_kind_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_958_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_958_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___boxed(lean_object* v_name_975_, lean_object* v_bi_976_, lean_object* v_type_977_, lean_object* v_k_978_, lean_object* v_kind_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
uint8_t v_bi_boxed_985_; uint8_t v_kind_boxed_986_; lean_object* v_res_987_; 
v_bi_boxed_985_ = lean_unbox(v_bi_976_);
v_kind_boxed_986_ = lean_unbox(v_kind_979_);
v_res_987_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_975_, v_bi_boxed_985_, v_type_977_, v_k_978_, v_kind_boxed_986_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(lean_object* v_name_988_, lean_object* v_type_989_, lean_object* v_k_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = 0;
v___x_997_ = 0;
v___x_998_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_988_, v___x_996_, v_type_989_, v_k_990_, v___x_997_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg___boxed(lean_object* v_name_999_, lean_object* v_type_1000_, lean_object* v_k_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v_name_999_, v_type_1000_, v_k_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0___boxed(lean_object** _args){
lean_object* v_i_1012_ = _args[0];
lean_object* v_v_1013_ = _args[1];
lean_object* v_acc_1014_ = _args[2];
lean_object* v___x_1015_ = _args[3];
lean_object* v_vars_1016_ = _args[4];
lean_object* v___x_1017_ = _args[5];
lean_object* v_val_1018_ = _args[6];
lean_object* v_args_1019_ = _args[7];
lean_object* v_preContext_1020_ = _args[8];
lean_object* v_atoms_1021_ = _args[9];
lean_object* v_k_1022_ = _args[10];
lean_object* v_00_u03b1_1023_ = _args[11];
lean_object* v_u_1024_ = _args[12];
lean_object* v_iv_1025_ = _args[13];
lean_object* v___y_1026_ = _args[14];
lean_object* v___y_1027_ = _args[15];
lean_object* v___y_1028_ = _args[16];
lean_object* v___y_1029_ = _args[17];
lean_object* v___y_1030_ = _args[18];
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(v_i_1012_, v_v_1013_, v_acc_1014_, v___x_1015_, v_vars_1016_, v___x_1017_, v_val_1018_, v_args_1019_, v_preContext_1020_, v_atoms_1021_, v_k_1022_, v_00_u03b1_1023_, v_u_1024_, v_iv_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v_i_1012_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(lean_object* v_preContext_1035_, lean_object* v_atoms_1036_, lean_object* v_i_1037_, lean_object* v_acc_1038_, lean_object* v_vars_1039_, lean_object* v_args_1040_, lean_object* v_k_1041_, lean_object* v_00_u03b1_1042_, lean_object* v_u_1043_, lean_object* v_v_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_op_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_op_1050_ = lean_ctor_get(v_preContext_1035_, 1);
v___x_1051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1));
v___x_1052_ = lean_array_fget_borrowed(v_atoms_1036_, v_i_1037_);
v___x_1053_ = lean_unsigned_to_nat(2u);
v___x_1054_ = lean_mk_empty_array_with_capacity(v___x_1053_);
lean_inc_ref(v_op_1050_);
lean_inc_ref(v___x_1054_);
v___x_1055_ = lean_array_push(v___x_1054_, v_op_1050_);
lean_inc(v___x_1052_);
v___x_1056_ = lean_array_push(v___x_1055_, v___x_1052_);
v___x_1057_ = l_Lean_Meta_AC_getInstance(v___x_1051_, v___x_1056_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
if (lean_obj_tag(v_a_1058_) == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec_ref(v___x_1054_);
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_i_1037_, v___x_1059_);
lean_dec(v_i_1037_);
lean_inc_ref(v_v_1044_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_v_1044_);
lean_ctor_set(v___x_1061_, 1, v_a_1058_);
v___x_1062_ = lean_array_push(v_acc_1038_, v___x_1061_);
v___x_1063_ = lean_array_push(v_vars_1039_, v_v_1044_);
lean_inc(v___x_1052_);
v___x_1064_ = lean_array_push(v_args_1040_, v___x_1052_);
v___x_1065_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1035_, v_atoms_1036_, v_k_1041_, v_00_u03b1_1042_, v_u_1043_, v___x_1060_, v___x_1062_, v___x_1063_, v___x_1064_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1065_;
}
else
{
lean_object* v_val_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_inc(v___x_1052_);
lean_inc_ref(v_op_1050_);
v_val_1066_ = lean_ctor_get(v_a_1058_, 0);
lean_inc(v_val_1066_);
lean_dec_ref_known(v_a_1058_, 1);
lean_inc(v_u_1043_);
lean_inc_ref(v_00_u03b1_1042_);
lean_inc_ref(v_v_1044_);
v___f_1067_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0___boxed), 19, 13);
lean_closure_set(v___f_1067_, 0, v_i_1037_);
lean_closure_set(v___f_1067_, 1, v_v_1044_);
lean_closure_set(v___f_1067_, 2, v_acc_1038_);
lean_closure_set(v___f_1067_, 3, v___x_1054_);
lean_closure_set(v___f_1067_, 4, v_vars_1039_);
lean_closure_set(v___f_1067_, 5, v___x_1052_);
lean_closure_set(v___f_1067_, 6, v_val_1066_);
lean_closure_set(v___f_1067_, 7, v_args_1040_);
lean_closure_set(v___f_1067_, 8, v_preContext_1035_);
lean_closure_set(v___f_1067_, 9, v_atoms_1036_);
lean_closure_set(v___f_1067_, 10, v_k_1041_);
lean_closure_set(v___f_1067_, 11, v_00_u03b1_1042_);
lean_closure_set(v___f_1067_, 12, v_u_1043_);
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3));
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_u_1043_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_mkConst(v___x_1051_, v___x_1070_);
v___x_1072_ = l_Lean_mkApp3(v___x_1071_, v_00_u03b1_1042_, v_op_1050_, v_v_1044_);
v___x_1073_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v___x_1068_, v___x_1072_, v___f_1067_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1073_;
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v___x_1054_);
lean_dec_ref(v_v_1044_);
lean_dec(v_u_1043_);
lean_dec_ref(v_00_u03b1_1042_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_args_1040_);
lean_dec_ref(v_vars_1039_);
lean_dec_ref(v_acc_1038_);
lean_dec(v_i_1037_);
lean_dec_ref(v_atoms_1036_);
lean_dec_ref(v_preContext_1035_);
v_a_1074_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1057_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1057_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___boxed(lean_object* v_preContext_1082_, lean_object* v_atoms_1083_, lean_object* v_i_1084_, lean_object* v_acc_1085_, lean_object* v_vars_1086_, lean_object* v_args_1087_, lean_object* v_k_1088_, lean_object* v_00_u03b1_1089_, lean_object* v_u_1090_, lean_object* v_v_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(v_preContext_1082_, v_atoms_1083_, v_i_1084_, v_acc_1085_, v_vars_1086_, v_args_1087_, v_k_1088_, v_00_u03b1_1089_, v_u_1090_, v_v_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(lean_object* v_preContext_1101_, lean_object* v_atoms_1102_, lean_object* v_k_1103_, lean_object* v_00_u03b1_1104_, lean_object* v_u_1105_, lean_object* v_i_1106_, lean_object* v_acc_1107_, lean_object* v_vars_1108_, lean_object* v_args_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_array_get_size(v_atoms_1102_);
v___x_1116_ = lean_nat_dec_lt(v_i_1106_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec(v_i_1106_);
lean_dec(v_u_1105_);
lean_dec_ref(v_00_u03b1_1104_);
lean_dec_ref(v_atoms_1102_);
lean_dec_ref(v_preContext_1101_);
lean_inc(v_a_1113_);
lean_inc_ref(v_a_1112_);
lean_inc(v_a_1111_);
lean_inc_ref(v_a_1110_);
v___x_1117_ = lean_apply_6(v_k_1103_, v_acc_1107_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, lean_box(0));
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; uint8_t v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = 1;
v___x_1120_ = 1;
v___x_1121_ = l_Lean_Meta_mkLambdaFVars(v_vars_1108_, v_a_1118_, v___x_1116_, v___x_1119_, v___x_1116_, v___x_1119_, v___x_1120_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec_ref(v_vars_1108_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1130_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1130_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1130_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1126_ = l_Lean_mkAppN(v_a_1122_, v_args_1109_);
lean_dec_ref(v_args_1109_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1126_);
v___x_1128_ = v___x_1124_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_dec_ref(v_args_1109_);
return v___x_1121_;
}
}
else
{
lean_dec_ref(v_args_1109_);
lean_dec_ref(v_vars_1108_);
return v___x_1117_;
}
}
else
{
lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_inc_ref(v_00_u03b1_1104_);
v___f_1131_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___boxed), 15, 9);
lean_closure_set(v___f_1131_, 0, v_preContext_1101_);
lean_closure_set(v___f_1131_, 1, v_atoms_1102_);
lean_closure_set(v___f_1131_, 2, v_i_1106_);
lean_closure_set(v___f_1131_, 3, v_acc_1107_);
lean_closure_set(v___f_1131_, 4, v_vars_1108_);
lean_closure_set(v___f_1131_, 5, v_args_1109_);
lean_closure_set(v___f_1131_, 6, v_k_1103_);
lean_closure_set(v___f_1131_, 7, v_00_u03b1_1104_);
lean_closure_set(v___f_1131_, 8, v_u_1105_);
v___x_1132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1));
v___x_1133_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v___x_1132_, v_00_u03b1_1104_, v___f_1131_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(lean_object* v_i_1134_, lean_object* v_v_1135_, lean_object* v_acc_1136_, lean_object* v___x_1137_, lean_object* v_vars_1138_, lean_object* v___x_1139_, lean_object* v_val_1140_, lean_object* v_args_1141_, lean_object* v_preContext_1142_, lean_object* v_atoms_1143_, lean_object* v_k_1144_, lean_object* v_00_u03b1_1145_, lean_object* v_u_1146_, lean_object* v_iv_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_i_1134_, v___x_1153_);
lean_inc_ref(v_iv_1147_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_iv_1147_);
lean_inc_ref(v_v_1135_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v_v_1135_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_array_push(v_acc_1136_, v___x_1156_);
lean_inc_ref(v___x_1137_);
v___x_1158_ = lean_array_push(v___x_1137_, v_v_1135_);
v___x_1159_ = lean_array_push(v___x_1158_, v_iv_1147_);
v___x_1160_ = l_Array_append___redArg(v_vars_1138_, v___x_1159_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = lean_array_push(v___x_1137_, v___x_1139_);
v___x_1162_ = lean_array_push(v___x_1161_, v_val_1140_);
v___x_1163_ = l_Array_append___redArg(v_args_1141_, v___x_1162_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1142_, v_atoms_1143_, v_k_1144_, v_00_u03b1_1145_, v_u_1146_, v___x_1154_, v___x_1157_, v___x_1160_, v___x_1163_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___boxed(lean_object* v_preContext_1165_, lean_object* v_atoms_1166_, lean_object* v_k_1167_, lean_object* v_00_u03b1_1168_, lean_object* v_u_1169_, lean_object* v_i_1170_, lean_object* v_acc_1171_, lean_object* v_vars_1172_, lean_object* v_args_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1165_, v_atoms_1166_, v_k_1167_, v_00_u03b1_1168_, v_u_1169_, v_i_1170_, v_acc_1171_, v_vars_1172_, v_args_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(lean_object* v_00_u03b1_1180_, lean_object* v_name_1181_, uint8_t v_bi_1182_, lean_object* v_type_1183_, lean_object* v_k_1184_, uint8_t v_kind_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_1181_, v_bi_1182_, v_type_1183_, v_k_1184_, v_kind_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_name_1193_, lean_object* v_bi_1194_, lean_object* v_type_1195_, lean_object* v_k_1196_, lean_object* v_kind_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
uint8_t v_bi_boxed_1203_; uint8_t v_kind_boxed_1204_; lean_object* v_res_1205_; 
v_bi_boxed_1203_ = lean_unbox(v_bi_1194_);
v_kind_boxed_1204_ = lean_unbox(v_kind_1197_);
v_res_1205_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(v_00_u03b1_1192_, v_name_1193_, v_bi_boxed_1203_, v_type_1195_, v_k_1196_, v_kind_boxed_1204_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(lean_object* v_00_u03b1_1206_, lean_object* v_name_1207_, lean_object* v_type_1208_, lean_object* v_k_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v_name_1207_, v_type_1208_, v_k_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_name_1217_, lean_object* v_type_1218_, lean_object* v_k_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(v_00_u03b1_1216_, v_name_1217_, v_type_1218_, v_k_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter___redArg(lean_object* v_____do__lift_1226_, lean_object* v_h__1_1227_, lean_object* v_h__2_1228_){
_start:
{
if (lean_obj_tag(v_____do__lift_1226_) == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec(v_h__2_1228_);
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_apply_1(v_h__1_1227_, v___x_1229_);
return v___x_1230_;
}
else
{
lean_object* v_val_1231_; lean_object* v___x_1232_; 
lean_dec(v_h__1_1227_);
v_val_1231_ = lean_ctor_get(v_____do__lift_1226_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v_____do__lift_1226_, 1);
v___x_1232_ = lean_apply_1(v_h__2_1228_, v_val_1231_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter(lean_object* v_motive_1233_, lean_object* v_____do__lift_1234_, lean_object* v_h__1_1235_, lean_object* v_h__2_1236_){
_start:
{
if (lean_obj_tag(v_____do__lift_1234_) == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_h__2_1236_);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_apply_1(v_h__1_1235_, v___x_1237_);
return v___x_1238_;
}
else
{
lean_object* v_val_1239_; lean_object* v___x_1240_; 
lean_dec(v_h__1_1235_);
v_val_1239_ = lean_ctor_get(v_____do__lift_1234_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v_____do__lift_1234_, 1);
v___x_1240_ = lean_apply_1(v_h__2_1236_, v_val_1239_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_abstractAtoms(lean_object* v_preContext_1243_, lean_object* v_atoms_1244_, lean_object* v_k_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1251_ = l_Lean_instInhabitedExpr;
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_array_get_borrowed(v___x_1251_, v_atoms_1244_, v___x_1252_);
lean_inc(v_a_1249_);
lean_inc_ref(v_a_1248_);
lean_inc(v_a_1247_);
lean_inc_ref(v_a_1246_);
lean_inc(v___x_1253_);
v___x_1254_ = lean_infer_type(v___x_1253_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc_n(v_a_1255_, 2);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = l_Lean_Meta_getLevel(v_a_1255_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = ((lean_object*)(l_Lean_Meta_AC_abstractAtoms___closed__0));
v___x_1259_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1243_, v_atoms_1244_, v_k_1245_, v_a_1255_, v_a_1257_, v___x_1252_, v___x_1258_, v___x_1258_, v___x_1258_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1259_;
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_a_1255_);
lean_dec_ref(v_k_1245_);
lean_dec_ref(v_atoms_1244_);
lean_dec_ref(v_preContext_1243_);
v_a_1260_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1256_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1256_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_dec_ref(v_k_1245_);
lean_dec_ref(v_atoms_1244_);
lean_dec_ref(v_preContext_1243_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_abstractAtoms___boxed(lean_object* v_preContext_1268_, lean_object* v_atoms_1269_, lean_object* v_k_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Meta_AC_abstractAtoms(v_preContext_1268_, v_atoms_1269_, v_k_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(lean_object* v___x_1282_, lean_object* v___x_1283_, lean_object* v_tp_1284_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2));
v___x_1286_ = l_Lean_mkConst(v___x_1285_, v___x_1282_);
v___x_1287_ = l_Lean_Expr_app___override(v___x_1283_, v_tp_1284_);
v___x_1288_ = l_Lean_Expr_app___override(v___x_1286_, v___x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v_tp_1296_, lean_object* v_v_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1));
v___x_1299_ = l_Lean_mkConst(v___x_1298_, v___x_1293_);
lean_inc_ref(v_tp_1296_);
v___x_1300_ = l_Lean_Expr_app___override(v___x_1294_, v_tp_1296_);
v___x_1301_ = l_Lean_mkAppB(v___x_1295_, v_tp_1296_, v_v_1297_);
v___x_1302_ = l_Lean_mkAppB(v___x_1299_, v___x_1300_, v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2));
v___x_1311_ = l_Lean_mkConst(v___x_1310_, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2));
v___x_1324_ = l_Lean_mkConst(v___x_1323_, v___x_1322_);
return v___x_1324_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11));
v___x_1331_ = l_Lean_mkConst(v___x_1330_, v___x_1329_);
return v___x_1331_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1));
v___x_1334_ = l_Lean_mkConst(v___x_1333_, v___x_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(lean_object* v_u_1335_, lean_object* v_preContext_1336_, lean_object* v_00_u03b1_1337_, size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_bs_1340_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
lean_dec_ref(v_00_u03b1_1337_);
lean_dec_ref(v_preContext_1336_);
lean_dec(v_u_1335_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_bs_1340_);
return v___x_1343_;
}
else
{
lean_object* v_v_1344_; lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1379_; 
v_v_1344_ = lean_array_uget(v_bs_1340_, v_i_1339_);
v_fst_1345_ = lean_ctor_get(v_v_1344_, 0);
v_snd_1346_ = lean_ctor_get(v_v_1344_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_v_1344_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1348_ = v_v_1344_;
v_isShared_1349_ = v_isSharedCheck_1379_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snd_1346_);
lean_inc(v_fst_1345_);
lean_dec(v_v_1344_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1379_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_op_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v_bs_x27_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v_op_1350_ = lean_ctor_get(v_preContext_1336_, 1);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
v___x_1353_ = lean_unsigned_to_nat(0u);
v_bs_x27_1354_ = lean_array_uset(v_bs_1340_, v_i_1339_, v___x_1353_);
v___x_1355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1));
lean_inc(v_u_1335_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 1);
lean_ctor_set(v___x_1348_, 1, v___x_1351_);
lean_ctor_set(v___x_1348_, 0, v_u_1335_);
v___x_1357_ = v___x_1348_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_u_1335_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1351_);
v___x_1357_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___y_1359_; lean_object* v___x_1367_; lean_object* v_isNeutralClass_1368_; 
lean_inc_ref(v___x_1357_);
v___x_1367_ = l_Lean_mkConst(v___x_1355_, v___x_1357_);
lean_inc(v_fst_1345_);
lean_inc_ref(v_op_1350_);
lean_inc_ref(v_00_u03b1_1337_);
v_isNeutralClass_1368_ = l_Lean_mkApp3(v___x_1367_, v_00_u03b1_1337_, v_op_1350_, v_fst_1345_);
if (lean_obj_tag(v_snd_1346_) == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9);
v___x_1370_ = l_Lean_Expr_app___override(v___x_1352_, v_isNeutralClass_1368_);
v___x_1371_ = l_Lean_Expr_app___override(v___x_1369_, v___x_1370_);
v___y_1359_ = v___x_1371_;
goto v___jp_1358_;
}
else
{
lean_object* v_val_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_val_1372_ = lean_ctor_get(v_snd_1346_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v_snd_1346_, 1);
v___x_1373_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
v___x_1374_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13);
lean_inc_ref(v_isNeutralClass_1368_);
v___x_1375_ = l_Lean_Expr_app___override(v___x_1352_, v_isNeutralClass_1368_);
v___x_1376_ = l_Lean_mkAppB(v___x_1373_, v_isNeutralClass_1368_, v_val_1372_);
v___x_1377_ = l_Lean_mkAppB(v___x_1374_, v___x_1375_, v___x_1376_);
v___y_1359_ = v___x_1377_;
goto v___jp_1358_;
}
v___jp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v___x_1360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8));
v___x_1361_ = l_Lean_mkConst(v___x_1360_, v___x_1357_);
lean_inc_ref(v_op_1350_);
lean_inc_ref(v_00_u03b1_1337_);
v___x_1362_ = l_Lean_mkApp4(v___x_1361_, v_00_u03b1_1337_, v_op_1350_, v_fst_1345_, v___y_1359_);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1339_, v___x_1363_);
v___x_1365_ = lean_array_uset(v_bs_x27_1354_, v_i_1339_, v___x_1362_);
v_i_1339_ = v___x_1364_;
v_bs_1340_ = v___x_1365_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___boxed(lean_object* v_u_1380_, lean_object* v_preContext_1381_, lean_object* v_00_u03b1_1382_, lean_object* v_sz_1383_, lean_object* v_i_1384_, lean_object* v_bs_1385_, lean_object* v___y_1386_){
_start:
{
size_t v_sz_boxed_1387_; size_t v_i_boxed_1388_; lean_object* v_res_1389_; 
v_sz_boxed_1387_ = lean_unbox_usize(v_sz_1383_);
lean_dec(v_sz_1383_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1380_, v_preContext_1381_, v_00_u03b1_1382_, v_sz_boxed_1387_, v_i_boxed_1388_, v_bs_1385_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(lean_object* v_u_1390_, lean_object* v_preContext_1391_, lean_object* v_00_u03b1_1392_, size_t v_sz_1393_, size_t v_i_1394_, lean_object* v_bs_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_usize_dec_lt(v_i_1394_, v_sz_1393_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
lean_dec_ref(v_00_u03b1_1392_);
lean_dec_ref(v_preContext_1391_);
lean_dec(v_u_1390_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_bs_1395_);
return v___x_1402_;
}
else
{
lean_object* v_v_1403_; lean_object* v_fst_1404_; lean_object* v_snd_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1438_; 
v_v_1403_ = lean_array_uget(v_bs_1395_, v_i_1394_);
v_fst_1404_ = lean_ctor_get(v_v_1403_, 0);
v_snd_1405_ = lean_ctor_get(v_v_1403_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_v_1403_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1407_ = v_v_1403_;
v_isShared_1408_ = v_isSharedCheck_1438_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_snd_1405_);
lean_inc(v_fst_1404_);
lean_dec(v_v_1403_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1438_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_op_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_bs_x27_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v_op_1409_ = lean_ctor_get(v_preContext_1391_, 1);
v___x_1410_ = lean_box(0);
v___x_1411_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
v___x_1412_ = lean_unsigned_to_nat(0u);
v_bs_x27_1413_ = lean_array_uset(v_bs_1395_, v_i_1394_, v___x_1412_);
v___x_1414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1));
lean_inc(v_u_1390_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 1);
lean_ctor_set(v___x_1407_, 1, v___x_1410_);
lean_ctor_set(v___x_1407_, 0, v_u_1390_);
v___x_1416_ = v___x_1407_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_u_1390_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v___x_1410_);
v___x_1416_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___y_1418_; lean_object* v___x_1426_; lean_object* v_isNeutralClass_1427_; 
lean_inc_ref(v___x_1416_);
v___x_1426_ = l_Lean_mkConst(v___x_1414_, v___x_1416_);
lean_inc(v_fst_1404_);
lean_inc_ref(v_op_1409_);
lean_inc_ref(v_00_u03b1_1392_);
v_isNeutralClass_1427_ = l_Lean_mkApp3(v___x_1426_, v_00_u03b1_1392_, v_op_1409_, v_fst_1404_);
if (lean_obj_tag(v_snd_1405_) == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9);
v___x_1429_ = l_Lean_Expr_app___override(v___x_1411_, v_isNeutralClass_1427_);
v___x_1430_ = l_Lean_Expr_app___override(v___x_1428_, v___x_1429_);
v___y_1418_ = v___x_1430_;
goto v___jp_1417_;
}
else
{
lean_object* v_val_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v_val_1431_ = lean_ctor_get(v_snd_1405_, 0);
lean_inc(v_val_1431_);
lean_dec_ref_known(v_snd_1405_, 1);
v___x_1432_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
v___x_1433_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13);
lean_inc_ref(v_isNeutralClass_1427_);
v___x_1434_ = l_Lean_Expr_app___override(v___x_1411_, v_isNeutralClass_1427_);
v___x_1435_ = l_Lean_mkAppB(v___x_1432_, v_isNeutralClass_1427_, v_val_1431_);
v___x_1436_ = l_Lean_mkAppB(v___x_1433_, v___x_1434_, v___x_1435_);
v___y_1418_ = v___x_1436_;
goto v___jp_1417_;
}
v___jp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8));
v___x_1420_ = l_Lean_mkConst(v___x_1419_, v___x_1416_);
lean_inc_ref(v_op_1409_);
lean_inc_ref(v_00_u03b1_1392_);
v___x_1421_ = l_Lean_mkApp4(v___x_1420_, v_00_u03b1_1392_, v_op_1409_, v_fst_1404_, v___y_1418_);
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_add(v_i_1394_, v___x_1422_);
v___x_1424_ = lean_array_uset(v_bs_x27_1413_, v_i_1394_, v___x_1421_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1390_, v_preContext_1391_, v_00_u03b1_1392_, v_sz_1393_, v___x_1423_, v___x_1424_);
return v___x_1425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0___boxed(lean_object* v_u_1439_, lean_object* v_preContext_1440_, lean_object* v_00_u03b1_1441_, lean_object* v_sz_1442_, lean_object* v_i_1443_, lean_object* v_bs_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
size_t v_sz_boxed_1450_; size_t v_i_boxed_1451_; lean_object* v_res_1452_; 
v_sz_boxed_1450_ = lean_unbox_usize(v_sz_1442_);
lean_dec(v_sz_1442_);
v_i_boxed_1451_ = lean_unbox_usize(v_i_1443_);
lean_dec(v_i_1443_);
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(v_u_1439_, v_preContext_1440_, v_00_u03b1_1441_, v_sz_boxed_1450_, v_i_boxed_1451_, v_bs_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = lean_box(0);
v___x_1454_ = l_Lean_instInhabitedExpr;
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___x_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(lean_object* v_preContext_1468_, lean_object* v_00_u03b1_1469_, lean_object* v_u_1470_, lean_object* v_vars_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; size_t v_sz_1480_; size_t v___x_1481_; lean_object* v___x_1482_; 
v___x_1477_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0_once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_array_get(v___x_1477_, v_vars_1471_, v___x_1478_);
v_sz_1480_ = lean_array_size(v_vars_1471_);
v___x_1481_ = ((size_t)0ULL);
lean_inc_ref(v_00_u03b1_1469_);
lean_inc_ref(v_preContext_1468_);
lean_inc(v_u_1470_);
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(v_u_1470_, v_preContext_1468_, v_00_u03b1_1469_, v_sz_1480_, v___x_1481_, v_vars_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v_op_1484_; lean_object* v_assoc_1485_; lean_object* v_comm_1486_; lean_object* v_idem_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1482_, 1);
v_op_1484_ = lean_ctor_get(v_preContext_1468_, 1);
lean_inc_ref_n(v_op_1484_, 2);
v_assoc_1485_ = lean_ctor_get(v_preContext_1468_, 2);
lean_inc_ref(v_assoc_1485_);
v_comm_1486_ = lean_ctor_get(v_preContext_1468_, 3);
lean_inc(v_comm_1486_);
v_idem_1487_ = lean_ctor_get(v_preContext_1468_, 4);
lean_inc(v_idem_1487_);
lean_dec_ref(v_preContext_1468_);
v___x_1488_ = lean_box(0);
v___x_1489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1490_ = lean_array_to_list(v_a_1483_);
v___x_1491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1));
v___x_1492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_u_1470_);
lean_ctor_set(v___x_1492_, 1, v___x_1488_);
lean_inc_ref(v___x_1492_);
v___x_1493_ = l_Lean_mkConst(v___x_1491_, v___x_1492_);
lean_inc_ref(v_00_u03b1_1469_);
v___x_1494_ = l_Lean_mkAppB(v___x_1493_, v_00_u03b1_1469_, v_op_1484_);
v___x_1495_ = l_Lean_Meta_mkListLit(v___x_1494_, v___x_1490_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1526_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1526_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1526_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_fst_1500_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___y_1513_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_fst_1500_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_fst_1500_);
lean_dec(v___x_1479_);
v___x_1510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
v___x_1511_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
v___x_1520_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__4));
lean_inc_ref(v___x_1492_);
v___x_1521_ = l_Lean_mkConst(v___x_1520_, v___x_1492_);
lean_inc_ref(v_op_1484_);
lean_inc_ref(v_00_u03b1_1469_);
v___x_1522_ = l_Lean_mkAppB(v___x_1521_, v_00_u03b1_1469_, v_op_1484_);
if (lean_obj_tag(v_comm_1486_) == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(v___x_1489_, v___x_1510_, v___x_1522_);
v___y_1513_ = v___x_1523_;
goto v___jp_1512_;
}
else
{
lean_object* v_val_1524_; lean_object* v___x_1525_; 
v_val_1524_ = lean_ctor_get(v_comm_1486_, 0);
lean_inc(v_val_1524_);
lean_dec_ref_known(v_comm_1486_, 1);
v___x_1525_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(v___x_1489_, v___x_1510_, v___x_1511_, v___x_1522_, v_val_1524_);
v___y_1513_ = v___x_1525_;
goto v___jp_1512_;
}
v___jp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3));
v___x_1505_ = l_Lean_mkConst(v___x_1504_, v___x_1492_);
v___x_1506_ = l_Lean_mkApp7(v___x_1505_, v_00_u03b1_1469_, v_op_1484_, v_assoc_1485_, v___y_1502_, v___y_1503_, v_a_1496_, v_fst_1500_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1506_);
v___x_1508_ = v___x_1498_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
v___jp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__6));
lean_inc_ref(v___x_1492_);
v___x_1515_ = l_Lean_mkConst(v___x_1514_, v___x_1492_);
lean_inc_ref(v_op_1484_);
lean_inc_ref(v_00_u03b1_1469_);
v___x_1516_ = l_Lean_mkAppB(v___x_1515_, v_00_u03b1_1469_, v_op_1484_);
if (lean_obj_tag(v_idem_1487_) == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(v___x_1489_, v___x_1510_, v___x_1516_);
v___y_1502_ = v___y_1513_;
v___y_1503_ = v___x_1517_;
goto v___jp_1501_;
}
else
{
lean_object* v_val_1518_; lean_object* v___x_1519_; 
v_val_1518_ = lean_ctor_get(v_idem_1487_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v_idem_1487_, 1);
v___x_1519_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(v___x_1489_, v___x_1510_, v___x_1511_, v___x_1516_, v_val_1518_);
v___y_1502_ = v___y_1513_;
v___y_1503_ = v___x_1519_;
goto v___jp_1501_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1492_, 2);
lean_dec(v_idem_1487_);
lean_dec(v_comm_1486_);
lean_dec_ref(v_assoc_1485_);
lean_dec_ref(v_op_1484_);
lean_dec(v___x_1479_);
lean_dec_ref(v_00_u03b1_1469_);
return v___x_1495_;
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v___x_1479_);
lean_dec(v_u_1470_);
lean_dec_ref(v_00_u03b1_1469_);
lean_dec_ref(v_preContext_1468_);
v_a_1527_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1482_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1482_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___boxed(lean_object* v_preContext_1535_, lean_object* v_00_u03b1_1536_, lean_object* v_u_1537_, lean_object* v_vars_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(v_preContext_1535_, v_00_u03b1_1536_, v_u_1537_, v_vars_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(lean_object* v_u_1545_, lean_object* v_preContext_1546_, lean_object* v_00_u03b1_1547_, size_t v_sz_1548_, size_t v_i_1549_, lean_object* v_bs_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1545_, v_preContext_1546_, v_00_u03b1_1547_, v_sz_1548_, v_i_1549_, v_bs_1550_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___boxed(lean_object* v_u_1557_, lean_object* v_preContext_1558_, lean_object* v_00_u03b1_1559_, lean_object* v_sz_1560_, lean_object* v_i_1561_, lean_object* v_bs_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
size_t v_sz_boxed_1568_; size_t v_i_boxed_1569_; lean_object* v_res_1570_; 
v_sz_boxed_1568_ = lean_unbox_usize(v_sz_1560_);
lean_dec(v_sz_1560_);
v_i_boxed_1569_ = lean_unbox_usize(v_i_1561_);
lean_dec(v_i_1561_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(v_u_1557_, v_preContext_1558_, v_00_u03b1_1559_, v_sz_boxed_1568_, v_i_boxed_1569_, v_bs_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1570_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2));
v___x_1581_ = l_Lean_mkConst(v___x_1580_, v___x_1579_);
return v___x_1581_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5));
v___x_1591_ = l_Lean_mkConst(v___x_1590_, v___x_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(lean_object* v_a_1592_){
_start:
{
if (lean_obj_tag(v_a_1592_) == 0)
{
lean_object* v_x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_x_1593_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_x_1593_);
lean_dec_ref_known(v_a_1592_, 1);
v___x_1594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3_once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3);
v___x_1595_ = l_Lean_mkNatLit(v_x_1593_);
v___x_1596_ = l_Lean_Expr_app___override(v___x_1594_, v___x_1595_);
return v___x_1596_;
}
else
{
lean_object* v_lhs_1597_; lean_object* v_rhs_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_lhs_1597_ = lean_ctor_get(v_a_1592_, 0);
lean_inc_ref(v_lhs_1597_);
v_rhs_1598_ = lean_ctor_get(v_a_1592_, 1);
lean_inc_ref(v_rhs_1598_);
lean_dec_ref_known(v_a_1592_, 2);
v___x_1599_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6_once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6);
v___x_1600_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v_lhs_1597_);
v___x_1601_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v_rhs_1598_);
v___x_1602_ = l_Lean_mkAppB(v___x_1599_, v___x_1600_, v___x_1601_);
return v___x_1602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(lean_object* v_preContext_1603_, lean_object* v_vars_1604_, lean_object* v_a_1605_){
_start:
{
if (lean_obj_tag(v_a_1605_) == 0)
{
lean_object* v_x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec_ref(v_preContext_1603_);
v_x_1606_ = lean_ctor_get(v_a_1605_, 0);
v___x_1607_ = l_Lean_instInhabitedExpr;
v___x_1608_ = lean_array_get_borrowed(v___x_1607_, v_vars_1604_, v_x_1606_);
lean_inc(v___x_1608_);
return v___x_1608_;
}
else
{
lean_object* v_lhs_1609_; lean_object* v_rhs_1610_; lean_object* v_op_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_lhs_1609_ = lean_ctor_get(v_a_1605_, 0);
v_rhs_1610_ = lean_ctor_get(v_a_1605_, 1);
v_op_1611_ = lean_ctor_get(v_preContext_1603_, 1);
lean_inc_ref(v_op_1611_);
lean_inc_ref(v_preContext_1603_);
v___x_1612_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1603_, v_vars_1604_, v_lhs_1609_);
v___x_1613_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1603_, v_vars_1604_, v_rhs_1610_);
v___x_1614_ = l_Lean_mkAppB(v_op_1611_, v___x_1612_, v___x_1613_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget___boxed(lean_object* v_preContext_1615_, lean_object* v_vars_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1615_, v_vars_1616_, v_a_1617_);
lean_dec_ref(v_a_1617_);
lean_dec_ref(v_vars_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(lean_object* v_msg_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___f_1626_; lean_object* v___x_1991__overap_1627_; lean_object* v___x_1628_; 
v___f_1626_ = ((lean_object*)(l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0));
v___x_1991__overap_1627_ = lean_panic_fn_borrowed(v___f_1626_, v_msg_1620_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
v___x_1628_ = lean_apply_5(v___x_1991__overap_1627_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, lean_box(0));
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___boxed(lean_object* v_msg_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(v_msg_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(lean_object* v_x_1636_){
_start:
{
if (lean_obj_tag(v_x_1636_) == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = ((lean_object*)(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0));
return v___x_1637_;
}
else
{
lean_object* v_tail_1638_; 
v_tail_1638_ = lean_ctor_get(v_x_1636_, 1);
if (lean_obj_tag(v_tail_1638_) == 0)
{
lean_object* v_head_1639_; lean_object* v___x_1640_; 
v_head_1639_ = lean_ctor_get(v_x_1636_, 0);
lean_inc(v_head_1639_);
lean_dec_ref_known(v_x_1636_, 2);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_head_1639_);
return v___x_1640_;
}
else
{
lean_object* v_head_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1650_; 
lean_inc(v_tail_1638_);
v_head_1641_ = lean_ctor_get(v_x_1636_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1636_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v_x_1636_, 1);
lean_dec(v_unused_1651_);
v___x_1643_ = v_x_1636_;
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_head_1641_);
lean_dec(v_x_1636_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v_head_1641_);
v___x_1646_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v_tail_1638_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v___x_1646_);
lean_ctor_set(v___x_1643_, 0, v___x_1645_);
v___x_1648_ = v___x_1643_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(size_t v_sz_1652_, size_t v_i_1653_, lean_object* v_bs_1654_){
_start:
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_usize_dec_lt(v_i_1653_, v_sz_1652_);
if (v___x_1655_ == 0)
{
return v_bs_1654_;
}
else
{
lean_object* v_v_1656_; lean_object* v_fst_1657_; lean_object* v___x_1658_; lean_object* v_bs_x27_1659_; size_t v___x_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v_v_1656_ = lean_array_uget_borrowed(v_bs_1654_, v_i_1653_);
v_fst_1657_ = lean_ctor_get(v_v_1656_, 0);
lean_inc(v_fst_1657_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v_bs_x27_1659_ = lean_array_uset(v_bs_1654_, v_i_1653_, v___x_1658_);
v___x_1660_ = ((size_t)1ULL);
v___x_1661_ = lean_usize_add(v_i_1653_, v___x_1660_);
v___x_1662_ = lean_array_uset(v_bs_x27_1659_, v_i_1653_, v_fst_1657_);
v_i_1653_ = v___x_1661_;
v_bs_1654_ = v___x_1662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2___boxed(lean_object* v_sz_1664_, lean_object* v_i_1665_, lean_object* v_bs_1666_){
_start:
{
size_t v_sz_boxed_1667_; size_t v_i_boxed_1668_; lean_object* v_res_1669_; 
v_sz_boxed_1667_ = lean_unbox_usize(v_sz_1664_);
lean_dec(v_sz_1664_);
v_i_boxed_1668_ = lean_unbox_usize(v_i_1665_);
lean_dec(v_i_1665_);
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(v_sz_boxed_1667_, v_i_boxed_1668_, v_bs_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(size_t v_sz_1670_, size_t v_i_1671_, lean_object* v_bs_1672_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1671_, v_sz_1670_);
if (v___x_1673_ == 0)
{
return v_bs_1672_;
}
else
{
lean_object* v_v_1674_; lean_object* v_snd_1675_; lean_object* v___x_1676_; lean_object* v_bs_x27_1677_; uint8_t v___y_1679_; 
v_v_1674_ = lean_array_uget_borrowed(v_bs_1672_, v_i_1671_);
v_snd_1675_ = lean_ctor_get(v_v_1674_, 1);
lean_inc(v_snd_1675_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v_bs_x27_1677_ = lean_array_uset(v_bs_1672_, v_i_1671_, v___x_1676_);
if (lean_obj_tag(v_snd_1675_) == 0)
{
uint8_t v___x_1685_; 
v___x_1685_ = 0;
v___y_1679_ = v___x_1685_;
goto v___jp_1678_;
}
else
{
lean_dec_ref_known(v_snd_1675_, 1);
v___y_1679_ = v___x_1673_;
goto v___jp_1678_;
}
v___jp_1678_:
{
size_t v___x_1680_; size_t v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1671_, v___x_1680_);
v___x_1682_ = lean_box(v___y_1679_);
v___x_1683_ = lean_array_uset(v_bs_x27_1677_, v_i_1671_, v___x_1682_);
v_i_1671_ = v___x_1681_;
v_bs_1672_ = v___x_1683_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0___boxed(lean_object* v_sz_1686_, lean_object* v_i_1687_, lean_object* v_bs_1688_){
_start:
{
size_t v_sz_boxed_1689_; size_t v_i_boxed_1690_; lean_object* v_res_1691_; 
v_sz_boxed_1689_ = lean_unbox_usize(v_sz_1686_);
lean_dec(v_sz_1686_);
v_i_boxed_1690_ = lean_unbox_usize(v_i_1687_);
lean_dec(v_i_1687_);
v_res_1691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(v_sz_boxed_1689_, v_i_boxed_1690_, v_bs_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(lean_object* v_ctx_1692_, lean_object* v_a_1693_){
_start:
{
if (lean_obj_tag(v_a_1693_) == 0)
{
return v_a_1693_;
}
else
{
lean_object* v_head_1694_; lean_object* v_tail_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1709_; 
v_head_1694_ = lean_ctor_get(v_a_1693_, 0);
v_tail_1695_ = lean_ctor_get(v_a_1693_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_a_1693_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1697_ = v_a_1693_;
v_isShared_1698_ = v_isSharedCheck_1709_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_tail_1695_);
lean_inc(v_head_1694_);
lean_dec(v_a_1693_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1709_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v_snd_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_snd_1699_ = lean_ctor_get(v_ctx_1692_, 1);
v___x_1700_ = 0;
v___x_1701_ = lean_box(v___x_1700_);
v___x_1702_ = lean_array_get(v___x_1701_, v_snd_1699_, v_head_1694_);
lean_dec(v___x_1701_);
v___x_1703_ = lean_unbox(v___x_1702_);
lean_dec(v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(v_ctx_1692_, v_tail_1695_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v___x_1704_);
v___x_1706_ = v___x_1697_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_head_1694_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
else
{
lean_del_object(v___x_1697_);
lean_dec(v_head_1694_);
v_a_1693_ = v_tail_1695_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3___boxed(lean_object* v_ctx_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(v_ctx_1710_, v_a_1711_);
lean_dec_ref(v_ctx_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(lean_object* v_ctx_1713_, lean_object* v_x_1714_){
_start:
{
if (lean_obj_tag(v_x_1714_) == 0)
{
return v_x_1714_;
}
else
{
lean_object* v_head_1715_; lean_object* v___x_1716_; 
v_head_1715_ = lean_ctor_get(v_x_1714_, 0);
lean_inc(v_head_1715_);
v___x_1716_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(v_ctx_1713_, v_x_1714_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_head_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
return v___x_1717_;
}
else
{
lean_dec(v_head_1715_);
return v___x_1716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1___boxed(lean_object* v_ctx_1718_, lean_object* v_x_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(v_ctx_1718_, v_x_1719_);
lean_dec_ref(v_ctx_1718_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(lean_object* v_ctx_1721_, lean_object* v_e_1722_){
_start:
{
lean_object* v_fst_1723_; lean_object* v_comm_1724_; lean_object* v_idem_1725_; lean_object* v___y_1727_; lean_object* v_xs_1729_; lean_object* v_xs_1730_; 
v_fst_1723_ = lean_ctor_get(v_ctx_1721_, 0);
v_comm_1724_ = lean_ctor_get(v_fst_1723_, 3);
v_idem_1725_ = lean_ctor_get(v_fst_1723_, 4);
v_xs_1729_ = l_Lean_Data_AC_Expr_toList(v_e_1722_);
v_xs_1730_ = l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(v_ctx_1721_, v_xs_1729_);
if (lean_obj_tag(v_comm_1724_) == 0)
{
v___y_1727_ = v_xs_1730_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Data_AC_sort(v_xs_1730_);
v___y_1727_ = v___x_1731_;
goto v___jp_1726_;
}
v___jp_1726_:
{
if (lean_obj_tag(v_idem_1725_) == 0)
{
return v___y_1727_;
}
else
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Data_AC_mergeIdem(v___y_1727_);
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1___boxed(lean_object* v_ctx_1732_, lean_object* v_e_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(v_ctx_1732_, v_e_1733_);
lean_dec_ref(v_e_1733_);
lean_dec_ref(v_ctx_1732_);
return v_res_1734_;
}
}
static lean_object* _init_l_Lean_Meta_AC_buildNormProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_box(0);
v___x_1741_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___lam__0___closed__2));
v___x_1742_ = l_Lean_mkConst(v___x_1741_, v___x_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___lam__0(lean_object* v___x_1750_, lean_object* v_fst_1751_, lean_object* v_preContext_1752_, lean_object* v_snd_1753_, lean_object* v_varsData_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_array_get_borrowed(v___x_1750_, v_fst_1751_, v___x_1760_);
lean_inc(v___y_1758_);
lean_inc_ref(v___y_1757_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
lean_inc(v___x_1761_);
v___x_1762_ = lean_infer_type(v___x_1761_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc_n(v_a_1763_, 2);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l_Lean_Meta_getLevel(v_a_1763_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc_n(v_a_1765_, 2);
lean_dec_ref_known(v___x_1764_, 1);
lean_inc_ref(v_varsData_1754_);
lean_inc(v_a_1763_);
lean_inc_ref(v_preContext_1752_);
v___x_1766_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(v_preContext_1752_, v_a_1763_, v_a_1765_, v_varsData_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_obj_once(&l_Lean_Meta_AC_buildNormProof___lam__0___closed__3, &l_Lean_Meta_AC_buildNormProof___lam__0___closed__3_once, _init_l_Lean_Meta_AC_buildNormProof___lam__0___closed__3);
v___x_1770_ = l_Lean_Meta_mkEqRefl(v___x_1769_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; size_t v_sz_1772_; size_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v_sz_1772_ = lean_array_size(v_varsData_1754_);
v___x_1773_ = ((size_t)0ULL);
lean_inc_ref(v_varsData_1754_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(v_sz_1772_, v___x_1773_, v_varsData_1754_);
lean_inc_ref_n(v_preContext_1752_, 2);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_preContext_1752_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(v___x_1775_, v_snd_1753_);
lean_dec_ref_known(v___x_1775_, 2);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(v_sz_1772_, v___x_1773_, v_varsData_1754_);
v___x_1778_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v___x_1776_);
v___x_1779_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1752_, v___x_1777_, v_snd_1753_);
v___x_1780_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1752_, v___x_1777_, v___x_1778_);
lean_dec_ref(v___x_1777_);
v___x_1781_ = l_Lean_Meta_mkEq(v___x_1779_, v___x_1780_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1803_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1803_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1803_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1786_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v_snd_1753_);
v___x_1787_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v___x_1778_);
v___x_1788_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___lam__0___closed__5));
v___x_1789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1765_);
lean_ctor_set(v___x_1789_, 1, v___x_1768_);
v___x_1790_ = l_Lean_mkConst(v___x_1788_, v___x_1789_);
v___x_1791_ = lean_unsigned_to_nat(5u);
v___x_1792_ = lean_mk_empty_array_with_capacity(v___x_1791_);
v___x_1793_ = lean_array_push(v___x_1792_, v_a_1763_);
v___x_1794_ = lean_array_push(v___x_1793_, v_a_1767_);
v___x_1795_ = lean_array_push(v___x_1794_, v___x_1786_);
v___x_1796_ = lean_array_push(v___x_1795_, v___x_1787_);
v___x_1797_ = lean_array_push(v___x_1796_, v_a_1771_);
v___x_1798_ = l_Lean_mkAppN(v___x_1790_, v___x_1797_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = l_Lean_Meta_mkExpectedPropHint(v___x_1798_, v_a_1782_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1799_);
v___x_1801_ = v___x_1784_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
else
{
lean_dec_ref(v___x_1778_);
lean_dec(v_a_1771_);
lean_dec(v_a_1767_);
lean_dec(v_a_1765_);
lean_dec(v_a_1763_);
lean_dec_ref(v_snd_1753_);
return v___x_1781_;
}
}
else
{
lean_dec(v_a_1767_);
lean_dec(v_a_1765_);
lean_dec(v_a_1763_);
lean_dec_ref(v_varsData_1754_);
lean_dec_ref(v_snd_1753_);
lean_dec_ref(v_preContext_1752_);
return v___x_1770_;
}
}
else
{
lean_dec(v_a_1765_);
lean_dec(v_a_1763_);
lean_dec_ref(v_varsData_1754_);
lean_dec_ref(v_snd_1753_);
lean_dec_ref(v_preContext_1752_);
return v___x_1766_;
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_a_1763_);
lean_dec_ref(v_varsData_1754_);
lean_dec_ref(v_snd_1753_);
lean_dec_ref(v_preContext_1752_);
v_a_1804_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1764_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1764_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_dec_ref(v_varsData_1754_);
lean_dec_ref(v_snd_1753_);
lean_dec_ref(v_preContext_1752_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___boxed(lean_object* v___x_1812_, lean_object* v_fst_1813_, lean_object* v_preContext_1814_, lean_object* v_snd_1815_, lean_object* v_varsData_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Meta_AC_buildNormProof___lam__0(v___x_1812_, v_fst_1813_, v_preContext_1814_, v_snd_1815_, v_varsData_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v_fst_1813_);
lean_dec_ref(v___x_1812_);
return v_res_1822_;
}
}
static lean_object* _init_l_Lean_Meta_AC_buildNormProof___closed__5(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1829_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__4));
v___x_1830_ = lean_unsigned_to_nat(52u);
v___x_1831_ = lean_unsigned_to_nat(132u);
v___x_1832_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__3));
v___x_1833_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__2));
v___x_1834_ = l_mkPanicMessageWithDecl(v___x_1833_, v___x_1832_, v___x_1831_, v___x_1830_, v___x_1829_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof(lean_object* v_preContext_1835_, lean_object* v_l_1836_, lean_object* v_r_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_op_1843_; lean_object* v___x_1844_; 
v_op_1843_ = lean_ctor_get(v_preContext_1835_, 1);
lean_inc_ref(v_op_1843_);
v___x_1844_ = l_Lean_Meta_AC_toACExpr(v_op_1843_, v_l_1836_, v_r_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v_fst_1846_; lean_object* v_snd_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1889_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v_fst_1846_ = lean_ctor_get(v_a_1845_, 0);
v_snd_1847_ = lean_ctor_get(v_a_1845_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_a_1845_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1849_ = v_a_1845_;
v_isShared_1850_ = v_isSharedCheck_1889_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_snd_1847_);
lean_inc(v_fst_1846_);
lean_dec(v_a_1845_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1889_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___f_1852_; lean_object* v___x_1853_; 
v___x_1851_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_preContext_1835_);
lean_inc(v_fst_1846_);
v___f_1852_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_buildNormProof___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1852_, 0, v___x_1851_);
lean_closure_set(v___f_1852_, 1, v_fst_1846_);
lean_closure_set(v___f_1852_, 2, v_preContext_1835_);
lean_closure_set(v___f_1852_, 3, v_snd_1847_);
v___x_1853_ = l_Lean_Meta_AC_abstractAtoms(v_preContext_1835_, v_fst_1846_, v___f_1852_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc_n(v_a_1854_, 2);
lean_dec_ref_known(v___x_1853_, 1);
lean_inc(v_a_1841_);
lean_inc_ref(v_a_1840_);
lean_inc(v_a_1839_);
lean_inc_ref(v_a_1838_);
v___x_1855_ = lean_infer_type(v_a_1854_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1872_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1872_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1872_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__1));
v___x_1861_ = lean_unsigned_to_nat(3u);
v___x_1862_ = l_Lean_Expr_isAppOfArity(v_a_1856_, v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_del_object(v___x_1858_);
lean_dec(v_a_1856_);
lean_dec(v_a_1854_);
lean_del_object(v___x_1849_);
v___x_1863_ = lean_obj_once(&l_Lean_Meta_AC_buildNormProof___closed__5, &l_Lean_Meta_AC_buildNormProof___closed__5_once, _init_l_Lean_Meta_AC_buildNormProof___closed__5);
v___x_1864_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(v___x_1863_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = l_Lean_Expr_appArg_x21(v_a_1856_);
lean_dec(v_a_1856_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v___x_1865_);
lean_ctor_set(v___x_1849_, 0, v_a_1854_);
v___x_1867_ = v___x_1849_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1854_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1867_);
v___x_1869_ = v___x_1858_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_a_1854_);
lean_del_object(v___x_1849_);
v_a_1873_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1855_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1855_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_del_object(v___x_1849_);
v_a_1881_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1853_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1853_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v_preContext_1835_);
v_a_1890_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1844_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1844_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___boxed(lean_object* v_preContext_1898_, lean_object* v_l_1899_, lean_object* v_r_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Meta_AC_buildNormProof(v_preContext_1898_, v_l_1899_, v_r_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3(lean_object* v_ctx_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v_x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___boxed(lean_object* v_ctx_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3(v_ctx_1910_, v_x_1911_);
lean_dec_ref(v_ctx_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___redArg(lean_object* v_e_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_e_1921_; lean_object* v_op_1928_; lean_object* v_l_1929_; lean_object* v_r_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; 
if (lean_obj_tag(v_e_1913_) == 5)
{
lean_object* v_fn_1986_; 
v_fn_1986_ = lean_ctor_get(v_e_1913_, 0);
if (lean_obj_tag(v_fn_1986_) == 5)
{
lean_object* v_parent_x3f_1987_; 
v_parent_x3f_1987_ = lean_ctor_get(v_a_1914_, 8);
if (lean_obj_tag(v_parent_x3f_1987_) == 1)
{
lean_object* v_val_1988_; 
v_val_1988_ = lean_ctor_get(v_parent_x3f_1987_, 0);
if (lean_obj_tag(v_val_1988_) == 5)
{
lean_object* v_fn_1989_; 
v_fn_1989_ = lean_ctor_get(v_val_1988_, 0);
if (lean_obj_tag(v_fn_1989_) == 5)
{
lean_object* v_arg_1990_; lean_object* v_fn_1991_; lean_object* v_arg_1992_; lean_object* v_fn_1993_; lean_object* v___x_1994_; 
v_arg_1990_ = lean_ctor_get(v_e_1913_, 1);
v_fn_1991_ = lean_ctor_get(v_fn_1986_, 0);
v_arg_1992_ = lean_ctor_get(v_fn_1986_, 1);
v_fn_1993_ = lean_ctor_get(v_fn_1989_, 0);
lean_inc_ref(v_fn_1993_);
lean_inc_ref(v_fn_1991_);
v___x_1994_ = l_Lean_Meta_isExprDefEq(v_fn_1991_, v_fn_1993_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2056_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2056_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2056_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
uint8_t v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = 1;
v___x_2000_ = lean_unbox(v_a_1995_);
lean_dec(v_a_1995_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; 
lean_del_object(v___x_1997_);
lean_inc_ref(v_fn_1991_);
v___x_2001_ = l_Lean_Meta_AC_preContext(v_fn_1991_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2041_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2041_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2041_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
if (lean_obj_tag(v_a_2002_) == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2006_ = lean_box(0);
v___x_2007_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2007_, 0, v_e_1913_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*2, v___x_1999_);
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2008_);
v___x_2010_ = v___x_2004_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
else
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2040_; 
lean_inc_ref(v_arg_1992_);
lean_inc_ref(v_arg_1990_);
lean_del_object(v___x_2004_);
lean_dec_ref_known(v_e_1913_, 2);
v_val_2012_ = lean_ctor_get(v_a_2002_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_a_2002_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2014_ = v_a_2002_;
v_isShared_2015_ = v_isSharedCheck_2040_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v_a_2002_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2040_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Meta_AC_buildNormProof(v_val_2012_, v_arg_1992_, v_arg_1990_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2031_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2031_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2031_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v_fst_2021_; lean_object* v_snd_2022_; lean_object* v___x_2024_; 
v_fst_2021_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_fst_2021_);
v_snd_2022_ = lean_ctor_get(v_a_2017_, 1);
lean_inc(v_snd_2022_);
lean_dec(v_a_2017_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v_fst_2021_);
v___x_2024_ = v___x_2014_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_fst_2021_);
v___x_2024_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2025_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2025_, 0, v_snd_2022_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*2, v___x_1999_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2026_);
v___x_2028_ = v___x_2019_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_del_object(v___x_2014_);
v_a_2032_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2016_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2016_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref_known(v_e_1913_, 2);
v_a_2042_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2001_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2001_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2051_, 0, v_e_1913_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*2, v___x_1999_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2052_);
v___x_2054_ = v___x_1997_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
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
lean_dec_ref_known(v_e_1913_, 2);
v_a_2057_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_1994_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_1994_);
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
else
{
lean_object* v_arg_2065_; lean_object* v_fn_2066_; lean_object* v_arg_2067_; 
v_arg_2065_ = lean_ctor_get(v_e_1913_, 1);
v_fn_2066_ = lean_ctor_get(v_fn_1986_, 0);
v_arg_2067_ = lean_ctor_get(v_fn_1986_, 1);
lean_inc_ref(v_arg_2065_);
lean_inc_ref(v_arg_2067_);
lean_inc_ref(v_fn_2066_);
v_op_1928_ = v_fn_2066_;
v_l_1929_ = v_arg_2067_;
v_r_1930_ = v_arg_2065_;
v___y_1931_ = v_a_1915_;
v___y_1932_ = v_a_1916_;
v___y_1933_ = v_a_1917_;
v___y_1934_ = v_a_1918_;
goto v___jp_1927_;
}
}
else
{
lean_object* v_arg_2068_; lean_object* v_fn_2069_; lean_object* v_arg_2070_; 
v_arg_2068_ = lean_ctor_get(v_e_1913_, 1);
v_fn_2069_ = lean_ctor_get(v_fn_1986_, 0);
v_arg_2070_ = lean_ctor_get(v_fn_1986_, 1);
lean_inc_ref(v_arg_2068_);
lean_inc_ref(v_arg_2070_);
lean_inc_ref(v_fn_2069_);
v_op_1928_ = v_fn_2069_;
v_l_1929_ = v_arg_2070_;
v_r_1930_ = v_arg_2068_;
v___y_1931_ = v_a_1915_;
v___y_1932_ = v_a_1916_;
v___y_1933_ = v_a_1917_;
v___y_1934_ = v_a_1918_;
goto v___jp_1927_;
}
}
else
{
lean_object* v_arg_2071_; lean_object* v_fn_2072_; lean_object* v_arg_2073_; 
v_arg_2071_ = lean_ctor_get(v_e_1913_, 1);
v_fn_2072_ = lean_ctor_get(v_fn_1986_, 0);
v_arg_2073_ = lean_ctor_get(v_fn_1986_, 1);
lean_inc_ref(v_arg_2071_);
lean_inc_ref(v_arg_2073_);
lean_inc_ref(v_fn_2072_);
v_op_1928_ = v_fn_2072_;
v_l_1929_ = v_arg_2073_;
v_r_1930_ = v_arg_2071_;
v___y_1931_ = v_a_1915_;
v___y_1932_ = v_a_1916_;
v___y_1933_ = v_a_1917_;
v___y_1934_ = v_a_1918_;
goto v___jp_1927_;
}
}
else
{
v_e_1921_ = v_e_1913_;
goto v___jp_1920_;
}
}
else
{
v_e_1921_ = v_e_1913_;
goto v___jp_1920_;
}
v___jp_1920_:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1922_ = lean_box(0);
v___x_1923_ = 1;
v___x_1924_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1924_, 0, v_e_1921_);
lean_ctor_set(v___x_1924_, 1, v___x_1922_);
lean_ctor_set_uint8(v___x_1924_, sizeof(void*)*2, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
v___jp_1927_:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_Meta_AC_preContext(v_op_1928_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1977_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1977_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1977_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
if (lean_obj_tag(v_a_1936_) == 0)
{
lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_dec_ref(v_r_1930_);
lean_dec_ref(v_l_1929_);
v___x_1940_ = lean_box(0);
v___x_1941_ = 1;
v___x_1942_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1942_, 0, v_e_1913_);
lean_ctor_set(v___x_1942_, 1, v___x_1940_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*2, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1943_);
v___x_1945_ = v___x_1938_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
else
{
lean_object* v_val_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1976_; 
lean_del_object(v___x_1938_);
lean_dec_ref(v_e_1913_);
v_val_1947_ = lean_ctor_get(v_a_1936_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_a_1936_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1949_ = v_a_1936_;
v_isShared_1950_ = v_isSharedCheck_1976_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_val_1947_);
lean_dec(v_a_1936_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1976_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Meta_AC_buildNormProof(v_val_1947_, v_l_1929_, v_r_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1967_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1967_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1967_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_fst_1956_; lean_object* v_snd_1957_; lean_object* v___x_1959_; 
v_fst_1956_ = lean_ctor_get(v_a_1952_, 0);
lean_inc(v_fst_1956_);
v_snd_1957_ = lean_ctor_get(v_a_1952_, 1);
lean_inc(v_snd_1957_);
lean_dec(v_a_1952_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v_fst_1956_);
v___x_1959_ = v___x_1949_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_fst_1956_);
v___x_1959_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1960_ = 1;
v___x_1961_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1961_, 0, v_snd_1957_);
lean_ctor_set(v___x_1961_, 1, v___x_1959_);
lean_ctor_set_uint8(v___x_1961_, sizeof(void*)*2, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1962_);
v___x_1964_ = v___x_1954_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_del_object(v___x_1949_);
v_a_1968_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1951_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1951_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_r_1930_);
lean_dec_ref(v_l_1929_);
lean_dec_ref(v_e_1913_);
v_a_1978_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1935_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1935_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___redArg___boxed(lean_object* v_e_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_Meta_AC_post___redArg(v_e_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_a_2075_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post(lean_object* v_e_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Meta_AC_post___redArg(v_e_2082_, v_a_2084_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___boxed(lean_object* v_e_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_Meta_AC_post(v_e_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(lean_object* v_e_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v___x_2105_; 
v___x_2105_ = l_Lean_Expr_hasMVar(v_e_2102_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_e_2102_);
return v___x_2106_;
}
else
{
lean_object* v___x_2107_; lean_object* v_mctx_2108_; lean_object* v___x_2109_; lean_object* v_fst_2110_; lean_object* v_snd_2111_; lean_object* v___x_2112_; lean_object* v_cache_2113_; lean_object* v_zetaDeltaFVarIds_2114_; lean_object* v_postponed_2115_; lean_object* v_diag_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2125_; 
v___x_2107_ = lean_st_ref_get(v___y_2103_);
v_mctx_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc_ref(v_mctx_2108_);
lean_dec(v___x_2107_);
v___x_2109_ = l_Lean_instantiateMVarsCore(v_mctx_2108_, v_e_2102_);
v_fst_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_fst_2110_);
v_snd_2111_ = lean_ctor_get(v___x_2109_, 1);
lean_inc(v_snd_2111_);
lean_dec_ref(v___x_2109_);
v___x_2112_ = lean_st_ref_take(v___y_2103_);
v_cache_2113_ = lean_ctor_get(v___x_2112_, 1);
v_zetaDeltaFVarIds_2114_ = lean_ctor_get(v___x_2112_, 2);
v_postponed_2115_ = lean_ctor_get(v___x_2112_, 3);
v_diag_2116_ = lean_ctor_get(v___x_2112_, 4);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v___x_2112_, 0);
lean_dec(v_unused_2126_);
v___x_2118_ = v___x_2112_;
v_isShared_2119_ = v_isSharedCheck_2125_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_diag_2116_);
lean_inc(v_postponed_2115_);
lean_inc(v_zetaDeltaFVarIds_2114_);
lean_inc(v_cache_2113_);
lean_dec(v___x_2112_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2125_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v_snd_2111_);
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_snd_2111_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_cache_2113_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_zetaDeltaFVarIds_2114_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_postponed_2115_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_diag_2116_);
v___x_2121_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_st_ref_put(v___y_2103_, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_fst_2110_);
return v___x_2123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg___boxed(lean_object* v_e_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_e_2127_, v___y_2128_);
lean_dec(v___y_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(lean_object* v_e_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_e_2131_, v___y_2133_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___boxed(lean_object* v_e_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(v_e_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__0(lean_object* v_x_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0));
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__0___boxed(lean_object* v_x_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__0(v_x_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v_x_2158_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__1(lean_object* v_x_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0));
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__1___boxed(lean_object* v_x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__1(v_x_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v_x_2181_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__2(lean_object* v_e_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v_e_2191_);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__2___boxed(lean_object* v_e_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__2(v_e_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__3(lean_object* v_x_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__3___boxed(lean_object* v_x_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__3(v_x_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v_x_2223_);
return v_res_2232_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__5(void){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2239_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__5, &l_Lean_Meta_AC_rewriteUnnormalized___closed__5_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__5);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__7(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_unsigned_to_nat(0u);
v___x_2243_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__6, &l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6);
v___x_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v___x_2242_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__8(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_unsigned_to_nat(32u);
v___x_2246_ = lean_mk_empty_array_with_capacity(v___x_2245_);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
return v___x_2247_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__9(void){
_start:
{
size_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2248_ = ((size_t)5ULL);
v___x_2249_ = lean_unsigned_to_nat(0u);
v___x_2250_ = lean_unsigned_to_nat(32u);
v___x_2251_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___x_2252_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__8, &l_Lean_Meta_AC_rewriteUnnormalized___closed__8_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__8);
v___x_2253_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
lean_ctor_set(v___x_2253_, 1, v___x_2251_);
lean_ctor_set(v___x_2253_, 2, v___x_2249_);
lean_ctor_set(v___x_2253_, 3, v___x_2249_);
lean_ctor_set_usize(v___x_2253_, 4, v___x_2248_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__10(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__9, &l_Lean_Meta_AC_rewriteUnnormalized___closed__9_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__9);
v___x_2255_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__6, &l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6);
v___x_2256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
lean_ctor_set(v___x_2256_, 2, v___x_2255_);
lean_ctor_set(v___x_2256_, 3, v___x_2254_);
return v___x_2256_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__10, &l_Lean_Meta_AC_rewriteUnnormalized___closed__10_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__10);
v___x_2258_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__7, &l_Lean_Meta_AC_rewriteUnnormalized___closed__7_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__7);
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set(v___x_2259_, 1, v___x_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized(lean_object* v_mvarId_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_2272_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2276_ = l_Lean_Meta_Simp_neutralConfig;
v___x_2277_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__0));
v___x_2278_ = l_Lean_Options_empty;
v___x_2279_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2276_, v___x_2277_, v_a_2275_, v___x_2278_, v_a_2269_, v_a_2271_, v_a_2272_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
lean_inc(v_mvarId_2268_);
v___x_2281_ = l_Lean_MVarId_getType(v_mvarId_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; lean_object* v_a_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_a_2282_, v_a_2270_);
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc_n(v_a_2284_, 2);
lean_dec_ref(v___x_2283_);
v___x_2285_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__11, &l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11);
v___x_2286_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__13));
v___x_2287_ = l_Lean_Meta_Simp_main(v_a_2284_, v_a_2280_, v___x_2285_, v___x_2286_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v_fst_2289_; lean_object* v___x_2290_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v_fst_2289_ = lean_ctor_get(v_a_2288_, 0);
lean_inc(v_fst_2289_);
lean_dec(v_a_2288_);
v___x_2290_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_2268_, v_a_2284_, v_fst_2289_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
lean_dec(v_a_2284_);
return v___x_2290_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_a_2284_);
lean_dec(v_mvarId_2268_);
v_a_2291_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2287_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2287_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_a_2280_);
lean_dec(v_mvarId_2268_);
v_a_2299_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2281_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2281_);
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
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_mvarId_2268_);
v_a_2307_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2279_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2279_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_mvarId_2268_);
v_a_2315_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2274_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2274_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___boxed(lean_object* v_mvarId_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Meta_AC_rewriteUnnormalized(v_mvarId_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object* v_goal_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Meta_AC_rewriteUnnormalized(v_goal_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = 1;
v___x_2339_ = l_Lean_MVarId_refl(v_a_2337_, v___x_2338_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
return v___x_2339_;
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v_a_2340_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2336_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2336_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl___boxed(lean_object* v_goal_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v_goal_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(lean_object* v_x_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
lean_inc(v___y_2359_);
lean_inc_ref(v___y_2358_);
lean_inc(v___y_2357_);
lean_inc_ref(v___y_2356_);
v___x_2365_ = lean_apply_9(v_x_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, lean_box(0));
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0___boxed(lean_object* v_x_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(v_x_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(lean_object* v_mvarId_2377_, lean_object* v_x_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___f_2388_; lean_object* v___x_2389_; 
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
v___f_2388_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2388_, 0, v_x_2378_);
lean_closure_set(v___f_2388_, 1, v___y_2379_);
lean_closure_set(v___f_2388_, 2, v___y_2380_);
lean_closure_set(v___f_2388_, 3, v___y_2381_);
lean_closure_set(v___f_2388_, 4, v___y_2382_);
v___x_2389_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2377_, v___f_2388_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2389_) == 0)
{
return v___x_2389_;
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___boxed(lean_object* v_mvarId_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_mvarId_2398_, v_x_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(lean_object* v_00_u03b1_2410_, lean_object* v_mvarId_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_mvarId_2411_, v_x_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_mvarId_2424_, lean_object* v_x_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(v_00_u03b1_2423_, v_mvarId_2424_, v_x_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___lam__0(lean_object* v_a_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v_a_2436_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___lam__0___boxed(lean_object* v_a_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Meta_AC_acRflTactic___redArg___lam__0(v_a_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg(lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_2459_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___f_2469_; lean_object* v___x_2470_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_n(v_a_2468_, 2);
lean_dec_ref_known(v___x_2467_, 1);
v___f_2469_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acRflTactic___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2469_, 0, v_a_2468_);
v___x_2470_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_a_2468_, v___f_2469_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
return v___x_2470_;
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
v_a_2471_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2467_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2467_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___boxed(lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Meta_AC_acRflTactic___redArg(v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic(lean_object* v_x_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Meta_AC_acRflTactic___redArg(v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___boxed(lean_object* v_x_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Meta_AC_acRflTactic(v_x_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_x_2500_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1(){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2526_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3));
v___x_2528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5));
v___x_2529_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acRflTactic___boxed), 10, 0);
v___x_2530_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2526_, v___x_2527_, v___x_2528_, v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___boxed(lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3(){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5));
v___x_2560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6));
v___x_2561_ = l_Lean_addBuiltinDeclarationRanges(v___x_2559_, v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___boxed(lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(lean_object* v_mvarId_2564_, lean_object* v_x_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2564_, v_x_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
v_a_2580_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2571_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2571_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg___boxed(lean_object* v_mvarId_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_mvarId_2588_, v_x_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(lean_object* v_00_u03b1_2596_, lean_object* v_mvarId_2597_, lean_object* v_x_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_mvarId_2597_, v_x_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___boxed(lean_object* v_00_u03b1_2605_, lean_object* v_mvarId_2606_, lean_object* v_x_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(v_00_u03b1_2605_, v_mvarId_2606_, v_x_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___lam__4(lean_object* v_fvarId_2614_, lean_object* v___f_2615_, lean_object* v___f_2616_, lean_object* v___f_2617_, lean_object* v___f_2618_, lean_object* v_goal_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2623_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = l_Lean_Meta_Simp_neutralConfig;
v___x_2628_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__0));
v___x_2629_ = l_Lean_Options_empty;
v___x_2630_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2627_, v___x_2628_, v_a_2626_, v___x_2629_, v___y_2620_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2632_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
lean_inc(v_fvarId_2614_);
v___x_2632_ = l_Lean_FVarId_getType___redArg(v_fvarId_2614_, v___y_2620_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2634_; lean_object* v_a_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_a_2633_, v___y_2621_);
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref(v___x_2634_);
v___x_2636_ = lean_unsigned_to_nat(32u);
v___x_2637_ = lean_mk_empty_array_with_capacity(v___x_2636_);
lean_dec_ref(v___x_2637_);
v___x_2638_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__11, &l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11);
v___x_2639_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__12));
v___x_2640_ = 1;
v___x_2641_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2641_, 0, v___f_2615_);
lean_ctor_set(v___x_2641_, 1, v___x_2639_);
lean_ctor_set(v___x_2641_, 2, v___f_2616_);
lean_ctor_set(v___x_2641_, 3, v___f_2617_);
lean_ctor_set(v___x_2641_, 4, v___f_2618_);
lean_ctor_set_uint8(v___x_2641_, sizeof(void*)*5, v___x_2640_);
v___x_2642_ = l_Lean_Meta_Simp_main(v_a_2635_, v_a_2631_, v___x_2638_, v___x_2641_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v_fst_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v_fst_2644_ = lean_ctor_get(v_a_2643_, 0);
lean_inc(v_fst_2644_);
lean_dec(v_a_2643_);
v___x_2645_ = 0;
v___x_2646_ = l_Lean_Meta_applySimpResultToLocalDecl(v_goal_2619_, v_fvarId_2614_, v_fst_2644_, v___x_2645_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2667_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2649_ = v___x_2646_;
v_isShared_2650_ = v_isSharedCheck_2667_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2646_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2667_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
if (lean_obj_tag(v_a_2647_) == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2651_ = lean_box(0);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2651_);
v___x_2653_ = v___x_2649_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
else
{
lean_object* v_val_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2666_; 
v_val_2655_ = lean_ctor_get(v_a_2647_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_a_2647_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2657_ = v_a_2647_;
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_val_2655_);
lean_dec(v_a_2647_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_snd_2659_; lean_object* v___x_2661_; 
v_snd_2659_ = lean_ctor_get(v_val_2655_, 1);
lean_inc(v_snd_2659_);
lean_dec(v_val_2655_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v_snd_2659_);
v___x_2661_ = v___x_2657_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_snd_2659_);
v___x_2661_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2663_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2661_);
v___x_2663_ = v___x_2649_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_a_2668_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2646_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2646_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_goal_2619_);
lean_dec(v_fvarId_2614_);
v_a_2676_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2642_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2642_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_a_2631_);
lean_dec(v_goal_2619_);
lean_dec_ref(v___f_2618_);
lean_dec_ref(v___f_2617_);
lean_dec_ref(v___f_2616_);
lean_dec_ref(v___f_2615_);
lean_dec(v_fvarId_2614_);
v_a_2684_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2632_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2632_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_goal_2619_);
lean_dec_ref(v___f_2618_);
lean_dec_ref(v___f_2617_);
lean_dec_ref(v___f_2616_);
lean_dec_ref(v___f_2615_);
lean_dec(v_fvarId_2614_);
v_a_2692_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2630_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2630_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_goal_2619_);
lean_dec_ref(v___f_2618_);
lean_dec_ref(v___f_2617_);
lean_dec_ref(v___f_2616_);
lean_dec_ref(v___f_2615_);
lean_dec(v_fvarId_2614_);
v_a_2700_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2625_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2625_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___lam__4___boxed(lean_object* v_fvarId_2708_, lean_object* v___f_2709_, lean_object* v___f_2710_, lean_object* v___f_2711_, lean_object* v___f_2712_, lean_object* v_goal_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Meta_AC_acNfHypMeta___lam__4(v_fvarId_2708_, v___f_2709_, v___f_2710_, v___f_2711_, v___f_2712_, v_goal_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta(lean_object* v_goal_2720_, lean_object* v_fvarId_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v___f_2727_; lean_object* v___f_2728_; lean_object* v___f_2729_; lean_object* v___f_2730_; lean_object* v___f_2731_; lean_object* v___x_2732_; 
v___f_2727_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__4));
v___f_2728_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__3));
v___f_2729_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__2));
v___f_2730_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__1));
lean_inc(v_goal_2720_);
v___f_2731_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acNfHypMeta___lam__4___boxed), 11, 6);
lean_closure_set(v___f_2731_, 0, v_fvarId_2721_);
lean_closure_set(v___f_2731_, 1, v___f_2730_);
lean_closure_set(v___f_2731_, 2, v___f_2729_);
lean_closure_set(v___f_2731_, 3, v___f_2728_);
lean_closure_set(v___f_2731_, 4, v___f_2727_);
lean_closure_set(v___f_2731_, 5, v_goal_2720_);
v___x_2732_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_goal_2720_, v___f_2731_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___boxed(lean_object* v_goal_2733_, lean_object* v_fvarId_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_Meta_AC_acNfHypMeta(v_goal_2733_, v_fvarId_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___lam__0(lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2742_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = l_Lean_Meta_AC_rewriteUnnormalized(v_a_2751_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = lean_box(0);
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2755_, v___y_2742_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
return v___x_2756_;
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_a_2757_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2752_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2752_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2750_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2750_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___lam__0___boxed(lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_Meta_AC_acNfTargetTactic___lam__0(v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic(lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___f_2793_; lean_object* v___x_2794_; 
v___f_2793_ = ((lean_object*)(l_Lean_Meta_AC_acNfTargetTactic___closed__0));
v___x_2794_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2793_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___boxed(lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_Meta_AC_acNfTargetTactic(v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___lam__0(lean_object* v_fvarId_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2807_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2817_ = l_Lean_Meta_AC_acNfHypMeta(v_a_2816_, v_fvarId_2805_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
if (lean_obj_tag(v_a_2818_) == 1)
{
lean_object* v_val_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_val_2819_ = lean_ctor_get(v_a_2818_, 0);
lean_inc(v_val_2819_);
lean_dec_ref_known(v_a_2818_, 1);
v___x_2820_ = lean_box(0);
v___x_2821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_val_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2821_, v___y_2807_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2822_;
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec(v_a_2818_);
v___x_2823_ = lean_box(0);
v___x_2824_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2823_, v___y_2807_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2824_;
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_a_2825_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2817_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2817_);
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
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_fvarId_2805_);
v_a_2833_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2815_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2815_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___lam__0___boxed(lean_object* v_fvarId_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_Meta_AC_acNfHypTactic___lam__0(v_fvarId_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic(lean_object* v_fvarId_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___f_2862_; lean_object* v___x_2863_; 
v___f_2862_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acNfHypTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2862_, 0, v_fvarId_2852_);
v___x_2863_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2862_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___boxed(lean_object* v_fvarId_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Meta_AC_acNfHypTactic(v_fvarId_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
return v_res_2874_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_box(0);
v___x_2876_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v___x_2875_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg(){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0);
v___x_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___boxed(lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(lean_object* v_00_u03b1_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___boxed(lean_object* v_00_u03b1_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(v_00_u03b1_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(lean_object* v_as_2905_, size_t v_i_2906_, size_t v_stop_2907_, lean_object* v_b_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
uint8_t v___x_2918_; 
v___x_2918_ = lean_usize_dec_eq(v_i_2906_, v_stop_2907_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_array_uget_borrowed(v_as_2905_, v_i_2906_);
lean_inc(v___x_2919_);
v___x_2920_ = l_Lean_Meta_AC_acNfHypTactic(v___x_2919_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; size_t v___x_2922_; size_t v___x_2923_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = ((size_t)1ULL);
v___x_2923_ = lean_usize_add(v_i_2906_, v___x_2922_);
v_i_2906_ = v___x_2923_;
v_b_2908_ = v_a_2921_;
goto _start;
}
else
{
return v___x_2920_;
}
}
else
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_b_2908_);
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1___boxed(lean_object* v_as_2926_, lean_object* v_i_2927_, lean_object* v_stop_2928_, lean_object* v_b_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
size_t v_i_boxed_2939_; size_t v_stop_boxed_2940_; lean_object* v_res_2941_; 
v_i_boxed_2939_ = lean_unbox_usize(v_i_2927_);
lean_dec(v_i_2927_);
v_stop_boxed_2940_ = lean_unbox_usize(v_stop_2928_);
lean_dec(v_stop_2928_);
v_res_2941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_as_2926_, v_i_boxed_2939_, v_stop_boxed_2940_, v_b_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec_ref(v_as_2926_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___lam__0(lean_object* v___y_2942_, lean_object* v___x_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
if (lean_obj_tag(v___y_2942_) == 0)
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_Meta_AC_acNfTargetTactic(v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v___x_2954_; 
lean_dec_ref_known(v___x_2953_, 1);
v___x_2954_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2945_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2956_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
v___x_2956_ = l_Lean_MVarId_getNondepPropHyps(v_a_2955_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2977_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2977_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2977_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2961_ = lean_array_get_size(v_a_2957_);
v___x_2962_ = lean_box(0);
v___x_2963_ = lean_nat_dec_lt(v___x_2943_, v___x_2961_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2965_; 
lean_dec(v_a_2957_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2962_);
v___x_2965_ = v___x_2959_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2962_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
else
{
uint8_t v___x_2967_; 
v___x_2967_ = lean_nat_dec_le(v___x_2961_, v___x_2961_);
if (v___x_2967_ == 0)
{
if (v___x_2963_ == 0)
{
lean_object* v___x_2969_; 
lean_dec(v_a_2957_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2962_);
v___x_2969_ = v___x_2959_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2962_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
else
{
size_t v___x_2971_; size_t v___x_2972_; lean_object* v___x_2973_; 
lean_del_object(v___x_2959_);
v___x_2971_ = ((size_t)0ULL);
v___x_2972_ = lean_usize_of_nat(v___x_2961_);
v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_2957_, v___x_2971_, v___x_2972_, v___x_2962_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v_a_2957_);
return v___x_2973_;
}
}
else
{
size_t v___x_2974_; size_t v___x_2975_; lean_object* v___x_2976_; 
lean_del_object(v___x_2959_);
v___x_2974_ = ((size_t)0ULL);
v___x_2975_ = lean_usize_of_nat(v___x_2961_);
v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_2957_, v___x_2974_, v___x_2975_, v___x_2962_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v_a_2957_);
return v___x_2976_;
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
v_a_2978_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2956_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2956_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
v_a_2986_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2954_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2954_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
return v___x_2953_;
}
}
else
{
lean_object* v_hypotheses_2994_; uint8_t v_type_2995_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; 
v_hypotheses_2994_ = lean_ctor_get(v___y_2942_, 0);
lean_inc_ref(v_hypotheses_2994_);
v_type_2995_ = lean_ctor_get_uint8(v___y_2942_, sizeof(void*)*1);
lean_dec_ref_known(v___y_2942_, 1);
if (v_type_2995_ == 0)
{
v___y_2997_ = v___y_2944_;
v___y_2998_ = v___y_2945_;
v___y_2999_ = v___y_2946_;
v___y_3000_ = v___y_2947_;
v___y_3001_ = v___y_2948_;
v___y_3002_ = v___y_2949_;
v___y_3003_ = v___y_2950_;
v___y_3004_ = v___y_2951_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Meta_AC_acNfTargetTactic(v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_dec_ref_known(v___x_3035_, 1);
v___y_2997_ = v___y_2944_;
v___y_2998_ = v___y_2945_;
v___y_2999_ = v___y_2946_;
v___y_3000_ = v___y_2947_;
v___y_3001_ = v___y_2948_;
v___y_3002_ = v___y_2949_;
v___y_3003_ = v___y_2950_;
v___y_3004_ = v___y_2951_;
goto v___jp_2996_;
}
else
{
lean_dec_ref(v_hypotheses_2994_);
return v___x_3035_;
}
}
v___jp_2996_:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_2994_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3026_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3026_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3026_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3010_ = lean_array_get_size(v_a_3006_);
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_nat_dec_lt(v___x_2943_, v___x_3010_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_a_3006_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v___x_3011_);
v___x_3014_ = v___x_3008_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3011_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
else
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_nat_dec_le(v___x_3010_, v___x_3010_);
if (v___x_3016_ == 0)
{
if (v___x_3012_ == 0)
{
lean_object* v___x_3018_; 
lean_dec(v_a_3006_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v___x_3011_);
v___x_3018_ = v___x_3008_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3011_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
else
{
size_t v___x_3020_; size_t v___x_3021_; lean_object* v___x_3022_; 
lean_del_object(v___x_3008_);
v___x_3020_ = ((size_t)0ULL);
v___x_3021_ = lean_usize_of_nat(v___x_3010_);
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3006_, v___x_3020_, v___x_3021_, v___x_3011_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v_a_3006_);
return v___x_3022_;
}
}
else
{
size_t v___x_3023_; size_t v___x_3024_; lean_object* v___x_3025_; 
lean_del_object(v___x_3008_);
v___x_3023_ = ((size_t)0ULL);
v___x_3024_ = lean_usize_of_nat(v___x_3010_);
v___x_3025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3006_, v___x_3023_, v___x_3024_, v___x_3011_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v_a_3006_);
return v___x_3025_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
v_a_3027_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3005_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3005_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___lam__0___boxed(lean_object* v___y_3036_, lean_object* v___x_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_Meta_AC_evalNf0___lam__0(v___y_3036_, v___x_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___x_3037_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0(lean_object* v_stx_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___closed__1));
lean_inc(v_stx_3056_);
v___x_3067_ = l_Lean_Syntax_isOfKind(v_stx_3056_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; 
lean_dec(v_stx_3056_);
v___x_3068_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___x_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3082_ = lean_unsigned_to_nat(1u);
v___x_3083_ = l_Lean_Syntax_getArg(v_stx_3056_, v___x_3082_);
lean_dec(v_stx_3056_);
v___x_3084_ = l_Lean_Syntax_isNone(v___x_3083_);
if (v___x_3084_ == 0)
{
uint8_t v___x_3085_; 
lean_inc(v___x_3083_);
v___x_3085_ = l_Lean_Syntax_matchesNull(v___x_3083_, v___x_3082_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
lean_dec(v___x_3083_);
v___x_3086_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v___x_3086_;
}
else
{
lean_object* v_loc_x3f_3087_; lean_object* v___x_3088_; 
v_loc_x3f_3087_ = l_Lean_Syntax_getArg(v___x_3083_, v___x_3069_);
lean_dec(v___x_3083_);
v___x_3088_ = l_Lean_Elab_Tactic_expandLocation(v_loc_x3f_3087_);
lean_dec(v_loc_x3f_3087_);
v___y_3071_ = v_a_3062_;
v___y_3072_ = v_a_3058_;
v___y_3073_ = v_a_3057_;
v___y_3074_ = v_a_3064_;
v___y_3075_ = v_a_3059_;
v___y_3076_ = v_a_3060_;
v___y_3077_ = v_a_3061_;
v___y_3078_ = v_a_3063_;
v___y_3079_ = v___x_3088_;
goto v___jp_3070_;
}
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
lean_dec(v___x_3083_);
v___x_3089_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___closed__2));
v___x_3090_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*1, v___x_3067_);
v___y_3071_ = v_a_3062_;
v___y_3072_ = v_a_3058_;
v___y_3073_ = v_a_3057_;
v___y_3074_ = v_a_3064_;
v___y_3075_ = v_a_3059_;
v___y_3076_ = v_a_3060_;
v___y_3077_ = v_a_3061_;
v___y_3078_ = v_a_3063_;
v___y_3079_ = v___x_3090_;
goto v___jp_3070_;
}
v___jp_3070_:
{
lean_object* v___y_3080_; lean_object* v___x_3081_; 
v___y_3080_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_evalNf0___lam__0___boxed), 11, 2);
lean_closure_set(v___y_3080_, 0, v___y_3079_);
lean_closure_set(v___y_3080_, 1, v___x_3069_);
v___x_3081_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_3080_, v___y_3073_, v___y_3072_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3071_, v___y_3078_, v___y_3074_);
return v___x_3081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___boxed(lean_object* v_stx_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_Meta_AC_evalNf0(v_stx_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1(){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3109_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3110_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___closed__1));
v___x_3111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1));
v___x_3112_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_evalNf0___boxed), 10, 0);
v___x_3113_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3109_, v___x_3110_, v___x_3111_, v___x_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___boxed(lean_object* v_a_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
return v_res_3115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_unsigned_to_nat(4236260923u);
v___x_3172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_));
v___x_3173_ = l_Lean_Name_num___override(v___x_3172_, v___x_3171_);
return v___x_3173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_));
v___x_3176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3177_ = l_Lean_Name_str___override(v___x_3176_, v___x_3175_);
return v___x_3177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_));
v___x_3180_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3181_ = l_Lean_Name_str___override(v___x_3180_, v___x_3179_);
return v___x_3181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = lean_unsigned_to_nat(2u);
v___x_3183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3184_ = l_Lean_Name_num___override(v___x_3183_, v___x_3182_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3186_; uint8_t v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3186_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__2));
v___x_3187_ = 0;
v___x_3188_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3189_ = l_Lean_registerTraceClass(v___x_3186_, v___x_3187_, v___x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2____boxed(lean_object* v_a_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_();
return v_res_3191_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
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
