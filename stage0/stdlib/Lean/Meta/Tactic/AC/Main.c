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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_AC_mergeIdem(lean_object*);
lean_object* l_Lean_Data_AC_Expr_toList(lean_object*);
lean_object* l_Lean_Data_AC_sort(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx___impl___boxed(lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_AC_rewriteUnnormalized___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_rewriteUnnormalized___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__0 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__0_value;
static const lean_closure_object l_Lean_Meta_AC_rewriteUnnormalized___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_rewriteUnnormalized___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__1 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__1_value;
static const lean_closure_object l_Lean_Meta_AC_rewriteUnnormalized___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_rewriteUnnormalized___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__2 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__2_value;
static const lean_closure_object l_Lean_Meta_AC_rewriteUnnormalized___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AC_rewriteUnnormalized___lam__3___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AC_rewriteUnnormalized___closed__3 = (const lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__3_value;
static const lean_array_object l_Lean_Meta_AC_rewriteUnnormalized___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
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
static const lean_ctor_object l_Lean_Meta_AC_rewriteUnnormalized___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 8, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__0_value),((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__12_value),((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__1_value),((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__2_value),((lean_object*)&l_Lean_Meta_AC_rewriteUnnormalized___closed__3_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
uint8_t l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0(lean_object* v_ctx_13_){
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
LEAN_EXPORT void l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_13_ = stack[0].m_obj;
uint8_t v_res_18_;
v_res_18_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0(v_ctx_13_);
stack->m_num = v_res_18_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0___boxed(lean_object* v_ctx_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0(v_ctx_19_);
lean_dec_ref(v_ctx_19_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
uint8_t l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1(lean_object* v_ctx_22_){
_start:
{
lean_object* v_fst_23_; lean_object* v_idem_24_; 
v_fst_23_ = lean_ctor_get(v_ctx_22_, 0);
v_idem_24_ = lean_ctor_get(v_fst_23_, 4);
if (lean_obj_tag(v_idem_24_) == 0)
{
uint8_t v___x_25_; 
v___x_25_ = 0;
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = 1;
return v___x_26_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_22_ = stack[0].m_obj;
uint8_t v_res_27_;
v_res_27_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1(v_ctx_22_);
stack->m_num = v_res_27_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1___boxed(lean_object* v_ctx_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1(v_ctx_28_);
lean_dec_ref(v_ctx_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
uint8_t l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2(uint8_t v___x_31_, lean_object* v_ctx_32_, lean_object* v_x_33_){
_start:
{
lean_object* v_snd_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_snd_34_ = lean_ctor_get(v_ctx_32_, 1);
v___x_35_ = lean_box(v___x_31_);
v___x_36_ = lean_array_get(v___x_35_, v_snd_34_, v_x_33_);
lean_dec(v___x_35_);
v___x_37_ = lean_unbox(v___x_36_);
lean_dec(v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_31_ = stack[0].m_num;
lean_object* v_ctx_32_ = stack[1].m_obj;
lean_object* v_x_33_ = stack[2].m_obj;
uint8_t v_res_38_;
v_res_38_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2(v___x_31_, v_ctx_32_, v_x_33_);
stack->m_num = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2___boxed(lean_object* v___x_39_, lean_object* v_ctx_40_, lean_object* v_x_41_){
_start:
{
uint8_t v___x_58__boxed_42_; uint8_t v_res_43_; lean_object* v_r_44_; 
v___x_58__boxed_42_ = lean_unbox(v___x_39_);
v_res_43_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2(v___x_58__boxed_42_, v_ctx_40_, v_x_41_);
lean_dec(v_x_41_);
lean_dec_ref(v_ctx_40_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0(lean_object* v_x_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = ((lean_object*)(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0));
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___boxed(lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0(v_x_59_);
lean_dec_ref(v_x_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1(lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_64_, 0, v___y_62_);
lean_ctor_set(v___x_64_, 1, v___y_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1___boxed(lean_object* v_x_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1(v_x_65_, v___y_66_, v___y_67_);
lean_dec_ref(v_x_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v_x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2___boxed(lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2(v_x_72_, v_x_73_);
lean_dec_ref(v_x_72_);
return v_res_74_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(lean_object* v_msgData_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_env_90_; uint8_t v___x_91_; lean_object* v_env_92_; lean_object* v___x_93_; lean_object* v_toCold_94_; lean_object* v_mctx_95_; lean_object* v_lctx_96_; lean_object* v_options_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_89_ = lean_st_ref_get(v___y_87_);
v_env_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_env_90_);
lean_dec(v___x_89_);
v___x_91_ = 0;
v_env_92_ = l_Lean_Environment_setRecordingDeps(v_env_90_, v___x_91_);
v___x_93_ = lean_st_ref_get(v___y_85_);
v_toCold_94_ = lean_ctor_get(v___y_86_, 0);
v_mctx_95_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_mctx_95_);
lean_dec(v___x_93_);
v_lctx_96_ = lean_ctor_get(v___y_84_, 2);
v_options_97_ = lean_ctor_get(v_toCold_94_, 2);
lean_inc_ref(v_options_97_);
lean_inc_ref(v_lctx_96_);
v___x_98_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_98_, 0, v_env_92_);
lean_ctor_set(v___x_98_, 1, v_mctx_95_);
lean_ctor_set(v___x_98_, 2, v_lctx_96_);
lean_ctor_set(v___x_98_, 3, v_options_97_);
v___x_99_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_msgData_83_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_83_ = stack[0].m_obj;
lean_object* v___y_84_ = stack[1].m_obj;
lean_object* v___y_85_ = stack[2].m_obj;
lean_object* v___y_86_ = stack[3].m_obj;
lean_object* v___y_87_ = stack[4].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(v_msgData_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0___boxed(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(v_msgData_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_108_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0(void){
_start:
{
lean_object* v___x_109_; double v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_float_of_nat(v___x_109_);
return v___x_110_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(lean_object* v_cls_114_, lean_object* v_msg_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_ref_121_; lean_object* v___x_122_; lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_168_; 
v_ref_121_ = lean_ctor_get(v___y_118_, 2);
v___x_122_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(v_msg_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_168_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_168_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_168_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v_traceState_128_; lean_object* v_env_129_; lean_object* v_nextMacroScope_130_; lean_object* v_ngen_131_; lean_object* v_auxDeclNGen_132_; lean_object* v_cache_133_; lean_object* v_recordedDeps_134_; lean_object* v_messages_135_; lean_object* v_infoState_136_; lean_object* v_snapshotTasks_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_167_; 
v___x_127_ = lean_st_ref_take(v___y_119_);
v_traceState_128_ = lean_ctor_get(v___x_127_, 4);
v_env_129_ = lean_ctor_get(v___x_127_, 0);
v_nextMacroScope_130_ = lean_ctor_get(v___x_127_, 1);
v_ngen_131_ = lean_ctor_get(v___x_127_, 2);
v_auxDeclNGen_132_ = lean_ctor_get(v___x_127_, 3);
v_cache_133_ = lean_ctor_get(v___x_127_, 5);
v_recordedDeps_134_ = lean_ctor_get(v___x_127_, 6);
v_messages_135_ = lean_ctor_get(v___x_127_, 7);
v_infoState_136_ = lean_ctor_get(v___x_127_, 8);
v_snapshotTasks_137_ = lean_ctor_get(v___x_127_, 9);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_167_ == 0)
{
v___x_139_ = v___x_127_;
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snapshotTasks_137_);
lean_inc(v_infoState_136_);
lean_inc(v_messages_135_);
lean_inc(v_recordedDeps_134_);
lean_inc(v_cache_133_);
lean_inc(v_traceState_128_);
lean_inc(v_auxDeclNGen_132_);
lean_inc(v_ngen_131_);
lean_inc(v_nextMacroScope_130_);
lean_inc(v_env_129_);
lean_dec(v___x_127_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint64_t v_tid_141_; lean_object* v_traces_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_166_; 
v_tid_141_ = lean_ctor_get_uint64(v_traceState_128_, sizeof(void*)*1);
v_traces_142_ = lean_ctor_get(v_traceState_128_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_traceState_128_);
if (v_isSharedCheck_166_ == 0)
{
v___x_144_ = v_traceState_128_;
v_isShared_145_ = v_isSharedCheck_166_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_traces_142_);
lean_dec(v_traceState_128_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_166_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; double v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_box(0);
v___x_148_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0);
v___x_149_ = 0;
v___x_150_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__1));
v___x_151_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_151_, 0, v_cls_114_);
lean_ctor_set(v___x_151_, 1, v___x_147_);
lean_ctor_set(v___x_151_, 2, v___x_150_);
lean_ctor_set_float(v___x_151_, sizeof(void*)*3, v___x_148_);
lean_ctor_set_float(v___x_151_, sizeof(void*)*3 + 8, v___x_148_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*3 + 16, v___x_149_);
v___x_152_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__2));
v___x_153_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set(v___x_153_, 1, v_a_123_);
lean_ctor_set(v___x_153_, 2, v___x_152_);
lean_inc(v_ref_121_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_ref_121_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = l_Lean_PersistentArray_push___redArg(v_traces_142_, v___x_154_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_155_);
v___x_157_ = v___x_144_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_155_);
lean_ctor_set_uint64(v_reuseFailAlloc_165_, sizeof(void*)*1, v_tid_141_);
v___x_157_ = v_reuseFailAlloc_165_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_159_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 4, v___x_157_);
v___x_159_ = v___x_139_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_env_129_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_nextMacroScope_130_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_ngen_131_);
lean_ctor_set(v_reuseFailAlloc_164_, 3, v_auxDeclNGen_132_);
lean_ctor_set(v_reuseFailAlloc_164_, 4, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_164_, 5, v_cache_133_);
lean_ctor_set(v_reuseFailAlloc_164_, 6, v_recordedDeps_134_);
lean_ctor_set(v_reuseFailAlloc_164_, 7, v_messages_135_);
lean_ctor_set(v_reuseFailAlloc_164_, 8, v_infoState_136_);
lean_ctor_set(v_reuseFailAlloc_164_, 9, v_snapshotTasks_137_);
v___x_159_ = v_reuseFailAlloc_164_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_st_ref_put(v___y_119_, v___x_159_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_146_);
v___x_162_ = v___x_125_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_146_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_114_ = stack[0].m_obj;
lean_object* v_msg_115_ = stack[1].m_obj;
lean_object* v___y_116_ = stack[2].m_obj;
lean_object* v___y_117_ = stack[3].m_obj;
lean_object* v___y_118_ = stack[4].m_obj;
lean_object* v___y_119_ = stack[5].m_obj;
lean_object* v_res_169_;
v_res_169_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(v_cls_114_, v_msg_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___boxed(lean_object* v_cls_170_, lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(v_cls_170_, v_msg_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
static lean_object* _init_l_Lean_Meta_AC_getInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___lam__0___closed__2));
v___x_183_ = l_Lean_stringToMessageData(v___x_182_);
return v___x_183_;
}
}
lean_object* l_Lean_Meta_AC_getInstance___lam__0(lean_object* v_a_184_, lean_object* v___x_185_, lean_object* v_____r_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_box(0);
v___x_193_ = l_Lean_Meta_synthInstance(v_a_184_, v___x_192_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_221_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_221_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_221_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_221_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_toCold_204_; lean_object* v_options_205_; uint8_t v_hasTrace_206_; 
v_toCold_204_ = lean_ctor_get(v___y_189_, 0);
v_options_205_ = lean_ctor_get(v_toCold_204_, 2);
v_hasTrace_206_ = lean_ctor_get_uint8(v_options_205_, sizeof(void*)*1);
if (v_hasTrace_206_ == 0)
{
lean_dec(v___x_185_);
goto v___jp_198_;
}
else
{
lean_object* v_inheritedTraceOptions_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_inheritedTraceOptions_207_ = lean_ctor_get(v_toCold_204_, 11);
v___x_208_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___lam__0___closed__1));
lean_inc(v___x_185_);
v___x_209_ = l_Lean_Name_append(v___x_208_, v___x_185_);
v___x_210_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_207_, v_options_205_, v___x_209_);
lean_dec(v___x_209_);
if (v___x_210_ == 0)
{
lean_dec(v___x_185_);
goto v___jp_198_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_obj_once(&l_Lean_Meta_AC_getInstance___lam__0___closed__3, &l_Lean_Meta_AC_getInstance___lam__0___closed__3_once, _init_l_Lean_Meta_AC_getInstance___lam__0___closed__3);
v___x_212_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(v___x_185_, v___x_211_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_dec_ref_known(v___x_212_, 1);
goto v___jp_198_;
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_del_object(v___x_196_);
lean_dec(v_a_194_);
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
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
v___jp_198_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v_a_194_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_200_);
v___x_202_ = v___x_196_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec(v___x_185_);
v_a_222_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_193_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_193_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_getInstance___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_184_ = stack[0].m_obj;
lean_object* v___x_185_ = stack[1].m_obj;
lean_object* v_____r_186_ = stack[2].m_obj;
lean_object* v___y_187_ = stack[3].m_obj;
lean_object* v___y_188_ = stack[4].m_obj;
lean_object* v___y_189_ = stack[5].m_obj;
lean_object* v___y_190_ = stack[6].m_obj;
lean_object* v_res_230_;
v_res_230_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_184_, v___x_185_, v_____r_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___lam__0___boxed(lean_object* v_a_231_, lean_object* v___x_232_, lean_object* v_____r_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_231_, v___x_232_, v_____r_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_239_;
}
}
static lean_object* _init_l_Lean_Meta_AC_getInstance___closed__3(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__2));
v___x_246_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___lam__0___closed__1));
v___x_247_ = l_Lean_Name_append(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Meta_AC_getInstance___closed__5(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__4));
v___x_250_ = l_Lean_stringToMessageData(v___x_249_);
return v___x_250_;
}
}
lean_object* l_Lean_Meta_AC_getInstance(lean_object* v_cls_251_, lean_object* v_exprs_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v___y_259_; uint8_t v___y_260_; lean_object* v_a_265_; lean_object* v___y_269_; lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_mkAppM(v_cls_251_, v_exprs_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_toCold_281_; lean_object* v_options_282_; lean_object* v_a_283_; lean_object* v_inheritedTraceOptions_284_; uint8_t v_hasTrace_285_; lean_object* v___x_286_; 
v_toCold_281_ = lean_ctor_get(v_a_255_, 0);
v_options_282_ = lean_ctor_get(v_toCold_281_, 2);
v_a_283_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_280_, 1);
v_inheritedTraceOptions_284_ = lean_ctor_get(v_toCold_281_, 11);
v_hasTrace_285_ = lean_ctor_get_uint8(v_options_282_, sizeof(void*)*1);
v___x_286_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__2));
if (v_hasTrace_285_ == 0)
{
goto v___jp_287_;
}
else
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_obj_once(&l_Lean_Meta_AC_getInstance___closed__3, &l_Lean_Meta_AC_getInstance___closed__3_once, _init_l_Lean_Meta_AC_getInstance___closed__3);
v___x_291_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_284_, v_options_282_, v___x_290_);
if (v___x_291_ == 0)
{
goto v___jp_287_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_Lean_Meta_AC_getInstance___closed__5, &l_Lean_Meta_AC_getInstance___closed__5_once, _init_l_Lean_Meta_AC_getInstance___closed__5);
lean_inc(v_a_283_);
v___x_293_ = l_Lean_indentExpr(v_a_283_);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(v___x_286_, v___x_294_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_297_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_295_, 1);
v___x_297_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_283_, v___x_286_, v_a_296_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
v___y_269_ = v___x_297_;
goto v___jp_268_;
}
else
{
lean_object* v_a_298_; 
lean_dec(v_a_283_);
v_a_298_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_295_, 1);
v_a_265_ = v_a_298_;
goto v___jp_264_;
}
}
}
v___jp_287_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_box(0);
v___x_289_ = l_Lean_Meta_AC_getInstance___lam__0(v_a_283_, v___x_286_, v___x_288_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
v___y_269_ = v___x_289_;
goto v___jp_268_;
}
}
else
{
lean_object* v_a_299_; 
v_a_299_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_280_, 1);
v_a_265_ = v_a_299_;
goto v___jp_264_;
}
v___jp_258_:
{
if (v___y_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref(v___y_259_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; 
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v___y_259_);
return v___x_263_;
}
}
v___jp_264_:
{
uint8_t v___x_266_; 
v___x_266_ = l_Lean_Exception_isInterrupt(v_a_265_);
if (v___x_266_ == 0)
{
uint8_t v___x_267_; 
lean_inc_ref(v_a_265_);
v___x_267_ = l_Lean_Exception_isRuntime(v_a_265_);
v___y_259_ = v_a_265_;
v___y_260_ = v___x_267_;
goto v___jp_258_;
}
else
{
v___y_259_ = v_a_265_;
v___y_260_ = v___x_266_;
goto v___jp_258_;
}
}
v___jp_268_:
{
if (lean_obj_tag(v___y_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
v_a_270_ = lean_ctor_get(v___y_269_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___y_269_);
if (v_isSharedCheck_278_ == 0)
{
v___x_272_ = v___y_269_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___y_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_a_274_; lean_object* v___x_276_; 
v_a_274_ = lean_ctor_get(v_a_270_, 0);
lean_inc(v_a_274_);
lean_dec(v_a_270_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v_a_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_object* v_a_279_; 
v_a_279_ = lean_ctor_get(v___y_269_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___y_269_, 1);
v_a_265_ = v_a_279_;
goto v___jp_264_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_getInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_251_ = stack[0].m_obj;
lean_object* v_exprs_252_ = stack[1].m_obj;
lean_object* v_a_253_ = stack[2].m_obj;
lean_object* v_a_254_ = stack[3].m_obj;
lean_object* v_a_255_ = stack[4].m_obj;
lean_object* v_a_256_ = stack[5].m_obj;
lean_object* v_res_300_;
v_res_300_ = l_Lean_Meta_AC_getInstance(v_cls_251_, v_exprs_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_getInstance___boxed(lean_object* v_cls_301_, lean_object* v_exprs_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Meta_AC_getInstance(v_cls_301_, v_exprs_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
return v_res_308_;
}
}
lean_object* l_Lean_Meta_AC_preContext(lean_object* v_expr_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_328_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__2));
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_mk_empty_array_with_capacity(v___x_329_);
lean_inc_ref(v_expr_322_);
v___x_331_ = lean_array_push(v___x_330_, v_expr_322_);
lean_inc_ref(v___x_331_);
v___x_332_ = l_Lean_Meta_AC_getInstance(v___x_328_, v___x_331_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_380_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_380_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_380_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_380_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
if (lean_obj_tag(v_a_333_) == 1)
{
lean_object* v_val_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_375_; 
lean_del_object(v___x_335_);
v_val_337_ = lean_ctor_get(v_a_333_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_a_333_);
if (v_isSharedCheck_375_ == 0)
{
v___x_339_ = v_a_333_;
v_isShared_340_ = v_isSharedCheck_375_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_val_337_);
lean_dec(v_a_333_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_375_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__4));
lean_inc_ref(v___x_331_);
v___x_342_ = l_Lean_Meta_AC_getInstance(v___x_341_, v___x_331_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__6));
v___x_345_ = l_Lean_Meta_AC_getInstance(v___x_344_, v___x_331_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_358_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_358_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_358_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_358_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_expr_322_);
lean_ctor_set(v___x_351_, 2, v_val_337_);
lean_ctor_set(v___x_351_, 3, v_a_343_);
lean_ctor_set(v___x_351_, 4, v_a_346_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_351_);
v___x_353_ = v___x_339_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_353_);
v___x_355_ = v___x_348_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_a_343_);
lean_del_object(v___x_339_);
lean_dec(v_val_337_);
lean_dec_ref(v_expr_322_);
v_a_359_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_345_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_345_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
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
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_del_object(v___x_339_);
lean_dec(v_val_337_);
lean_dec_ref(v___x_331_);
lean_dec_ref(v_expr_322_);
v_a_367_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_342_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_342_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
else
{
lean_object* v___x_376_; lean_object* v___x_378_; 
lean_dec(v_a_333_);
lean_dec_ref(v___x_331_);
lean_dec_ref(v_expr_322_);
v___x_376_ = lean_box(0);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_376_);
v___x_378_ = v___x_335_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v___x_331_);
lean_dec_ref(v_expr_322_);
v_a_381_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_332_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_332_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_preContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_322_ = stack[0].m_obj;
lean_object* v_a_323_ = stack[1].m_obj;
lean_object* v_a_324_ = stack[2].m_obj;
lean_object* v_a_325_ = stack[3].m_obj;
lean_object* v_a_326_ = stack[4].m_obj;
lean_object* v_res_389_;
v_res_389_ = l_Lean_Meta_AC_preContext(v_expr_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_preContext___boxed(lean_object* v_expr_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Meta_AC_preContext(v_expr_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx___impl(lean_object* v_x_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = lean_obj_tag_nat(v_x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorIdx___impl___boxed(lean_object* v_x_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Meta_AC_PreExpr_ctorIdx___impl(v_x_399_);
lean_dec_ref(v_x_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim___redArg(lean_object* v_t_401_, lean_object* v_k_402_){
_start:
{
if (lean_obj_tag(v_t_401_) == 0)
{
lean_object* v_lhs_403_; lean_object* v_rhs_404_; lean_object* v___x_405_; 
v_lhs_403_ = lean_ctor_get(v_t_401_, 0);
lean_inc_ref(v_lhs_403_);
v_rhs_404_ = lean_ctor_get(v_t_401_, 1);
lean_inc_ref(v_rhs_404_);
lean_dec_ref_known(v_t_401_, 2);
v___x_405_ = lean_apply_2(v_k_402_, v_lhs_403_, v_rhs_404_);
return v___x_405_;
}
else
{
lean_object* v_e_406_; lean_object* v___x_407_; 
v_e_406_ = lean_ctor_get(v_t_401_, 0);
lean_inc_ref(v_e_406_);
lean_dec_ref_known(v_t_401_, 1);
v___x_407_ = lean_apply_1(v_k_402_, v_e_406_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim(lean_object* v_motive_408_, lean_object* v_ctorIdx_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_k_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_410_, v_k_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_ctorElim___boxed(lean_object* v_motive_414_, lean_object* v_ctorIdx_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_k_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Meta_AC_PreExpr_ctorElim(v_motive_414_, v_ctorIdx_415_, v_t_416_, v_h_417_, v_k_418_);
lean_dec(v_ctorIdx_415_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_op_elim___redArg(lean_object* v_t_420_, lean_object* v_op_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_420_, v_op_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_op_elim(lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_op_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_424_, v_op_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_var_elim___redArg(lean_object* v_t_428_, lean_object* v_var_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_428_, v_var_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_PreExpr_var_elim(lean_object* v_motive_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_var_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_432_, v_var_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_bin(lean_object* v_op_436_, lean_object* v_l_437_, lean_object* v_r_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = l_Lean_Expr_app___override(v_op_436_, v_l_437_);
v___x_440_ = l_Lean_Expr_app___override(v___x_439_, v_r_438_);
return v___x_440_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(lean_object* v_a_441_, lean_object* v_x_442_){
_start:
{
if (lean_obj_tag(v_x_442_) == 0)
{
uint8_t v___x_443_; 
v___x_443_ = 0;
return v___x_443_;
}
else
{
lean_object* v_key_444_; lean_object* v_tail_445_; uint8_t v___x_446_; 
v_key_444_ = lean_ctor_get(v_x_442_, 0);
v_tail_445_ = lean_ctor_get(v_x_442_, 2);
v___x_446_ = lean_expr_eqv(v_key_444_, v_a_441_);
if (v___x_446_ == 0)
{
v_x_442_ = v_tail_445_;
goto _start;
}
else
{
return v___x_446_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_441_ = stack[0].m_obj;
lean_object* v_x_442_ = stack[1].m_obj;
uint8_t v_res_448_;
v_res_448_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_441_, v_x_442_);
stack->m_num = v_res_448_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg___boxed(lean_object* v_a_449_, lean_object* v_x_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_449_, v_x_450_);
lean_dec(v_x_450_);
lean_dec_ref(v_a_449_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
return v_x_453_;
}
else
{
lean_object* v_key_455_; lean_object* v_value_456_; lean_object* v_tail_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_480_; 
v_key_455_ = lean_ctor_get(v_x_454_, 0);
v_value_456_ = lean_ctor_get(v_x_454_, 1);
v_tail_457_ = lean_ctor_get(v_x_454_, 2);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_454_);
if (v_isSharedCheck_480_ == 0)
{
v___x_459_ = v_x_454_;
v_isShared_460_ = v_isSharedCheck_480_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_tail_457_);
lean_inc(v_value_456_);
lean_inc(v_key_455_);
lean_dec(v_x_454_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_480_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; uint64_t v_fold_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; size_t v___x_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_461_ = lean_array_get_size(v_x_453_);
v___x_462_ = l_Lean_Expr_hash(v_key_455_);
v___x_463_ = 32ULL;
v___x_464_ = lean_uint64_shift_right(v___x_462_, v___x_463_);
v_fold_465_ = lean_uint64_xor(v___x_462_, v___x_464_);
v___x_466_ = 16ULL;
v___x_467_ = lean_uint64_shift_right(v_fold_465_, v___x_466_);
v___x_468_ = lean_uint64_xor(v_fold_465_, v___x_467_);
v___x_469_ = lean_uint64_to_usize(v___x_468_);
v___x_470_ = lean_usize_of_nat(v___x_461_);
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_sub(v___x_470_, v___x_471_);
v___x_473_ = lean_usize_land(v___x_469_, v___x_472_);
v___x_474_ = lean_array_uget_borrowed(v_x_453_, v___x_473_);
lean_inc(v___x_474_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 2, v___x_474_);
v___x_476_ = v___x_459_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_key_455_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_value_456_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v___x_474_);
v___x_476_ = v_reuseFailAlloc_479_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; 
v___x_477_ = lean_array_uset(v_x_453_, v___x_473_, v___x_476_);
v_x_453_ = v___x_477_;
v_x_454_ = v_tail_457_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_481_, lean_object* v_source_482_, lean_object* v_target_483_){
_start:
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_array_get_size(v_source_482_);
v___x_485_ = lean_nat_dec_lt(v_i_481_, v___x_484_);
if (v___x_485_ == 0)
{
lean_dec_ref(v_source_482_);
lean_dec(v_i_481_);
return v_target_483_;
}
else
{
lean_object* v_es_486_; lean_object* v___x_487_; lean_object* v_source_488_; lean_object* v_target_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_es_486_ = lean_array_fget(v_source_482_, v_i_481_);
v___x_487_ = lean_box(0);
v_source_488_ = lean_array_fset(v_source_482_, v_i_481_, v___x_487_);
v_target_489_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_483_, v_es_486_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_i_481_, v___x_490_);
lean_dec(v_i_481_);
v_i_481_ = v___x_491_;
v_source_482_ = v_source_488_;
v_target_483_ = v_target_489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(lean_object* v_data_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_nbuckets_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_494_ = lean_array_get_size(v_data_493_);
v___x_495_ = lean_unsigned_to_nat(2u);
v_nbuckets_496_ = lean_nat_mul(v___x_494_, v___x_495_);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_box(0);
v___x_499_ = lean_mk_array(v_nbuckets_496_, v___x_498_);
v___x_500_ = lean_array_propagate_mark(v_data_493_, v___x_499_);
v___x_501_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(v___x_497_, v_data_493_, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(lean_object* v_m_502_, lean_object* v_a_503_, lean_object* v_b_504_){
_start:
{
lean_object* v_size_505_; lean_object* v_buckets_506_; lean_object* v___x_507_; uint64_t v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; uint64_t v_fold_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; size_t v___x_519_; lean_object* v_bkt_520_; uint8_t v___x_521_; 
v_size_505_ = lean_ctor_get(v_m_502_, 0);
v_buckets_506_ = lean_ctor_get(v_m_502_, 1);
v___x_507_ = lean_array_get_size(v_buckets_506_);
v___x_508_ = l_Lean_Expr_hash(v_a_503_);
v___x_509_ = 32ULL;
v___x_510_ = lean_uint64_shift_right(v___x_508_, v___x_509_);
v_fold_511_ = lean_uint64_xor(v___x_508_, v___x_510_);
v___x_512_ = 16ULL;
v___x_513_ = lean_uint64_shift_right(v_fold_511_, v___x_512_);
v___x_514_ = lean_uint64_xor(v_fold_511_, v___x_513_);
v___x_515_ = lean_uint64_to_usize(v___x_514_);
v___x_516_ = lean_usize_of_nat(v___x_507_);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_sub(v___x_516_, v___x_517_);
v___x_519_ = lean_usize_land(v___x_515_, v___x_518_);
v_bkt_520_ = lean_array_uget_borrowed(v_buckets_506_, v___x_519_);
v___x_521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_503_, v_bkt_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_542_; 
lean_inc_ref(v_buckets_506_);
lean_inc(v_size_505_);
v_isSharedCheck_542_ = !lean_is_exclusive(v_m_502_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; lean_object* v_unused_544_; 
v_unused_543_ = lean_ctor_get(v_m_502_, 1);
lean_dec(v_unused_543_);
v_unused_544_ = lean_ctor_get(v_m_502_, 0);
lean_dec(v_unused_544_);
v___x_523_ = v_m_502_;
v_isShared_524_ = v_isSharedCheck_542_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_m_502_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_542_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v_size_x27_526_; lean_object* v___x_527_; lean_object* v_buckets_x27_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v_size_x27_526_ = lean_nat_add(v_size_505_, v___x_525_);
lean_dec(v_size_505_);
lean_inc(v_bkt_520_);
v___x_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_527_, 0, v_a_503_);
lean_ctor_set(v___x_527_, 1, v_b_504_);
lean_ctor_set(v___x_527_, 2, v_bkt_520_);
v_buckets_x27_528_ = lean_array_uset(v_buckets_506_, v___x_519_, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(4u);
v___x_530_ = lean_nat_mul(v_size_x27_526_, v___x_529_);
v___x_531_ = lean_unsigned_to_nat(3u);
v___x_532_ = lean_nat_div(v___x_530_, v___x_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_array_get_size(v_buckets_x27_528_);
v___x_534_ = lean_nat_dec_le(v___x_532_, v___x_533_);
lean_dec(v___x_532_);
if (v___x_534_ == 0)
{
lean_object* v_val_535_; lean_object* v___x_537_; 
v_val_535_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_buckets_x27_528_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_val_535_);
lean_ctor_set(v___x_523_, 0, v_size_x27_526_);
v___x_537_ = v___x_523_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_size_x27_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_val_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
else
{
lean_object* v___x_540_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_buckets_x27_528_);
lean_ctor_set(v___x_523_, 0, v_size_x27_526_);
v___x_540_ = v___x_523_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_size_x27_526_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_buckets_x27_528_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_dec(v_b_504_);
lean_dec_ref(v_a_503_);
return v_m_502_;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(lean_object* v_op_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_e_554_; lean_object* v___y_555_; 
if (lean_obj_tag(v_a_546_) == 5)
{
lean_object* v_fn_561_; 
v_fn_561_ = lean_ctor_get(v_a_546_, 0);
if (lean_obj_tag(v_fn_561_) == 5)
{
lean_object* v_arg_562_; lean_object* v_fn_563_; lean_object* v_arg_564_; lean_object* v___x_565_; 
v_arg_562_ = lean_ctor_get(v_a_546_, 1);
v_fn_563_ = lean_ctor_get(v_fn_561_, 0);
v_arg_564_ = lean_ctor_get(v_fn_561_, 1);
lean_inc_ref(v_fn_563_);
lean_inc_ref(v_op_545_);
v___x_565_ = l_Lean_Meta_isExprDefEq(v_op_545_, v_fn_563_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_607_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_607_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_607_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_607_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
uint8_t v___x_570_; 
v___x_570_ = lean_unbox(v_a_566_);
lean_dec(v_a_566_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
lean_dec_ref(v_op_545_);
v___x_571_ = lean_box(0);
lean_inc_ref(v_a_546_);
v___x_572_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v_a_547_, v_a_546_, v___x_571_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v_a_546_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_572_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_574_);
v___x_576_ = v___x_568_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
else
{
lean_object* v___x_578_; 
lean_inc_ref(v_arg_564_);
lean_inc_ref(v_arg_562_);
lean_del_object(v___x_568_);
lean_dec_ref_known(v_a_546_, 2);
lean_inc_ref(v_op_545_);
v___x_578_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_545_, v_arg_564_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_606_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v_fst_580_ = lean_ctor_get(v_a_579_, 0);
v_snd_581_ = lean_ctor_get(v_a_579_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v_a_579_);
if (v_isSharedCheck_606_ == 0)
{
v___x_583_ = v_a_579_;
v_isShared_584_ = v_isSharedCheck_606_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_snd_581_);
lean_inc(v_fst_580_);
lean_dec(v_a_579_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_606_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; 
v___x_585_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_545_, v_arg_562_, v_snd_581_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_605_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_605_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_605_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_605_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_604_; 
v_fst_590_ = lean_ctor_get(v_a_586_, 0);
v_snd_591_ = lean_ctor_get(v_a_586_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_a_586_);
if (v_isSharedCheck_604_ == 0)
{
v___x_593_ = v_a_586_;
v_isShared_594_ = v_isSharedCheck_604_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snd_591_);
lean_inc(v_fst_590_);
lean_dec(v_a_586_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_604_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v_fst_590_);
v___x_596_ = v___x_583_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_fst_580_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_fst_590_);
v___x_596_ = v_reuseFailAlloc_603_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_snd_591_);
v___x_598_ = v_reuseFailAlloc_602_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_598_);
v___x_600_ = v___x_588_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_583_);
lean_dec(v_fst_580_);
return v___x_585_;
}
}
}
else
{
lean_dec_ref(v_arg_562_);
lean_dec_ref(v_op_545_);
return v___x_578_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref_known(v_a_546_, 2);
lean_dec_ref(v_a_547_);
lean_dec_ref(v_op_545_);
v_a_608_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_565_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_565_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_dec_ref(v_op_545_);
v_e_554_ = v_a_546_;
v___y_555_ = v_a_547_;
goto v___jp_553_;
}
}
else
{
lean_dec_ref(v_op_545_);
v_e_554_ = v_a_546_;
v___y_555_ = v_a_547_;
goto v___jp_553_;
}
v___jp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_556_ = lean_box(0);
lean_inc_ref(v_e_554_);
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v___y_555_, v_e_554_, v___x_556_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v_e_554_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_545_ = stack[0].m_obj;
lean_object* v_a_546_ = stack[1].m_obj;
lean_object* v_a_547_ = stack[2].m_obj;
lean_object* v_a_548_ = stack[3].m_obj;
lean_object* v_a_549_ = stack[4].m_obj;
lean_object* v_a_550_ = stack[5].m_obj;
lean_object* v_a_551_ = stack[6].m_obj;
lean_object* v_res_616_;
v_res_616_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
stack->m_obj
 = v_res_616_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr___boxed(lean_object* v_op_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0(lean_object* v_00_u03b2_626_, lean_object* v_m_627_, lean_object* v_a_628_, lean_object* v_b_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v_m_627_, v_a_628_, v_b_629_);
return v___x_630_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(lean_object* v_00_u03b2_631_, lean_object* v_a_632_, lean_object* v_x_633_){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_632_, v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_632_ = stack[1].m_obj;
lean_object* v_x_633_ = stack[2].m_obj;
uint8_t v_res_635_;
v_res_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(lean_box(0), v_a_632_, v_x_633_);
stack->m_num = v_res_635_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_636_, lean_object* v_a_637_, lean_object* v_x_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(v_00_u03b2_636_, v_a_637_, v_x_638_);
lean_dec(v_x_638_);
lean_dec_ref(v_a_637_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1(lean_object* v_00_u03b2_641_, lean_object* v_data_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_data_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_644_, lean_object* v_i_645_, lean_object* v_source_646_, lean_object* v_target_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(v_i_645_, v_source_646_, v_target_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_650_, v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(lean_object* v_varMap_653_, lean_object* v_a_654_){
_start:
{
if (lean_obj_tag(v_a_654_) == 0)
{
lean_object* v_lhs_655_; lean_object* v_rhs_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_665_; 
v_lhs_655_ = lean_ctor_get(v_a_654_, 0);
v_rhs_656_ = lean_ctor_get(v_a_654_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_a_654_);
if (v_isSharedCheck_665_ == 0)
{
v___x_658_ = v_a_654_;
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_rhs_656_);
lean_inc(v_lhs_655_);
lean_dec(v_a_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
lean_inc_ref(v_varMap_653_);
v___x_660_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(v_varMap_653_, v_lhs_655_);
v___x_661_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(v_varMap_653_, v_rhs_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
lean_ctor_set(v___x_658_, 1, v___x_661_);
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_e_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_e_666_ = lean_ctor_get(v_a_654_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v_a_654_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v_a_654_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_e_666_);
lean_dec(v_a_654_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_apply_1(v_varMap_653_, v_e_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 0);
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5(lean_object* v_msg_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_panic_fn_borrowed(v___x_676_, v_msg_675_);
return v___x_677_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_681_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__2));
v___x_682_ = lean_unsigned_to_nat(11u);
v___x_683_ = lean_unsigned_to_nat(163u);
v___x_684_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__1));
v___x_685_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__0));
v___x_686_ = l_mkPanicMessageWithDecl(v___x_685_, v___x_684_, v___x_683_, v___x_682_, v___x_681_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(lean_object* v_a_687_, lean_object* v_x_688_){
_start:
{
if (lean_obj_tag(v_x_688_) == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3);
v___x_690_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5(v___x_689_);
return v___x_690_;
}
else
{
lean_object* v_key_691_; lean_object* v_value_692_; lean_object* v_tail_693_; uint8_t v___x_694_; 
v_key_691_ = lean_ctor_get(v_x_688_, 0);
v_value_692_ = lean_ctor_get(v_x_688_, 1);
v_tail_693_ = lean_ctor_get(v_x_688_, 2);
v___x_694_ = lean_expr_eqv(v_key_691_, v_a_687_);
if (v___x_694_ == 0)
{
v_x_688_ = v_tail_693_;
goto _start;
}
else
{
lean_inc(v_value_692_);
return v_value_692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___boxed(lean_object* v_a_696_, lean_object* v_x_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(v_a_696_, v_x_697_);
lean_dec(v_x_697_);
lean_dec_ref(v_a_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(lean_object* v_m_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_buckets_701_; lean_object* v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v___x_705_; uint64_t v_fold_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_buckets_701_ = lean_ctor_get(v_m_699_, 1);
v___x_702_ = lean_array_get_size(v_buckets_701_);
v___x_703_ = l_Lean_Expr_hash(v_a_700_);
v___x_704_ = 32ULL;
v___x_705_ = lean_uint64_shift_right(v___x_703_, v___x_704_);
v_fold_706_ = lean_uint64_xor(v___x_703_, v___x_705_);
v___x_707_ = 16ULL;
v___x_708_ = lean_uint64_shift_right(v_fold_706_, v___x_707_);
v___x_709_ = lean_uint64_xor(v_fold_706_, v___x_708_);
v___x_710_ = lean_uint64_to_usize(v___x_709_);
v___x_711_ = lean_usize_of_nat(v___x_702_);
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_sub(v___x_711_, v___x_712_);
v___x_714_ = lean_usize_land(v___x_710_, v___x_713_);
v___x_715_ = lean_array_uget_borrowed(v_buckets_701_, v___x_714_);
v___x_716_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(v_a_700_, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___boxed(lean_object* v_m_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(v_m_717_, v_a_718_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_m_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0(lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(v___y_720_, v___y_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___lam__0___boxed(lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Meta_AC_toACExpr___lam__0(v___y_723_, v___y_724_);
lean_dec_ref(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_AC_toACExpr_spec__4(lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_727_) == 0)
{
return v_x_726_;
}
else
{
lean_object* v_key_728_; lean_object* v_tail_729_; lean_object* v___x_730_; 
v_key_728_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_key_728_);
v_tail_729_ = lean_ctor_get(v_x_727_, 2);
lean_inc(v_tail_729_);
lean_dec_ref_known(v_x_727_, 3);
v___x_730_ = lean_array_push(v_x_726_, v_key_728_);
v_x_726_ = v___x_730_;
v_x_727_ = v_tail_729_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(lean_object* v_as_732_, size_t v_i_733_, size_t v_stop_734_, lean_object* v_b_735_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = lean_usize_dec_eq(v_i_733_, v_stop_734_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; size_t v___x_739_; size_t v___x_740_; 
v___x_737_ = lean_array_uget_borrowed(v_as_732_, v_i_733_);
lean_inc(v___x_737_);
v___x_738_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_AC_toACExpr_spec__4(v_b_735_, v___x_737_);
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_add(v_i_733_, v___x_739_);
v_i_733_ = v___x_740_;
v_b_735_ = v___x_738_;
goto _start;
}
else
{
return v_b_735_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_732_ = stack[0].m_obj;
size_t v_i_733_ = stack[1].m_num;
size_t v_stop_734_ = stack[2].m_num;
lean_object* v_b_735_ = stack[3].m_obj;
lean_object* v_res_742_;
v_res_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_as_732_, v_i_733_, v_stop_734_, v_b_735_);
stack->m_obj
 = v_res_742_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5___boxed(lean_object* v_as_743_, lean_object* v_i_744_, lean_object* v_stop_745_, lean_object* v_b_746_){
_start:
{
size_t v_i_boxed_747_; size_t v_stop_boxed_748_; lean_object* v_res_749_; 
v_i_boxed_747_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_stop_boxed_748_ = lean_unbox_usize(v_stop_745_);
lean_dec(v_stop_745_);
v_res_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_as_743_, v_i_boxed_747_, v_stop_boxed_748_, v_b_746_);
lean_dec_ref(v_as_743_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(lean_object* v_xs_750_, lean_object* v_j_751_){
_start:
{
lean_object* v_zero_752_; uint8_t v_isZero_753_; 
v_zero_752_ = lean_unsigned_to_nat(0u);
v_isZero_753_ = lean_nat_dec_eq(v_j_751_, v_zero_752_);
if (v_isZero_753_ == 1)
{
lean_dec(v_j_751_);
return v_xs_750_;
}
else
{
lean_object* v_one_754_; lean_object* v_n_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_one_754_ = lean_unsigned_to_nat(1u);
v_n_755_ = lean_nat_sub(v_j_751_, v_one_754_);
v___x_756_ = lean_array_fget_borrowed(v_xs_750_, v_j_751_);
v___x_757_ = lean_array_fget_borrowed(v_xs_750_, v_n_755_);
v___x_758_ = lean_expr_lt(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_dec(v_n_755_);
lean_dec(v_j_751_);
return v_xs_750_;
}
else
{
lean_object* v___x_759_; 
v___x_759_ = lean_array_fswap(v_xs_750_, v_j_751_, v_n_755_);
lean_dec(v_j_751_);
v_xs_750_ = v___x_759_;
v_j_751_ = v_n_755_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1(lean_object* v_xs_761_, lean_object* v_i_762_, lean_object* v_fuel_763_){
_start:
{
lean_object* v_zero_764_; uint8_t v_isZero_765_; 
v_zero_764_ = lean_unsigned_to_nat(0u);
v_isZero_765_ = lean_nat_dec_eq(v_fuel_763_, v_zero_764_);
if (v_isZero_765_ == 1)
{
lean_dec(v_fuel_763_);
lean_dec(v_i_762_);
return v_xs_761_;
}
else
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_array_get_size(v_xs_761_);
v___x_767_ = lean_nat_dec_lt(v_i_762_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v_fuel_763_);
lean_dec(v_i_762_);
return v_xs_761_;
}
else
{
lean_object* v_one_768_; lean_object* v_n_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_one_768_ = lean_unsigned_to_nat(1u);
v_n_769_ = lean_nat_sub(v_fuel_763_, v_one_768_);
lean_dec(v_fuel_763_);
lean_inc(v_i_762_);
v___x_770_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(v_xs_761_, v_i_762_);
v___x_771_ = lean_nat_add(v_i_762_, v_one_768_);
lean_dec(v_i_762_);
v_xs_761_ = v___x_770_;
v_i_762_ = v___x_771_;
v_fuel_763_ = v_n_769_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(lean_object* v_a_773_, lean_object* v_b_774_, lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_775_) == 0)
{
lean_dec(v_b_774_);
lean_dec_ref(v_a_773_);
return v_x_775_;
}
else
{
lean_object* v_key_776_; lean_object* v_value_777_; lean_object* v_tail_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_790_; 
v_key_776_ = lean_ctor_get(v_x_775_, 0);
v_value_777_ = lean_ctor_get(v_x_775_, 1);
v_tail_778_ = lean_ctor_get(v_x_775_, 2);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_775_);
if (v_isSharedCheck_790_ == 0)
{
v___x_780_ = v_x_775_;
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_tail_778_);
lean_inc(v_value_777_);
lean_inc(v_key_776_);
lean_dec(v_x_775_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
uint8_t v___x_782_; 
v___x_782_ = lean_expr_eqv(v_key_776_, v_a_773_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_773_, v_b_774_, v_tail_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 2, v___x_783_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_key_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_value_777_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
else
{
lean_object* v___x_788_; 
lean_dec(v_value_777_);
lean_dec(v_key_776_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v_b_774_);
lean_ctor_set(v___x_780_, 0, v_a_773_);
v___x_788_ = v___x_780_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_773_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_b_774_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_tail_778_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(lean_object* v_m_791_, lean_object* v_a_792_, lean_object* v_b_793_){
_start:
{
lean_object* v_size_794_; lean_object* v_buckets_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_838_; 
v_size_794_ = lean_ctor_get(v_m_791_, 0);
v_buckets_795_ = lean_ctor_get(v_m_791_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_m_791_);
if (v_isSharedCheck_838_ == 0)
{
v___x_797_ = v_m_791_;
v_isShared_798_ = v_isSharedCheck_838_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_buckets_795_);
lean_inc(v_size_794_);
lean_dec(v_m_791_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_838_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; uint64_t v___x_800_; uint64_t v___x_801_; uint64_t v___x_802_; uint64_t v_fold_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v_bkt_812_; uint8_t v___x_813_; 
v___x_799_ = lean_array_get_size(v_buckets_795_);
v___x_800_ = l_Lean_Expr_hash(v_a_792_);
v___x_801_ = 32ULL;
v___x_802_ = lean_uint64_shift_right(v___x_800_, v___x_801_);
v_fold_803_ = lean_uint64_xor(v___x_800_, v___x_802_);
v___x_804_ = 16ULL;
v___x_805_ = lean_uint64_shift_right(v_fold_803_, v___x_804_);
v___x_806_ = lean_uint64_xor(v_fold_803_, v___x_805_);
v___x_807_ = lean_uint64_to_usize(v___x_806_);
v___x_808_ = lean_usize_of_nat(v___x_799_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_sub(v___x_808_, v___x_809_);
v___x_811_ = lean_usize_land(v___x_807_, v___x_810_);
v_bkt_812_ = lean_array_uget_borrowed(v_buckets_795_, v___x_811_);
v___x_813_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_792_, v_bkt_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v_size_x27_815_; lean_object* v___x_816_; lean_object* v_buckets_x27_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_814_ = lean_unsigned_to_nat(1u);
v_size_x27_815_ = lean_nat_add(v_size_794_, v___x_814_);
lean_dec(v_size_794_);
lean_inc(v_bkt_812_);
v___x_816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_816_, 0, v_a_792_);
lean_ctor_set(v___x_816_, 1, v_b_793_);
lean_ctor_set(v___x_816_, 2, v_bkt_812_);
v_buckets_x27_817_ = lean_array_uset(v_buckets_795_, v___x_811_, v___x_816_);
v___x_818_ = lean_unsigned_to_nat(4u);
v___x_819_ = lean_nat_mul(v_size_x27_815_, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(3u);
v___x_821_ = lean_nat_div(v___x_819_, v___x_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_array_get_size(v_buckets_x27_817_);
v___x_823_ = lean_nat_dec_le(v___x_821_, v___x_822_);
lean_dec(v___x_821_);
if (v___x_823_ == 0)
{
lean_object* v_val_824_; lean_object* v___x_826_; 
v_val_824_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_buckets_x27_817_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v_val_824_);
lean_ctor_set(v___x_797_, 0, v_size_x27_815_);
v___x_826_ = v___x_797_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_size_x27_815_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_val_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
lean_object* v___x_829_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v_buckets_x27_817_);
lean_ctor_set(v___x_797_, 0, v_size_x27_815_);
v___x_829_ = v___x_797_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_size_x27_815_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_buckets_x27_817_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_object* v___x_831_; lean_object* v_buckets_x27_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
lean_inc(v_bkt_812_);
v___x_831_ = lean_box(0);
v_buckets_x27_832_ = lean_array_uset(v_buckets_795_, v___x_811_, v___x_831_);
v___x_833_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_792_, v_b_793_, v_bkt_812_);
v___x_834_ = lean_array_uset(v_buckets_x27_832_, v___x_811_, v___x_833_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_834_);
v___x_836_ = v___x_797_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_size_794_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(lean_object* v_as_839_, size_t v_i_840_, size_t v_stop_841_, lean_object* v_b_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = lean_usize_dec_eq(v_i_840_, v_stop_841_);
if (v___x_843_ == 0)
{
lean_object* v_size_844_; lean_object* v___x_845_; lean_object* v___x_846_; size_t v___x_847_; size_t v___x_848_; 
v_size_844_ = lean_ctor_get(v_b_842_, 0);
lean_inc(v_size_844_);
v___x_845_ = lean_array_uget_borrowed(v_as_839_, v_i_840_);
lean_inc(v___x_845_);
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(v_b_842_, v___x_845_, v_size_844_);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_add(v_i_840_, v___x_847_);
v_i_840_ = v___x_848_;
v_b_842_ = v___x_846_;
goto _start;
}
else
{
return v_b_842_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_839_ = stack[0].m_obj;
size_t v_i_840_ = stack[1].m_num;
size_t v_stop_841_ = stack[2].m_num;
lean_object* v_b_842_ = stack[3].m_obj;
lean_object* v_res_850_;
v_res_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v_as_839_, v_i_840_, v_stop_841_, v_b_842_);
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3___boxed(lean_object* v_as_851_, lean_object* v_i_852_, lean_object* v_stop_853_, lean_object* v_b_854_){
_start:
{
size_t v_i_boxed_855_; size_t v_stop_boxed_856_; lean_object* v_res_857_; 
v_i_boxed_855_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_stop_boxed_856_ = lean_unbox_usize(v_stop_853_);
lean_dec(v_stop_853_);
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v_as_851_, v_i_boxed_855_, v_stop_boxed_856_, v_b_854_);
lean_dec_ref(v_as_851_);
return v_res_857_;
}
}
static lean_object* _init_l_Lean_Meta_AC_toACExpr___closed__0(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_unsigned_to_nat(16u);
v___x_860_ = lean_mk_array(v___x_859_, v___x_858_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Meta_AC_toACExpr___closed__1(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = lean_obj_once(&l_Lean_Meta_AC_toACExpr___closed__0, &l_Lean_Meta_AC_toACExpr___closed__0_once, _init_l_Lean_Meta_AC_toACExpr___closed__0);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___x_861_);
return v___x_863_;
}
}
lean_object* l_Lean_Meta_AC_toACExpr(lean_object* v_op_864_, lean_object* v_l_865_, lean_object* v_r_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_inc_ref(v_op_864_);
v___x_872_ = l_Lean_mkAppB(v_op_864_, v_l_865_, v_r_866_);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_obj_once(&l_Lean_Meta_AC_toACExpr___closed__1, &l_Lean_Meta_AC_toACExpr___closed__1_once, _init_l_Lean_Meta_AC_toACExpr___closed__1);
v___x_875_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(v_op_864_, v___x_872_, v___x_874_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_918_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_918_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_918_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_918_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_fst_880_; lean_object* v_snd_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_917_; 
v_fst_880_ = lean_ctor_get(v_a_876_, 0);
v_snd_881_ = lean_ctor_get(v_a_876_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_a_876_);
if (v_isSharedCheck_917_ == 0)
{
v___x_883_ = v_a_876_;
v_isShared_884_ = v_isSharedCheck_917_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_snd_881_);
lean_inc(v_fst_880_);
lean_dec(v_a_876_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_917_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_897_; lean_object* v_size_909_; lean_object* v_buckets_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_size_909_ = lean_ctor_get(v_snd_881_, 0);
lean_inc(v_size_909_);
v_buckets_910_ = lean_ctor_get(v_snd_881_, 1);
lean_inc_ref(v_buckets_910_);
lean_dec(v_snd_881_);
v___x_911_ = lean_mk_empty_array_with_capacity(v_size_909_);
lean_dec(v_size_909_);
v___x_912_ = lean_array_get_size(v_buckets_910_);
v___x_913_ = lean_nat_dec_lt(v___x_873_, v___x_912_);
if (v___x_913_ == 0)
{
lean_dec_ref(v_buckets_910_);
v___y_897_ = v___x_911_;
goto v___jp_896_;
}
else
{
size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((size_t)0ULL);
v___x_915_ = lean_usize_of_nat(v___x_912_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_buckets_910_, v___x_914_, v___x_915_, v___x_911_);
lean_dec_ref(v_buckets_910_);
v___y_897_ = v___x_916_;
goto v___jp_896_;
}
v___jp_885_:
{
lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___f_888_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_toACExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_888_, 0, v___y_887_);
v___x_889_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(v___f_888_, v_fst_880_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v___x_889_);
lean_ctor_set(v___x_883_, 0, v___y_886_);
v___x_891_ = v___x_883_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___y_886_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_889_);
v___x_891_ = v_reuseFailAlloc_895_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_891_);
v___x_893_ = v___x_878_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
v___jp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_898_ = lean_array_get_size(v___y_897_);
v___x_899_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1(v___y_897_, v___x_873_, v___x_898_);
v___x_900_ = lean_array_get_size(v___x_899_);
v___x_901_ = lean_nat_dec_lt(v___x_873_, v___x_900_);
if (v___x_901_ == 0)
{
v___y_886_ = v___x_899_;
v___y_887_ = v___x_874_;
goto v___jp_885_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = lean_nat_dec_le(v___x_900_, v___x_900_);
if (v___x_902_ == 0)
{
if (v___x_901_ == 0)
{
v___y_886_ = v___x_899_;
v___y_887_ = v___x_874_;
goto v___jp_885_;
}
else
{
size_t v___x_903_; size_t v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((size_t)0ULL);
v___x_904_ = lean_usize_of_nat(v___x_900_);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v___x_899_, v___x_903_, v___x_904_, v___x_874_);
v___y_886_ = v___x_899_;
v___y_887_ = v___x_905_;
goto v___jp_885_;
}
}
else
{
size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; 
v___x_906_ = ((size_t)0ULL);
v___x_907_ = lean_usize_of_nat(v___x_900_);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v___x_899_, v___x_906_, v___x_907_, v___x_874_);
v___y_886_ = v___x_899_;
v___y_887_ = v___x_908_;
goto v___jp_885_;
}
}
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
v_a_919_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_875_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_875_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_toACExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_864_ = stack[0].m_obj;
lean_object* v_l_865_ = stack[1].m_obj;
lean_object* v_r_866_ = stack[2].m_obj;
lean_object* v_a_867_ = stack[3].m_obj;
lean_object* v_a_868_ = stack[4].m_obj;
lean_object* v_a_869_ = stack[5].m_obj;
lean_object* v_a_870_ = stack[6].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Lean_Meta_AC_toACExpr(v_op_864_, v_l_865_, v_r_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_toACExpr___boxed(lean_object* v_op_928_, lean_object* v_l_929_, lean_object* v_r_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Meta_AC_toACExpr(v_op_928_, v_l_929_, v_r_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0(lean_object* v_00_u03b2_937_, lean_object* v_m_938_, lean_object* v_a_939_, lean_object* v_b_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(v_m_938_, v_a_939_, v_b_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0(lean_object* v_00_u03b2_942_, lean_object* v_a_943_, lean_object* v_b_944_, lean_object* v_x_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_943_, v_b_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2(lean_object* v_xs_947_, lean_object* v_j_948_, lean_object* v_h_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(v_xs_947_, v_j_948_);
return v___x_950_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(lean_object* v_k_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
v___x_958_ = lean_apply_6(v_k_951_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, lean_box(0));
return v___x_958_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_951_ = stack[0].m_obj;
lean_object* v_b_952_ = stack[1].m_obj;
lean_object* v___y_953_ = stack[2].m_obj;
lean_object* v___y_954_ = stack[3].m_obj;
lean_object* v___y_955_ = stack[4].m_obj;
lean_object* v___y_956_ = stack[5].m_obj;
lean_object* v_res_959_;
v_res_959_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(v_k_951_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
stack->m_obj
 = v_res_959_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(v_k_960_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_967_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(lean_object* v_name_968_, uint8_t v_bi_969_, lean_object* v_type_970_, lean_object* v_k_971_, uint8_t v_kind_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___f_978_; lean_object* v___x_979_; 
v___f_978_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_978_, 0, v_k_971_);
v___x_979_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_968_, v_bi_969_, v_type_970_, v___f_978_, v_kind_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_979_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_979_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_968_ = stack[0].m_obj;
uint8_t v_bi_969_ = stack[1].m_num;
lean_object* v_type_970_ = stack[2].m_obj;
lean_object* v_k_971_ = stack[3].m_obj;
uint8_t v_kind_972_ = stack[4].m_num;
lean_object* v___y_973_ = stack[5].m_obj;
lean_object* v___y_974_ = stack[6].m_obj;
lean_object* v___y_975_ = stack[7].m_obj;
lean_object* v___y_976_ = stack[8].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_968_, v_bi_969_, v_type_970_, v_k_971_, v_kind_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___boxed(lean_object* v_name_997_, lean_object* v_bi_998_, lean_object* v_type_999_, lean_object* v_k_1000_, lean_object* v_kind_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v_bi_boxed_1007_; uint8_t v_kind_boxed_1008_; lean_object* v_res_1009_; 
v_bi_boxed_1007_ = lean_unbox(v_bi_998_);
v_kind_boxed_1008_ = lean_unbox(v_kind_1001_);
v_res_1009_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_997_, v_bi_boxed_1007_, v_type_999_, v_k_1000_, v_kind_boxed_1008_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1009_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(lean_object* v_name_1010_, lean_object* v_type_1011_, lean_object* v_k_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v___x_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = 0;
v___x_1019_ = 0;
v___x_1020_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_1010_, v___x_1018_, v_type_1011_, v_k_1012_, v___x_1019_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
return v___x_1020_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1010_ = stack[0].m_obj;
lean_object* v_type_1011_ = stack[1].m_obj;
lean_object* v_k_1012_ = stack[2].m_obj;
lean_object* v___y_1013_ = stack[3].m_obj;
lean_object* v___y_1014_ = stack[4].m_obj;
lean_object* v___y_1015_ = stack[5].m_obj;
lean_object* v___y_1016_ = stack[6].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v_name_1010_, v_type_1011_, v_k_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg___boxed(lean_object* v_name_1022_, lean_object* v_type_1023_, lean_object* v_k_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v_name_1022_, v_type_1023_, v_k_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0___boxed(lean_object** _args){
lean_object* v_i_1035_ = _args[0];
lean_object* v_v_1036_ = _args[1];
lean_object* v_acc_1037_ = _args[2];
lean_object* v___x_1038_ = _args[3];
lean_object* v_vars_1039_ = _args[4];
lean_object* v___x_1040_ = _args[5];
lean_object* v_val_1041_ = _args[6];
lean_object* v_args_1042_ = _args[7];
lean_object* v_preContext_1043_ = _args[8];
lean_object* v_atoms_1044_ = _args[9];
lean_object* v_k_1045_ = _args[10];
lean_object* v_00_u03b1_1046_ = _args[11];
lean_object* v_u_1047_ = _args[12];
lean_object* v_iv_1048_ = _args[13];
lean_object* v___y_1049_ = _args[14];
lean_object* v___y_1050_ = _args[15];
lean_object* v___y_1051_ = _args[16];
lean_object* v___y_1052_ = _args[17];
lean_object* v___y_1053_ = _args[18];
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(v_i_1035_, v_v_1036_, v_acc_1037_, v___x_1038_, v_vars_1039_, v___x_1040_, v_val_1041_, v_args_1042_, v_preContext_1043_, v_atoms_1044_, v_k_1045_, v_00_u03b1_1046_, v_u_1047_, v_iv_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v_i_1035_);
return v_res_1054_;
}
}
lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(lean_object* v_preContext_1058_, lean_object* v_atoms_1059_, lean_object* v_i_1060_, lean_object* v_acc_1061_, lean_object* v_vars_1062_, lean_object* v_args_1063_, lean_object* v_k_1064_, lean_object* v_00_u03b1_1065_, lean_object* v_u_1066_, lean_object* v_v_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_op_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_op_1073_ = lean_ctor_get(v_preContext_1058_, 1);
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1));
v___x_1075_ = lean_array_fget_borrowed(v_atoms_1059_, v_i_1060_);
v___x_1076_ = lean_unsigned_to_nat(2u);
v___x_1077_ = lean_mk_empty_array_with_capacity(v___x_1076_);
lean_inc_ref(v_op_1073_);
lean_inc_ref(v___x_1077_);
v___x_1078_ = lean_array_push(v___x_1077_, v_op_1073_);
lean_inc(v___x_1075_);
v___x_1079_ = lean_array_push(v___x_1078_, v___x_1075_);
v___x_1080_ = l_Lean_Meta_AC_getInstance(v___x_1074_, v___x_1079_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
if (lean_obj_tag(v_a_1081_) == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec_ref(v___x_1077_);
v___x_1082_ = lean_unsigned_to_nat(1u);
v___x_1083_ = lean_nat_add(v_i_1060_, v___x_1082_);
lean_dec(v_i_1060_);
lean_inc_ref(v_v_1067_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_v_1067_);
lean_ctor_set(v___x_1084_, 1, v_a_1081_);
v___x_1085_ = lean_array_push(v_acc_1061_, v___x_1084_);
v___x_1086_ = lean_array_push(v_vars_1062_, v_v_1067_);
lean_inc(v___x_1075_);
v___x_1087_ = lean_array_push(v_args_1063_, v___x_1075_);
v___x_1088_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1058_, v_atoms_1059_, v_k_1064_, v_00_u03b1_1065_, v_u_1066_, v___x_1083_, v___x_1085_, v___x_1086_, v___x_1087_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1088_;
}
else
{
lean_object* v_val_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_inc(v___x_1075_);
lean_inc_ref(v_op_1073_);
v_val_1089_ = lean_ctor_get(v_a_1081_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v_a_1081_, 1);
lean_inc(v_u_1066_);
lean_inc_ref(v_00_u03b1_1065_);
lean_inc_ref(v_v_1067_);
v___f_1090_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0___boxed), 19, 13);
lean_closure_set(v___f_1090_, 0, v_i_1060_);
lean_closure_set(v___f_1090_, 1, v_v_1067_);
lean_closure_set(v___f_1090_, 2, v_acc_1061_);
lean_closure_set(v___f_1090_, 3, v___x_1077_);
lean_closure_set(v___f_1090_, 4, v_vars_1062_);
lean_closure_set(v___f_1090_, 5, v___x_1075_);
lean_closure_set(v___f_1090_, 6, v_val_1089_);
lean_closure_set(v___f_1090_, 7, v_args_1063_);
lean_closure_set(v___f_1090_, 8, v_preContext_1058_);
lean_closure_set(v___f_1090_, 9, v_atoms_1059_);
lean_closure_set(v___f_1090_, 10, v_k_1064_);
lean_closure_set(v___f_1090_, 11, v_00_u03b1_1065_);
lean_closure_set(v___f_1090_, 12, v_u_1066_);
v___x_1091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3));
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_u_1066_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_mkConst(v___x_1074_, v___x_1093_);
v___x_1095_ = l_Lean_mkApp3(v___x_1094_, v_00_u03b1_1065_, v_op_1073_, v_v_1067_);
v___x_1096_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v___x_1091_, v___x_1095_, v___f_1090_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1096_;
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___x_1077_);
lean_dec_ref(v_v_1067_);
lean_dec(v_u_1066_);
lean_dec_ref(v_00_u03b1_1065_);
lean_dec_ref(v_k_1064_);
lean_dec_ref(v_args_1063_);
lean_dec_ref(v_vars_1062_);
lean_dec_ref(v_acc_1061_);
lean_dec(v_i_1060_);
lean_dec_ref(v_atoms_1059_);
lean_dec_ref(v_preContext_1058_);
v_a_1097_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1080_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1080_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_preContext_1058_ = stack[0].m_obj;
lean_object* v_atoms_1059_ = stack[1].m_obj;
lean_object* v_i_1060_ = stack[2].m_obj;
lean_object* v_acc_1061_ = stack[3].m_obj;
lean_object* v_vars_1062_ = stack[4].m_obj;
lean_object* v_args_1063_ = stack[5].m_obj;
lean_object* v_k_1064_ = stack[6].m_obj;
lean_object* v_00_u03b1_1065_ = stack[7].m_obj;
lean_object* v_u_1066_ = stack[8].m_obj;
lean_object* v_v_1067_ = stack[9].m_obj;
lean_object* v___y_1068_ = stack[10].m_obj;
lean_object* v___y_1069_ = stack[11].m_obj;
lean_object* v___y_1070_ = stack[12].m_obj;
lean_object* v___y_1071_ = stack[13].m_obj;
lean_object* v_res_1105_;
v_res_1105_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(v_preContext_1058_, v_atoms_1059_, v_i_1060_, v_acc_1061_, v_vars_1062_, v_args_1063_, v_k_1064_, v_00_u03b1_1065_, v_u_1066_, v_v_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
stack->m_obj
 = v_res_1105_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___boxed(lean_object* v_preContext_1106_, lean_object* v_atoms_1107_, lean_object* v_i_1108_, lean_object* v_acc_1109_, lean_object* v_vars_1110_, lean_object* v_args_1111_, lean_object* v_k_1112_, lean_object* v_00_u03b1_1113_, lean_object* v_u_1114_, lean_object* v_v_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(v_preContext_1106_, v_atoms_1107_, v_i_1108_, v_acc_1109_, v_vars_1110_, v_args_1111_, v_k_1112_, v_00_u03b1_1113_, v_u_1114_, v_v_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1121_;
}
}
lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(lean_object* v_preContext_1125_, lean_object* v_atoms_1126_, lean_object* v_k_1127_, lean_object* v_00_u03b1_1128_, lean_object* v_u_1129_, lean_object* v_i_1130_, lean_object* v_acc_1131_, lean_object* v_vars_1132_, lean_object* v_args_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_array_get_size(v_atoms_1126_);
v___x_1140_ = lean_nat_dec_lt(v_i_1130_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec(v_i_1130_);
lean_dec(v_u_1129_);
lean_dec_ref(v_00_u03b1_1128_);
lean_dec_ref(v_atoms_1126_);
lean_dec_ref(v_preContext_1125_);
lean_inc(v_a_1137_);
lean_inc_ref(v_a_1136_);
lean_inc(v_a_1135_);
lean_inc_ref(v_a_1134_);
v___x_1141_ = lean_apply_6(v_k_1127_, v_acc_1131_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, lean_box(0));
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; uint8_t v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = 1;
v___x_1144_ = 1;
v___x_1145_ = l_Lean_Meta_mkLambdaFVars(v_vars_1132_, v_a_1142_, v___x_1140_, v___x_1143_, v___x_1140_, v___x_1143_, v___x_1144_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
lean_dec_ref(v_vars_1132_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = l_Lean_mkAppN(v_a_1146_, v_args_1133_);
lean_dec_ref(v_args_1133_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1150_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_dec_ref(v_args_1133_);
return v___x_1145_;
}
}
else
{
lean_dec_ref(v_args_1133_);
lean_dec_ref(v_vars_1132_);
return v___x_1141_;
}
}
else
{
lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_inc_ref(v_00_u03b1_1128_);
v___f_1155_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___boxed), 15, 9);
lean_closure_set(v___f_1155_, 0, v_preContext_1125_);
lean_closure_set(v___f_1155_, 1, v_atoms_1126_);
lean_closure_set(v___f_1155_, 2, v_i_1130_);
lean_closure_set(v___f_1155_, 3, v_acc_1131_);
lean_closure_set(v___f_1155_, 4, v_vars_1132_);
lean_closure_set(v___f_1155_, 5, v_args_1133_);
lean_closure_set(v___f_1155_, 6, v_k_1127_);
lean_closure_set(v___f_1155_, 7, v_00_u03b1_1128_);
lean_closure_set(v___f_1155_, 8, v_u_1129_);
v___x_1156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1));
v___x_1157_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v___x_1156_, v_00_u03b1_1128_, v___f_1155_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
return v___x_1157_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_preContext_1125_ = stack[0].m_obj;
lean_object* v_atoms_1126_ = stack[1].m_obj;
lean_object* v_k_1127_ = stack[2].m_obj;
lean_object* v_00_u03b1_1128_ = stack[3].m_obj;
lean_object* v_u_1129_ = stack[4].m_obj;
lean_object* v_i_1130_ = stack[5].m_obj;
lean_object* v_acc_1131_ = stack[6].m_obj;
lean_object* v_vars_1132_ = stack[7].m_obj;
lean_object* v_args_1133_ = stack[8].m_obj;
lean_object* v_a_1134_ = stack[9].m_obj;
lean_object* v_a_1135_ = stack[10].m_obj;
lean_object* v_a_1136_ = stack[11].m_obj;
lean_object* v_a_1137_ = stack[12].m_obj;
lean_object* v_res_1158_;
v_res_1158_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1125_, v_atoms_1126_, v_k_1127_, v_00_u03b1_1128_, v_u_1129_, v_i_1130_, v_acc_1131_, v_vars_1132_, v_args_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
stack->m_obj
 = v_res_1158_;
}
lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(lean_object* v_i_1159_, lean_object* v_v_1160_, lean_object* v_acc_1161_, lean_object* v___x_1162_, lean_object* v_vars_1163_, lean_object* v___x_1164_, lean_object* v_val_1165_, lean_object* v_args_1166_, lean_object* v_preContext_1167_, lean_object* v_atoms_1168_, lean_object* v_k_1169_, lean_object* v_00_u03b1_1170_, lean_object* v_u_1171_, lean_object* v_iv_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_add(v_i_1159_, v___x_1178_);
lean_inc_ref(v_iv_1172_);
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_iv_1172_);
lean_inc_ref(v_v_1160_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_v_1160_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_array_push(v_acc_1161_, v___x_1181_);
lean_inc_ref(v___x_1162_);
v___x_1183_ = lean_array_push(v___x_1162_, v_v_1160_);
v___x_1184_ = lean_array_push(v___x_1183_, v_iv_1172_);
v___x_1185_ = l_Array_append___redArg(v_vars_1163_, v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = lean_array_push(v___x_1162_, v___x_1164_);
v___x_1187_ = lean_array_push(v___x_1186_, v_val_1165_);
v___x_1188_ = l_Array_append___redArg(v_args_1166_, v___x_1187_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1167_, v_atoms_1168_, v_k_1169_, v_00_u03b1_1170_, v_u_1171_, v___x_1179_, v___x_1182_, v___x_1185_, v___x_1188_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1189_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1159_ = stack[0].m_obj;
lean_object* v_v_1160_ = stack[1].m_obj;
lean_object* v_acc_1161_ = stack[2].m_obj;
lean_object* v___x_1162_ = stack[3].m_obj;
lean_object* v_vars_1163_ = stack[4].m_obj;
lean_object* v___x_1164_ = stack[5].m_obj;
lean_object* v_val_1165_ = stack[6].m_obj;
lean_object* v_args_1166_ = stack[7].m_obj;
lean_object* v_preContext_1167_ = stack[8].m_obj;
lean_object* v_atoms_1168_ = stack[9].m_obj;
lean_object* v_k_1169_ = stack[10].m_obj;
lean_object* v_00_u03b1_1170_ = stack[11].m_obj;
lean_object* v_u_1171_ = stack[12].m_obj;
lean_object* v_iv_1172_ = stack[13].m_obj;
lean_object* v___y_1173_ = stack[14].m_obj;
lean_object* v___y_1174_ = stack[15].m_obj;
lean_object* v___y_1175_ = stack[16].m_obj;
lean_object* v___y_1176_ = stack[17].m_obj;
lean_object* v_res_1190_;
v_res_1190_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(v_i_1159_, v_v_1160_, v_acc_1161_, v___x_1162_, v_vars_1163_, v___x_1164_, v_val_1165_, v_args_1166_, v_preContext_1167_, v_atoms_1168_, v_k_1169_, v_00_u03b1_1170_, v_u_1171_, v_iv_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
stack->m_obj
 = v_res_1190_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___boxed(lean_object* v_preContext_1191_, lean_object* v_atoms_1192_, lean_object* v_k_1193_, lean_object* v_00_u03b1_1194_, lean_object* v_u_1195_, lean_object* v_i_1196_, lean_object* v_acc_1197_, lean_object* v_vars_1198_, lean_object* v_args_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1191_, v_atoms_1192_, v_k_1193_, v_00_u03b1_1194_, v_u_1195_, v_i_1196_, v_acc_1197_, v_vars_1198_, v_args_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1205_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(lean_object* v_00_u03b1_1206_, lean_object* v_name_1207_, uint8_t v_bi_1208_, lean_object* v_type_1209_, lean_object* v_k_1210_, uint8_t v_kind_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_1207_, v_bi_1208_, v_type_1209_, v_k_1210_, v_kind_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1207_ = stack[1].m_obj;
uint8_t v_bi_1208_ = stack[2].m_num;
lean_object* v_type_1209_ = stack[3].m_obj;
lean_object* v_k_1210_ = stack[4].m_obj;
uint8_t v_kind_1211_ = stack[5].m_num;
lean_object* v___y_1212_ = stack[6].m_obj;
lean_object* v___y_1213_ = stack[7].m_obj;
lean_object* v___y_1214_ = stack[8].m_obj;
lean_object* v___y_1215_ = stack[9].m_obj;
lean_object* v_res_1218_;
v_res_1218_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(lean_box(0), v_name_1207_, v_bi_1208_, v_type_1209_, v_k_1210_, v_kind_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
stack->m_obj
 = v_res_1218_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_name_1220_, lean_object* v_bi_1221_, lean_object* v_type_1222_, lean_object* v_k_1223_, lean_object* v_kind_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
uint8_t v_bi_boxed_1230_; uint8_t v_kind_boxed_1231_; lean_object* v_res_1232_; 
v_bi_boxed_1230_ = lean_unbox(v_bi_1221_);
v_kind_boxed_1231_ = lean_unbox(v_kind_1224_);
v_res_1232_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(v_00_u03b1_1219_, v_name_1220_, v_bi_boxed_1230_, v_type_1222_, v_k_1223_, v_kind_boxed_1231_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1232_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(lean_object* v_00_u03b1_1233_, lean_object* v_name_1234_, lean_object* v_type_1235_, lean_object* v_k_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v_name_1234_, v_type_1235_, v_k_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1234_ = stack[1].m_obj;
lean_object* v_type_1235_ = stack[2].m_obj;
lean_object* v_k_1236_ = stack[3].m_obj;
lean_object* v___y_1237_ = stack[4].m_obj;
lean_object* v___y_1238_ = stack[5].m_obj;
lean_object* v___y_1239_ = stack[6].m_obj;
lean_object* v___y_1240_ = stack[7].m_obj;
lean_object* v_res_1243_;
v_res_1243_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(lean_box(0), v_name_1234_, v_type_1235_, v_k_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
stack->m_obj
 = v_res_1243_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___boxed(lean_object* v_00_u03b1_1244_, lean_object* v_name_1245_, lean_object* v_type_1246_, lean_object* v_k_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(v_00_u03b1_1244_, v_name_1245_, v_type_1246_, v_k_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter___redArg(lean_object* v_____do__lift_1254_, lean_object* v_h__1_1255_, lean_object* v_h__2_1256_){
_start:
{
if (lean_obj_tag(v_____do__lift_1254_) == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec(v_h__2_1256_);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_apply_1(v_h__1_1255_, v___x_1257_);
return v___x_1258_;
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1260_; 
lean_dec(v_h__1_1255_);
v_val_1259_ = lean_ctor_get(v_____do__lift_1254_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v_____do__lift_1254_, 1);
v___x_1260_ = lean_apply_1(v_h__2_1256_, v_val_1259_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter(lean_object* v_motive_1261_, lean_object* v_____do__lift_1262_, lean_object* v_h__1_1263_, lean_object* v_h__2_1264_){
_start:
{
if (lean_obj_tag(v_____do__lift_1262_) == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v_h__2_1264_);
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_apply_1(v_h__1_1263_, v___x_1265_);
return v___x_1266_;
}
else
{
lean_object* v_val_1267_; lean_object* v___x_1268_; 
lean_dec(v_h__1_1263_);
v_val_1267_ = lean_ctor_get(v_____do__lift_1262_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v_____do__lift_1262_, 1);
v___x_1268_ = lean_apply_1(v_h__2_1264_, v_val_1267_);
return v___x_1268_;
}
}
}
lean_object* l_Lean_Meta_AC_abstractAtoms(lean_object* v_preContext_1271_, lean_object* v_atoms_1272_, lean_object* v_k_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1279_ = l_Lean_instInhabitedExpr;
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_array_get_borrowed(v___x_1279_, v_atoms_1272_, v___x_1280_);
lean_inc(v_a_1277_);
lean_inc_ref(v_a_1276_);
lean_inc(v_a_1275_);
lean_inc_ref(v_a_1274_);
lean_inc(v___x_1281_);
v___x_1282_ = lean_infer_type(v___x_1281_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_n(v_a_1283_, 2);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = l_Lean_Meta_getLevel(v_a_1283_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = ((lean_object*)(l_Lean_Meta_AC_abstractAtoms___closed__0));
v___x_1287_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(v_preContext_1271_, v_atoms_1272_, v_k_1273_, v_a_1283_, v_a_1285_, v___x_1280_, v___x_1286_, v___x_1286_, v___x_1286_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_a_1283_);
lean_dec_ref(v_k_1273_);
lean_dec_ref(v_atoms_1272_);
lean_dec_ref(v_preContext_1271_);
v_a_1288_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1284_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1284_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_dec_ref(v_k_1273_);
lean_dec_ref(v_atoms_1272_);
lean_dec_ref(v_preContext_1271_);
return v___x_1282_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_abstractAtoms_0interp(lean_interpreter_value* stack)
{
lean_object* v_preContext_1271_ = stack[0].m_obj;
lean_object* v_atoms_1272_ = stack[1].m_obj;
lean_object* v_k_1273_ = stack[2].m_obj;
lean_object* v_a_1274_ = stack[3].m_obj;
lean_object* v_a_1275_ = stack[4].m_obj;
lean_object* v_a_1276_ = stack[5].m_obj;
lean_object* v_a_1277_ = stack[6].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l_Lean_Meta_AC_abstractAtoms(v_preContext_1271_, v_atoms_1272_, v_k_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_abstractAtoms___boxed(lean_object* v_preContext_1297_, lean_object* v_atoms_1298_, lean_object* v_k_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_AC_abstractAtoms(v_preContext_1297_, v_atoms_1298_, v_k_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(lean_object* v___x_1311_, lean_object* v___x_1312_, lean_object* v_tp_1313_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2));
v___x_1315_ = l_Lean_mkConst(v___x_1314_, v___x_1311_);
v___x_1316_ = l_Lean_Expr_app___override(v___x_1312_, v_tp_1313_);
v___x_1317_ = l_Lean_Expr_app___override(v___x_1315_, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v_tp_1325_, lean_object* v_v_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1));
v___x_1328_ = l_Lean_mkConst(v___x_1327_, v___x_1322_);
lean_inc_ref(v_tp_1325_);
v___x_1329_ = l_Lean_Expr_app___override(v___x_1323_, v_tp_1325_);
v___x_1330_ = l_Lean_mkAppB(v___x_1324_, v_tp_1325_, v_v_1326_);
v___x_1331_ = l_Lean_mkAppB(v___x_1328_, v___x_1329_, v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2));
v___x_1340_ = l_Lean_mkConst(v___x_1339_, v___x_1338_);
return v___x_1340_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2));
v___x_1353_ = l_Lean_mkConst(v___x_1352_, v___x_1351_);
return v___x_1353_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11));
v___x_1360_ = l_Lean_mkConst(v___x_1359_, v___x_1358_);
return v___x_1360_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1));
v___x_1363_ = l_Lean_mkConst(v___x_1362_, v___x_1361_);
return v___x_1363_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(lean_object* v_u_1364_, lean_object* v_preContext_1365_, lean_object* v_00_u03b1_1366_, size_t v_sz_1367_, size_t v_i_1368_, lean_object* v_bs_1369_){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_usize_dec_lt(v_i_1368_, v_sz_1367_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v_00_u03b1_1366_);
lean_dec_ref(v_preContext_1365_);
lean_dec(v_u_1364_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_bs_1369_);
return v___x_1372_;
}
else
{
lean_object* v_v_1373_; lean_object* v_fst_1374_; lean_object* v_snd_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1408_; 
v_v_1373_ = lean_array_uget(v_bs_1369_, v_i_1368_);
v_fst_1374_ = lean_ctor_get(v_v_1373_, 0);
v_snd_1375_ = lean_ctor_get(v_v_1373_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_v_1373_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1377_ = v_v_1373_;
v_isShared_1378_ = v_isSharedCheck_1408_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_snd_1375_);
lean_inc(v_fst_1374_);
lean_dec(v_v_1373_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1408_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v_op_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v_bs_x27_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v_op_1379_ = lean_ctor_get(v_preContext_1365_, 1);
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
v___x_1382_ = lean_unsigned_to_nat(0u);
v_bs_x27_1383_ = lean_array_uset(v_bs_1369_, v_i_1368_, v___x_1382_);
v___x_1384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1));
lean_inc(v_u_1364_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 1);
lean_ctor_set(v___x_1377_, 1, v___x_1380_);
lean_ctor_set(v___x_1377_, 0, v_u_1364_);
v___x_1386_ = v___x_1377_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_u_1364_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v___x_1380_);
v___x_1386_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___y_1388_; lean_object* v___x_1396_; lean_object* v_isNeutralClass_1397_; 
lean_inc_ref(v___x_1386_);
v___x_1396_ = l_Lean_mkConst(v___x_1384_, v___x_1386_);
lean_inc(v_fst_1374_);
lean_inc_ref(v_op_1379_);
lean_inc_ref(v_00_u03b1_1366_);
v_isNeutralClass_1397_ = l_Lean_mkApp3(v___x_1396_, v_00_u03b1_1366_, v_op_1379_, v_fst_1374_);
if (lean_obj_tag(v_snd_1375_) == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9);
v___x_1399_ = l_Lean_Expr_app___override(v___x_1381_, v_isNeutralClass_1397_);
v___x_1400_ = l_Lean_Expr_app___override(v___x_1398_, v___x_1399_);
v___y_1388_ = v___x_1400_;
goto v___jp_1387_;
}
else
{
lean_object* v_val_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_val_1401_ = lean_ctor_get(v_snd_1375_, 0);
lean_inc(v_val_1401_);
lean_dec_ref_known(v_snd_1375_, 1);
v___x_1402_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
v___x_1403_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13);
lean_inc_ref(v_isNeutralClass_1397_);
v___x_1404_ = l_Lean_Expr_app___override(v___x_1381_, v_isNeutralClass_1397_);
v___x_1405_ = l_Lean_mkAppB(v___x_1402_, v_isNeutralClass_1397_, v_val_1401_);
v___x_1406_ = l_Lean_mkAppB(v___x_1403_, v___x_1404_, v___x_1405_);
v___y_1388_ = v___x_1406_;
goto v___jp_1387_;
}
v___jp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8));
v___x_1390_ = l_Lean_mkConst(v___x_1389_, v___x_1386_);
lean_inc_ref(v_op_1379_);
lean_inc_ref(v_00_u03b1_1366_);
v___x_1391_ = l_Lean_mkApp4(v___x_1390_, v_00_u03b1_1366_, v_op_1379_, v_fst_1374_, v___y_1388_);
v___x_1392_ = ((size_t)1ULL);
v___x_1393_ = lean_usize_add(v_i_1368_, v___x_1392_);
v___x_1394_ = lean_array_uset(v_bs_x27_1383_, v_i_1368_, v___x_1391_);
v_i_1368_ = v___x_1393_;
v_bs_1369_ = v___x_1394_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1364_ = stack[0].m_obj;
lean_object* v_preContext_1365_ = stack[1].m_obj;
lean_object* v_00_u03b1_1366_ = stack[2].m_obj;
size_t v_sz_1367_ = stack[3].m_num;
size_t v_i_1368_ = stack[4].m_num;
lean_object* v_bs_1369_ = stack[5].m_obj;
lean_object* v_res_1409_;
v_res_1409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1364_, v_preContext_1365_, v_00_u03b1_1366_, v_sz_1367_, v_i_1368_, v_bs_1369_);
stack->m_obj
 = v_res_1409_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___boxed(lean_object* v_u_1410_, lean_object* v_preContext_1411_, lean_object* v_00_u03b1_1412_, lean_object* v_sz_1413_, lean_object* v_i_1414_, lean_object* v_bs_1415_, lean_object* v___y_1416_){
_start:
{
size_t v_sz_boxed_1417_; size_t v_i_boxed_1418_; lean_object* v_res_1419_; 
v_sz_boxed_1417_ = lean_unbox_usize(v_sz_1413_);
lean_dec(v_sz_1413_);
v_i_boxed_1418_ = lean_unbox_usize(v_i_1414_);
lean_dec(v_i_1414_);
v_res_1419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1410_, v_preContext_1411_, v_00_u03b1_1412_, v_sz_boxed_1417_, v_i_boxed_1418_, v_bs_1415_);
return v_res_1419_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(lean_object* v_u_1420_, lean_object* v_preContext_1421_, lean_object* v_00_u03b1_1422_, size_t v_sz_1423_, size_t v_i_1424_, lean_object* v_bs_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_usize_dec_lt(v_i_1424_, v_sz_1423_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec_ref(v_00_u03b1_1422_);
lean_dec_ref(v_preContext_1421_);
lean_dec(v_u_1420_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_bs_1425_);
return v___x_1432_;
}
else
{
lean_object* v_v_1433_; lean_object* v_fst_1434_; lean_object* v_snd_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1468_; 
v_v_1433_ = lean_array_uget(v_bs_1425_, v_i_1424_);
v_fst_1434_ = lean_ctor_get(v_v_1433_, 0);
v_snd_1435_ = lean_ctor_get(v_v_1433_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_v_1433_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1437_ = v_v_1433_;
v_isShared_1438_ = v_isSharedCheck_1468_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_snd_1435_);
lean_inc(v_fst_1434_);
lean_dec(v_v_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1468_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v_op_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_bs_x27_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
v_op_1439_ = lean_ctor_get(v_preContext_1421_, 1);
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
v___x_1442_ = lean_unsigned_to_nat(0u);
v_bs_x27_1443_ = lean_array_uset(v_bs_1425_, v_i_1424_, v___x_1442_);
v___x_1444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1));
lean_inc(v_u_1420_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 1);
lean_ctor_set(v___x_1437_, 1, v___x_1440_);
lean_ctor_set(v___x_1437_, 0, v_u_1420_);
v___x_1446_ = v___x_1437_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_u_1420_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___x_1440_);
v___x_1446_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___y_1448_; lean_object* v___x_1456_; lean_object* v_isNeutralClass_1457_; 
lean_inc_ref(v___x_1446_);
v___x_1456_ = l_Lean_mkConst(v___x_1444_, v___x_1446_);
lean_inc(v_fst_1434_);
lean_inc_ref(v_op_1439_);
lean_inc_ref(v_00_u03b1_1422_);
v_isNeutralClass_1457_ = l_Lean_mkApp3(v___x_1456_, v_00_u03b1_1422_, v_op_1439_, v_fst_1434_);
if (lean_obj_tag(v_snd_1435_) == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9);
v___x_1459_ = l_Lean_Expr_app___override(v___x_1441_, v_isNeutralClass_1457_);
v___x_1460_ = l_Lean_Expr_app___override(v___x_1458_, v___x_1459_);
v___y_1448_ = v___x_1460_;
goto v___jp_1447_;
}
else
{
lean_object* v_val_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_val_1461_ = lean_ctor_get(v_snd_1435_, 0);
lean_inc(v_val_1461_);
lean_dec_ref_known(v_snd_1435_, 1);
v___x_1462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
v___x_1463_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13);
lean_inc_ref(v_isNeutralClass_1457_);
v___x_1464_ = l_Lean_Expr_app___override(v___x_1441_, v_isNeutralClass_1457_);
v___x_1465_ = l_Lean_mkAppB(v___x_1462_, v_isNeutralClass_1457_, v_val_1461_);
v___x_1466_ = l_Lean_mkAppB(v___x_1463_, v___x_1464_, v___x_1465_);
v___y_1448_ = v___x_1466_;
goto v___jp_1447_;
}
v___jp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8));
v___x_1450_ = l_Lean_mkConst(v___x_1449_, v___x_1446_);
lean_inc_ref(v_op_1439_);
lean_inc_ref(v_00_u03b1_1422_);
v___x_1451_ = l_Lean_mkApp4(v___x_1450_, v_00_u03b1_1422_, v_op_1439_, v_fst_1434_, v___y_1448_);
v___x_1452_ = ((size_t)1ULL);
v___x_1453_ = lean_usize_add(v_i_1424_, v___x_1452_);
v___x_1454_ = lean_array_uset(v_bs_x27_1443_, v_i_1424_, v___x_1451_);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1420_, v_preContext_1421_, v_00_u03b1_1422_, v_sz_1423_, v___x_1453_, v___x_1454_);
return v___x_1455_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1420_ = stack[0].m_obj;
lean_object* v_preContext_1421_ = stack[1].m_obj;
lean_object* v_00_u03b1_1422_ = stack[2].m_obj;
size_t v_sz_1423_ = stack[3].m_num;
size_t v_i_1424_ = stack[4].m_num;
lean_object* v_bs_1425_ = stack[5].m_obj;
lean_object* v___y_1426_ = stack[6].m_obj;
lean_object* v___y_1427_ = stack[7].m_obj;
lean_object* v___y_1428_ = stack[8].m_obj;
lean_object* v___y_1429_ = stack[9].m_obj;
lean_object* v_res_1469_;
v_res_1469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(v_u_1420_, v_preContext_1421_, v_00_u03b1_1422_, v_sz_1423_, v_i_1424_, v_bs_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
stack->m_obj
 = v_res_1469_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0___boxed(lean_object* v_u_1470_, lean_object* v_preContext_1471_, lean_object* v_00_u03b1_1472_, lean_object* v_sz_1473_, lean_object* v_i_1474_, lean_object* v_bs_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
size_t v_sz_boxed_1481_; size_t v_i_boxed_1482_; lean_object* v_res_1483_; 
v_sz_boxed_1481_ = lean_unbox_usize(v_sz_1473_);
lean_dec(v_sz_1473_);
v_i_boxed_1482_ = lean_unbox_usize(v_i_1474_);
lean_dec(v_i_1474_);
v_res_1483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(v_u_1470_, v_preContext_1471_, v_00_u03b1_1472_, v_sz_boxed_1481_, v_i_boxed_1482_, v_bs_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = lean_box(0);
v___x_1485_ = l_Lean_instInhabitedExpr;
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v___x_1484_);
return v___x_1486_;
}
}
lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(lean_object* v_preContext_1499_, lean_object* v_00_u03b1_1500_, lean_object* v_u_1501_, lean_object* v_vars_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_fst_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1571_; 
v___x_1508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0_once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_array_get(v___x_1508_, v_vars_1502_, v___x_1509_);
v_fst_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v___x_1510_, 1);
lean_dec(v_unused_1572_);
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1571_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_fst_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1571_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; size_t v_sz_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0));
v___x_1517_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
v___x_1518_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
v_sz_1519_ = lean_array_size(v_vars_1502_);
v___x_1520_ = ((size_t)0ULL);
lean_inc_ref(v_00_u03b1_1500_);
lean_inc_ref(v_preContext_1499_);
lean_inc(v_u_1501_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(v_u_1501_, v_preContext_1499_, v_00_u03b1_1500_, v_sz_1519_, v___x_1520_, v_vars_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v_op_1523_; lean_object* v_assoc_1524_; lean_object* v_comm_1525_; lean_object* v_idem_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v_op_1523_ = lean_ctor_get(v_preContext_1499_, 1);
lean_inc_ref(v_op_1523_);
v_assoc_1524_ = lean_ctor_get(v_preContext_1499_, 2);
lean_inc_ref(v_assoc_1524_);
v_comm_1525_ = lean_ctor_get(v_preContext_1499_, 3);
lean_inc(v_comm_1525_);
v_idem_1526_ = lean_ctor_get(v_preContext_1499_, 4);
lean_inc(v_idem_1526_);
lean_dec_ref(v_preContext_1499_);
v___x_1527_ = lean_array_to_list(v_a_1522_);
v___x_1528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1));
if (v_isShared_1514_ == 0)
{
lean_ctor_set_tag(v___x_1513_, 1);
lean_ctor_set(v___x_1513_, 1, v___x_1515_);
lean_ctor_set(v___x_1513_, 0, v_u_1501_);
v___x_1530_ = v___x_1513_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_u_1501_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1515_);
v___x_1530_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_inc_ref(v___x_1530_);
v___x_1531_ = l_Lean_mkConst(v___x_1528_, v___x_1530_);
lean_inc_ref(v_op_1523_);
lean_inc_ref(v_00_u03b1_1500_);
v___x_1532_ = l_Lean_mkAppB(v___x_1531_, v_00_u03b1_1500_, v_op_1523_);
v___x_1533_ = l_Lean_Meta_mkListLit(v___x_1532_, v___x_1527_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1561_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1561_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1561_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1548_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__4));
lean_inc_ref(v___x_1530_);
v___x_1556_ = l_Lean_mkConst(v___x_1555_, v___x_1530_);
lean_inc_ref(v_op_1523_);
lean_inc_ref(v_00_u03b1_1500_);
v___x_1557_ = l_Lean_mkAppB(v___x_1556_, v_00_u03b1_1500_, v_op_1523_);
if (lean_obj_tag(v_comm_1525_) == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(v___x_1516_, v___x_1517_, v___x_1557_);
v___y_1548_ = v___x_1558_;
goto v___jp_1547_;
}
else
{
lean_object* v_val_1559_; lean_object* v___x_1560_; 
v_val_1559_ = lean_ctor_get(v_comm_1525_, 0);
lean_inc(v_val_1559_);
lean_dec_ref_known(v_comm_1525_, 1);
v___x_1560_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(v___x_1516_, v___x_1517_, v___x_1518_, v___x_1557_, v_val_1559_);
v___y_1548_ = v___x_1560_;
goto v___jp_1547_;
}
v___jp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3));
v___x_1542_ = l_Lean_mkConst(v___x_1541_, v___x_1530_);
v___x_1543_ = l_Lean_mkApp7(v___x_1542_, v_00_u03b1_1500_, v_op_1523_, v_assoc_1524_, v___y_1539_, v___y_1540_, v_a_1534_, v_fst_1511_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1543_);
v___x_1545_ = v___x_1536_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
v___jp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = ((lean_object*)(l_Lean_Meta_AC_preContext___closed__6));
lean_inc_ref(v___x_1530_);
v___x_1550_ = l_Lean_mkConst(v___x_1549_, v___x_1530_);
lean_inc_ref(v_op_1523_);
lean_inc_ref(v_00_u03b1_1500_);
v___x_1551_ = l_Lean_mkAppB(v___x_1550_, v_00_u03b1_1500_, v_op_1523_);
if (lean_obj_tag(v_idem_1526_) == 0)
{
lean_object* v___x_1552_; 
v___x_1552_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(v___x_1516_, v___x_1517_, v___x_1551_);
v___y_1539_ = v___y_1548_;
v___y_1540_ = v___x_1552_;
goto v___jp_1538_;
}
else
{
lean_object* v_val_1553_; lean_object* v___x_1554_; 
v_val_1553_ = lean_ctor_get(v_idem_1526_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v_idem_1526_, 1);
v___x_1554_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(v___x_1516_, v___x_1517_, v___x_1518_, v___x_1551_, v_val_1553_);
v___y_1539_ = v___y_1548_;
v___y_1540_ = v___x_1554_;
goto v___jp_1538_;
}
}
}
}
else
{
lean_dec_ref(v___x_1530_);
lean_dec(v_idem_1526_);
lean_dec(v_comm_1525_);
lean_dec_ref(v_assoc_1524_);
lean_dec_ref(v_op_1523_);
lean_dec(v_fst_1511_);
lean_dec_ref(v_00_u03b1_1500_);
return v___x_1533_;
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_del_object(v___x_1513_);
lean_dec(v_fst_1511_);
lean_dec(v_u_1501_);
lean_dec_ref(v_00_u03b1_1500_);
lean_dec_ref(v_preContext_1499_);
v_a_1563_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1521_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1521_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_preContext_1499_ = stack[0].m_obj;
lean_object* v_00_u03b1_1500_ = stack[1].m_obj;
lean_object* v_u_1501_ = stack[2].m_obj;
lean_object* v_vars_1502_ = stack[3].m_obj;
lean_object* v_a_1503_ = stack[4].m_obj;
lean_object* v_a_1504_ = stack[5].m_obj;
lean_object* v_a_1505_ = stack[6].m_obj;
lean_object* v_a_1506_ = stack[7].m_obj;
lean_object* v_res_1573_;
v_res_1573_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(v_preContext_1499_, v_00_u03b1_1500_, v_u_1501_, v_vars_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
stack->m_obj
 = v_res_1573_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___boxed(lean_object* v_preContext_1574_, lean_object* v_00_u03b1_1575_, lean_object* v_u_1576_, lean_object* v_vars_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(v_preContext_1574_, v_00_u03b1_1575_, v_u_1576_, v_vars_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
return v_res_1583_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(lean_object* v_u_1584_, lean_object* v_preContext_1585_, lean_object* v_00_u03b1_1586_, size_t v_sz_1587_, size_t v_i_1588_, lean_object* v_bs_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_1584_, v_preContext_1585_, v_00_u03b1_1586_, v_sz_1587_, v_i_1588_, v_bs_1589_);
return v___x_1595_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1584_ = stack[0].m_obj;
lean_object* v_preContext_1585_ = stack[1].m_obj;
lean_object* v_00_u03b1_1586_ = stack[2].m_obj;
size_t v_sz_1587_ = stack[3].m_num;
size_t v_i_1588_ = stack[4].m_num;
lean_object* v_bs_1589_ = stack[5].m_obj;
lean_object* v___y_1590_ = stack[6].m_obj;
lean_object* v___y_1591_ = stack[7].m_obj;
lean_object* v___y_1592_ = stack[8].m_obj;
lean_object* v___y_1593_ = stack[9].m_obj;
lean_object* v_res_1596_;
v_res_1596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(v_u_1584_, v_preContext_1585_, v_00_u03b1_1586_, v_sz_1587_, v_i_1588_, v_bs_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
stack->m_obj
 = v_res_1596_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___boxed(lean_object* v_u_1597_, lean_object* v_preContext_1598_, lean_object* v_00_u03b1_1599_, lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(v_u_1597_, v_preContext_1598_, v_00_u03b1_1599_, v_sz_boxed_1608_, v_i_boxed_1609_, v_bs_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1610_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = lean_box(0);
v___x_1620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2));
v___x_1621_ = l_Lean_mkConst(v___x_1620_, v___x_1619_);
return v___x_1621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5));
v___x_1631_ = l_Lean_mkConst(v___x_1630_, v___x_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(lean_object* v_a_1632_){
_start:
{
if (lean_obj_tag(v_a_1632_) == 0)
{
lean_object* v_x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_x_1633_ = lean_ctor_get(v_a_1632_, 0);
lean_inc(v_x_1633_);
lean_dec_ref_known(v_a_1632_, 1);
v___x_1634_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3_once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3);
v___x_1635_ = l_Lean_mkNatLit(v_x_1633_);
v___x_1636_ = l_Lean_Expr_app___override(v___x_1634_, v___x_1635_);
return v___x_1636_;
}
else
{
lean_object* v_lhs_1637_; lean_object* v_rhs_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_lhs_1637_ = lean_ctor_get(v_a_1632_, 0);
lean_inc_ref(v_lhs_1637_);
v_rhs_1638_ = lean_ctor_get(v_a_1632_, 1);
lean_inc_ref(v_rhs_1638_);
lean_dec_ref_known(v_a_1632_, 2);
v___x_1639_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6_once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6);
v___x_1640_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v_lhs_1637_);
v___x_1641_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v_rhs_1638_);
v___x_1642_ = l_Lean_mkAppB(v___x_1639_, v___x_1640_, v___x_1641_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(lean_object* v_preContext_1643_, lean_object* v_vars_1644_, lean_object* v_a_1645_){
_start:
{
if (lean_obj_tag(v_a_1645_) == 0)
{
lean_object* v_x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref(v_preContext_1643_);
v_x_1646_ = lean_ctor_get(v_a_1645_, 0);
v___x_1647_ = l_Lean_instInhabitedExpr;
v___x_1648_ = lean_array_get_borrowed(v___x_1647_, v_vars_1644_, v_x_1646_);
lean_inc(v___x_1648_);
return v___x_1648_;
}
else
{
lean_object* v_lhs_1649_; lean_object* v_rhs_1650_; lean_object* v_op_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_lhs_1649_ = lean_ctor_get(v_a_1645_, 0);
v_rhs_1650_ = lean_ctor_get(v_a_1645_, 1);
v_op_1651_ = lean_ctor_get(v_preContext_1643_, 1);
lean_inc_ref(v_op_1651_);
lean_inc_ref(v_preContext_1643_);
v___x_1652_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1643_, v_vars_1644_, v_lhs_1649_);
v___x_1653_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1643_, v_vars_1644_, v_rhs_1650_);
v___x_1654_ = l_Lean_mkAppB(v_op_1651_, v___x_1652_, v___x_1653_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget___boxed(lean_object* v_preContext_1655_, lean_object* v_vars_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1655_, v_vars_1656_, v_a_1657_);
lean_dec_ref(v_a_1657_);
lean_dec_ref(v_vars_1656_);
return v_res_1658_;
}
}
lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(lean_object* v_msg_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___f_1666_; lean_object* v___x_1991__overap_1667_; lean_object* v___x_1668_; 
v___f_1666_ = ((lean_object*)(l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0));
v___x_1991__overap_1667_ = lean_panic_fn_borrowed(v___f_1666_, v_msg_1660_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1663_);
lean_inc(v___y_1662_);
lean_inc_ref(v___y_1661_);
v___x_1668_ = lean_apply_5(v___x_1991__overap_1667_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, lean_box(0));
return v___x_1668_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1660_ = stack[0].m_obj;
lean_object* v___y_1661_ = stack[1].m_obj;
lean_object* v___y_1662_ = stack[2].m_obj;
lean_object* v___y_1663_ = stack[3].m_obj;
lean_object* v___y_1664_ = stack[4].m_obj;
lean_object* v_res_1669_;
v_res_1669_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(v_msg_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
stack->m_obj
 = v_res_1669_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___boxed(lean_object* v_msg_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(v_msg_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__1(size_t v_sz_1677_, size_t v_i_1678_, lean_object* v_bs_1679_){
_start:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_lt(v_i_1678_, v_sz_1677_);
if (v___x_1680_ == 0)
{
return v_bs_1679_;
}
else
{
lean_object* v_v_1681_; lean_object* v_fst_1682_; lean_object* v___x_1683_; lean_object* v_bs_x27_1684_; size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
v_v_1681_ = lean_array_uget_borrowed(v_bs_1679_, v_i_1678_);
v_fst_1682_ = lean_ctor_get(v_v_1681_, 0);
lean_inc(v_fst_1682_);
v___x_1683_ = lean_unsigned_to_nat(0u);
v_bs_x27_1684_ = lean_array_uset(v_bs_1679_, v_i_1678_, v___x_1683_);
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1678_, v___x_1685_);
v___x_1687_ = lean_array_uset(v_bs_x27_1684_, v_i_1678_, v_fst_1682_);
v_i_1678_ = v___x_1686_;
v_bs_1679_ = v___x_1687_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1677_ = stack[0].m_num;
size_t v_i_1678_ = stack[1].m_num;
lean_object* v_bs_1679_ = stack[2].m_obj;
lean_object* v_res_1689_;
v_res_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__1(v_sz_1677_, v_i_1678_, v_bs_1679_);
stack->m_obj
 = v_res_1689_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__1___boxed(lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_bs_1692_){
_start:
{
size_t v_sz_boxed_1693_; size_t v_i_boxed_1694_; lean_object* v_res_1695_; 
v_sz_boxed_1693_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1694_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__1(v_sz_boxed_1693_, v_i_boxed_1694_, v_bs_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(lean_object* v_x_1696_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = ((lean_object*)(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0));
return v___x_1697_;
}
else
{
lean_object* v_tail_1698_; 
v_tail_1698_ = lean_ctor_get(v_x_1696_, 1);
if (lean_obj_tag(v_tail_1698_) == 0)
{
lean_object* v_head_1699_; lean_object* v___x_1700_; 
v_head_1699_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_head_1699_);
lean_dec_ref_known(v_x_1696_, 2);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_head_1699_);
return v___x_1700_;
}
else
{
lean_object* v_head_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1710_; 
lean_inc(v_tail_1698_);
v_head_1701_ = lean_ctor_get(v_x_1696_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v_x_1696_, 1);
lean_dec(v_unused_1711_);
v___x_1703_ = v_x_1696_;
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_head_1701_);
lean_dec(v_x_1696_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_head_1701_);
v___x_1706_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v_tail_1698_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v___x_1706_);
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1708_ = v___x_1703_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2_spec__4(lean_object* v_ctx_1712_, lean_object* v_a_1713_){
_start:
{
if (lean_obj_tag(v_a_1713_) == 0)
{
return v_a_1713_;
}
else
{
lean_object* v_head_1714_; lean_object* v_tail_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1729_; 
v_head_1714_ = lean_ctor_get(v_a_1713_, 0);
v_tail_1715_ = lean_ctor_get(v_a_1713_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_a_1713_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1717_ = v_a_1713_;
v_isShared_1718_ = v_isSharedCheck_1729_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_tail_1715_);
lean_inc(v_head_1714_);
lean_dec(v_a_1713_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1729_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_snd_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v_snd_1719_ = lean_ctor_get(v_ctx_1712_, 1);
v___x_1720_ = 0;
v___x_1721_ = lean_box(v___x_1720_);
v___x_1722_ = lean_array_get(v___x_1721_, v_snd_1719_, v_head_1714_);
lean_dec(v___x_1721_);
v___x_1723_ = lean_unbox(v___x_1722_);
lean_dec(v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2_spec__4(v_ctx_1712_, v_tail_1715_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v___x_1724_);
v___x_1726_ = v___x_1717_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_head_1714_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
else
{
lean_del_object(v___x_1717_);
lean_dec(v_head_1714_);
v_a_1713_ = v_tail_1715_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2_spec__4___boxed(lean_object* v_ctx_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2_spec__4(v_ctx_1730_, v_a_1731_);
lean_dec_ref(v_ctx_1730_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2(lean_object* v_ctx_1733_, lean_object* v_x_1734_){
_start:
{
if (lean_obj_tag(v_x_1734_) == 0)
{
return v_x_1734_;
}
else
{
lean_object* v_head_1735_; lean_object* v___x_1736_; 
v_head_1735_ = lean_ctor_get(v_x_1734_, 0);
lean_inc(v_head_1735_);
v___x_1736_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2_spec__4(v_ctx_1733_, v_x_1734_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_head_1735_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
return v___x_1737_;
}
else
{
lean_dec(v_head_1735_);
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2___boxed(lean_object* v_ctx_1738_, lean_object* v_x_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2(v_ctx_1738_, v_x_1739_);
lean_dec_ref(v_ctx_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2(lean_object* v_ctx_1741_, lean_object* v_e_1742_){
_start:
{
lean_object* v_fst_1743_; lean_object* v_comm_1744_; lean_object* v_idem_1745_; lean_object* v___y_1747_; lean_object* v_xs_1749_; lean_object* v_xs_1750_; 
v_fst_1743_ = lean_ctor_get(v_ctx_1741_, 0);
v_comm_1744_ = lean_ctor_get(v_fst_1743_, 3);
v_idem_1745_ = lean_ctor_get(v_fst_1743_, 4);
v_xs_1749_ = l_Lean_Data_AC_Expr_toList(v_e_1742_);
v_xs_1750_ = l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2_spec__2(v_ctx_1741_, v_xs_1749_);
if (lean_obj_tag(v_comm_1744_) == 0)
{
v___y_1747_ = v_xs_1750_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Data_AC_sort(v_xs_1750_);
v___y_1747_ = v___x_1751_;
goto v___jp_1746_;
}
v___jp_1746_:
{
if (lean_obj_tag(v_idem_1745_) == 0)
{
return v___y_1747_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Data_AC_mergeIdem(v___y_1747_);
return v___x_1748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2___boxed(lean_object* v_ctx_1752_, lean_object* v_e_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2(v_ctx_1752_, v_e_1753_);
lean_dec_ref(v_e_1753_);
lean_dec_ref(v_ctx_1752_);
return v_res_1754_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(size_t v_sz_1755_, size_t v_i_1756_, lean_object* v_bs_1757_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_usize_dec_lt(v_i_1756_, v_sz_1755_);
if (v___x_1758_ == 0)
{
return v_bs_1757_;
}
else
{
lean_object* v_v_1759_; lean_object* v_snd_1760_; lean_object* v___x_1761_; lean_object* v_bs_x27_1762_; uint8_t v___y_1764_; 
v_v_1759_ = lean_array_uget_borrowed(v_bs_1757_, v_i_1756_);
v_snd_1760_ = lean_ctor_get(v_v_1759_, 1);
lean_inc(v_snd_1760_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v_bs_x27_1762_ = lean_array_uset(v_bs_1757_, v_i_1756_, v___x_1761_);
if (lean_obj_tag(v_snd_1760_) == 0)
{
uint8_t v___x_1770_; 
v___x_1770_ = 0;
v___y_1764_ = v___x_1770_;
goto v___jp_1763_;
}
else
{
lean_dec_ref_known(v_snd_1760_, 1);
v___y_1764_ = v___x_1758_;
goto v___jp_1763_;
}
v___jp_1763_:
{
size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1765_ = ((size_t)1ULL);
v___x_1766_ = lean_usize_add(v_i_1756_, v___x_1765_);
v___x_1767_ = lean_box(v___y_1764_);
v___x_1768_ = lean_array_uset(v_bs_x27_1762_, v_i_1756_, v___x_1767_);
v_i_1756_ = v___x_1766_;
v_bs_1757_ = v___x_1768_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1755_ = stack[0].m_num;
size_t v_i_1756_ = stack[1].m_num;
lean_object* v_bs_1757_ = stack[2].m_obj;
lean_object* v_res_1771_;
v_res_1771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(v_sz_1755_, v_i_1756_, v_bs_1757_);
stack->m_obj
 = v_res_1771_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0___boxed(lean_object* v_sz_1772_, lean_object* v_i_1773_, lean_object* v_bs_1774_){
_start:
{
size_t v_sz_boxed_1775_; size_t v_i_boxed_1776_; lean_object* v_res_1777_; 
v_sz_boxed_1775_ = lean_unbox_usize(v_sz_1772_);
lean_dec(v_sz_1772_);
v_i_boxed_1776_ = lean_unbox_usize(v_i_1773_);
lean_dec(v_i_1773_);
v_res_1777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(v_sz_boxed_1775_, v_i_boxed_1776_, v_bs_1774_);
return v_res_1777_;
}
}
static lean_object* _init_l_Lean_Meta_AC_buildNormProof___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_box(0);
v___x_1784_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___lam__0___closed__2));
v___x_1785_ = l_Lean_mkConst(v___x_1784_, v___x_1783_);
return v___x_1785_;
}
}
lean_object* l_Lean_Meta_AC_buildNormProof___lam__0(lean_object* v___x_1793_, lean_object* v_fst_1794_, lean_object* v_preContext_1795_, lean_object* v_snd_1796_, lean_object* v_varsData_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_array_get_borrowed(v___x_1793_, v_fst_1794_, v___x_1803_);
lean_inc(v___y_1801_);
lean_inc_ref(v___y_1800_);
lean_inc(v___y_1799_);
lean_inc_ref(v___y_1798_);
lean_inc(v___x_1804_);
v___x_1805_ = lean_infer_type(v___x_1804_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc_n(v_a_1806_, 2);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = l_Lean_Meta_getLevel(v_a_1806_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc_n(v_a_1808_, 2);
lean_dec_ref_known(v___x_1807_, 1);
lean_inc_ref(v_varsData_1797_);
lean_inc(v_a_1806_);
lean_inc_ref(v_preContext_1795_);
v___x_1809_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(v_preContext_1795_, v_a_1806_, v_a_1808_, v_varsData_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; size_t v_sz_1811_; size_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v_sz_1811_ = lean_array_size(v_varsData_1797_);
v___x_1812_ = ((size_t)0ULL);
lean_inc_ref(v_varsData_1797_);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(v_sz_1811_, v___x_1812_, v_varsData_1797_);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__1(v_sz_1811_, v___x_1812_, v_varsData_1797_);
lean_inc_ref(v_preContext_1795_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_preContext_1795_);
lean_ctor_set(v___x_1815_, 1, v___x_1813_);
v___x_1816_ = l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__2(v___x_1815_, v_snd_1796_);
lean_dec_ref_known(v___x_1815_, 2);
v___x_1817_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v___x_1816_);
lean_inc_ref(v_snd_1796_);
v___x_1818_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v_snd_1796_);
lean_inc_ref(v___x_1817_);
v___x_1819_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(v___x_1817_);
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_obj_once(&l_Lean_Meta_AC_buildNormProof___lam__0___closed__3, &l_Lean_Meta_AC_buildNormProof___lam__0___closed__3_once, _init_l_Lean_Meta_AC_buildNormProof___lam__0___closed__3);
v___x_1822_ = l_Lean_Meta_mkEqRefl(v___x_1821_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v___x_1824_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___lam__0___closed__5));
v___x_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_a_1808_);
lean_ctor_set(v___x_1825_, 1, v___x_1820_);
v___x_1826_ = l_Lean_mkConst(v___x_1824_, v___x_1825_);
v___x_1827_ = lean_unsigned_to_nat(5u);
v___x_1828_ = lean_mk_empty_array_with_capacity(v___x_1827_);
v___x_1829_ = lean_array_push(v___x_1828_, v_a_1806_);
v___x_1830_ = lean_array_push(v___x_1829_, v_a_1810_);
v___x_1831_ = lean_array_push(v___x_1830_, v___x_1818_);
v___x_1832_ = lean_array_push(v___x_1831_, v___x_1819_);
v___x_1833_ = lean_array_push(v___x_1832_, v_a_1823_);
v___x_1834_ = l_Lean_mkAppN(v___x_1826_, v___x_1833_);
lean_dec_ref(v___x_1833_);
lean_inc_ref(v_preContext_1795_);
v___x_1835_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1795_, v___x_1814_, v_snd_1796_);
lean_dec_ref(v_snd_1796_);
v___x_1836_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_1795_, v___x_1814_, v___x_1817_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___x_1814_);
v___x_1837_ = l_Lean_Meta_mkEq(v___x_1835_, v___x_1836_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1846_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = l_Lean_Meta_mkExpectedPropHint(v___x_1834_, v_a_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_dec_ref(v___x_1834_);
return v___x_1837_;
}
}
else
{
lean_dec_ref(v___x_1819_);
lean_dec_ref(v___x_1818_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___x_1814_);
lean_dec(v_a_1810_);
lean_dec(v_a_1808_);
lean_dec(v_a_1806_);
lean_dec_ref(v_snd_1796_);
lean_dec_ref(v_preContext_1795_);
return v___x_1822_;
}
}
else
{
lean_dec(v_a_1808_);
lean_dec(v_a_1806_);
lean_dec_ref(v_varsData_1797_);
lean_dec_ref(v_snd_1796_);
lean_dec_ref(v_preContext_1795_);
return v___x_1809_;
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_a_1806_);
lean_dec_ref(v_varsData_1797_);
lean_dec_ref(v_snd_1796_);
lean_dec_ref(v_preContext_1795_);
v_a_1847_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1807_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1807_);
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
else
{
lean_dec_ref(v_varsData_1797_);
lean_dec_ref(v_snd_1796_);
lean_dec_ref(v_preContext_1795_);
return v___x_1805_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_buildNormProof___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1793_ = stack[0].m_obj;
lean_object* v_fst_1794_ = stack[1].m_obj;
lean_object* v_preContext_1795_ = stack[2].m_obj;
lean_object* v_snd_1796_ = stack[3].m_obj;
lean_object* v_varsData_1797_ = stack[4].m_obj;
lean_object* v___y_1798_ = stack[5].m_obj;
lean_object* v___y_1799_ = stack[6].m_obj;
lean_object* v___y_1800_ = stack[7].m_obj;
lean_object* v___y_1801_ = stack[8].m_obj;
lean_object* v_res_1855_;
v_res_1855_ = l_Lean_Meta_AC_buildNormProof___lam__0(v___x_1793_, v_fst_1794_, v_preContext_1795_, v_snd_1796_, v_varsData_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
stack->m_obj
 = v_res_1855_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___lam__0___boxed(lean_object* v___x_1856_, lean_object* v_fst_1857_, lean_object* v_preContext_1858_, lean_object* v_snd_1859_, lean_object* v_varsData_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Meta_AC_buildNormProof___lam__0(v___x_1856_, v_fst_1857_, v_preContext_1858_, v_snd_1859_, v_varsData_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec_ref(v_fst_1857_);
lean_dec_ref(v___x_1856_);
return v_res_1866_;
}
}
static lean_object* _init_l_Lean_Meta_AC_buildNormProof___closed__5(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1873_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__4));
v___x_1874_ = lean_unsigned_to_nat(52u);
v___x_1875_ = lean_unsigned_to_nat(132u);
v___x_1876_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__3));
v___x_1877_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__2));
v___x_1878_ = l_mkPanicMessageWithDecl(v___x_1877_, v___x_1876_, v___x_1875_, v___x_1874_, v___x_1873_);
return v___x_1878_;
}
}
lean_object* l_Lean_Meta_AC_buildNormProof(lean_object* v_preContext_1879_, lean_object* v_l_1880_, lean_object* v_r_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_op_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_op_1887_ = lean_ctor_get(v_preContext_1879_, 1);
v___x_1888_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_op_1887_);
v___x_1889_ = l_Lean_Meta_AC_toACExpr(v_op_1887_, v_l_1880_, v_r_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v_fst_1891_; lean_object* v_snd_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1933_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
v_fst_1891_ = lean_ctor_get(v_a_1890_, 0);
v_snd_1892_ = lean_ctor_get(v_a_1890_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_a_1890_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1894_ = v_a_1890_;
v_isShared_1895_ = v_isSharedCheck_1933_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_snd_1892_);
lean_inc(v_fst_1891_);
lean_dec(v_a_1890_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1933_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___f_1896_; lean_object* v___x_1897_; 
lean_inc_ref(v_preContext_1879_);
lean_inc(v_fst_1891_);
v___f_1896_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_buildNormProof___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1896_, 0, v___x_1888_);
lean_closure_set(v___f_1896_, 1, v_fst_1891_);
lean_closure_set(v___f_1896_, 2, v_preContext_1879_);
lean_closure_set(v___f_1896_, 3, v_snd_1892_);
v___x_1897_ = l_Lean_Meta_AC_abstractAtoms(v_preContext_1879_, v_fst_1891_, v___f_1896_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc_n(v_a_1898_, 2);
lean_dec_ref_known(v___x_1897_, 1);
lean_inc(v_a_1885_);
lean_inc_ref(v_a_1884_);
lean_inc(v_a_1883_);
lean_inc_ref(v_a_1882_);
v___x_1899_ = lean_infer_type(v_a_1898_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1916_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1916_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1916_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1904_ = ((lean_object*)(l_Lean_Meta_AC_buildNormProof___closed__1));
v___x_1905_ = lean_unsigned_to_nat(3u);
v___x_1906_ = l_Lean_Expr_isAppOfArity(v_a_1900_, v___x_1904_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
lean_del_object(v___x_1902_);
lean_dec(v_a_1900_);
lean_dec(v_a_1898_);
lean_del_object(v___x_1894_);
v___x_1907_ = lean_obj_once(&l_Lean_Meta_AC_buildNormProof___closed__5, &l_Lean_Meta_AC_buildNormProof___closed__5_once, _init_l_Lean_Meta_AC_buildNormProof___closed__5);
v___x_1908_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(v___x_1907_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
return v___x_1908_;
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = l_Lean_Expr_appArg_x21(v_a_1900_);
lean_dec(v_a_1900_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1909_);
lean_ctor_set(v___x_1894_, 0, v_a_1898_);
v___x_1911_ = v___x_1894_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1898_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1913_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1911_);
v___x_1913_ = v___x_1902_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1898_);
lean_del_object(v___x_1894_);
v_a_1917_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1899_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1899_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
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
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_del_object(v___x_1894_);
v_a_1925_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1897_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1897_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref(v_preContext_1879_);
v_a_1934_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1889_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1889_);
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
LEAN_EXPORT void l_Lean_Meta_AC_buildNormProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_preContext_1879_ = stack[0].m_obj;
lean_object* v_l_1880_ = stack[1].m_obj;
lean_object* v_r_1881_ = stack[2].m_obj;
lean_object* v_a_1882_ = stack[3].m_obj;
lean_object* v_a_1883_ = stack[4].m_obj;
lean_object* v_a_1884_ = stack[5].m_obj;
lean_object* v_a_1885_ = stack[6].m_obj;
lean_object* v_res_1942_;
v_res_1942_ = l_Lean_Meta_AC_buildNormProof(v_preContext_1879_, v_l_1880_, v_r_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
stack->m_obj
 = v_res_1942_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_buildNormProof___boxed(lean_object* v_preContext_1943_, lean_object* v_l_1944_, lean_object* v_r_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_Meta_AC_buildNormProof(v_preContext_1943_, v_l_1944_, v_r_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3(lean_object* v_ctx_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v_x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___boxed(lean_object* v_ctx_1955_, lean_object* v_x_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3(v_ctx_1955_, v_x_1956_);
lean_dec_ref(v_ctx_1955_);
return v_res_1957_;
}
}
lean_object* l_Lean_Meta_AC_post___redArg(lean_object* v_e_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_e_1966_; lean_object* v_op_1973_; lean_object* v_l_1974_; lean_object* v_r_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; 
if (lean_obj_tag(v_e_1958_) == 5)
{
lean_object* v_fn_2031_; 
v_fn_2031_ = lean_ctor_get(v_e_1958_, 0);
if (lean_obj_tag(v_fn_2031_) == 5)
{
lean_object* v_parent_x3f_2032_; 
v_parent_x3f_2032_ = lean_ctor_get(v_a_1959_, 8);
if (lean_obj_tag(v_parent_x3f_2032_) == 1)
{
lean_object* v_val_2033_; 
v_val_2033_ = lean_ctor_get(v_parent_x3f_2032_, 0);
if (lean_obj_tag(v_val_2033_) == 5)
{
lean_object* v_fn_2034_; 
v_fn_2034_ = lean_ctor_get(v_val_2033_, 0);
if (lean_obj_tag(v_fn_2034_) == 5)
{
lean_object* v_arg_2035_; lean_object* v_fn_2036_; lean_object* v_arg_2037_; lean_object* v_fn_2038_; lean_object* v___x_2039_; 
v_arg_2035_ = lean_ctor_get(v_e_1958_, 1);
v_fn_2036_ = lean_ctor_get(v_fn_2031_, 0);
v_arg_2037_ = lean_ctor_get(v_fn_2031_, 1);
v_fn_2038_ = lean_ctor_get(v_fn_2034_, 0);
lean_inc_ref(v_fn_2038_);
lean_inc_ref(v_fn_2036_);
v___x_2039_ = l_Lean_Meta_isExprDefEq(v_fn_2036_, v_fn_2038_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2101_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2101_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2101_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
uint8_t v___x_2044_; uint8_t v___x_2045_; 
v___x_2044_ = 1;
v___x_2045_ = lean_unbox(v_a_2040_);
lean_dec(v_a_2040_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_del_object(v___x_2042_);
lean_inc_ref(v_fn_2036_);
v___x_2046_ = l_Lean_Meta_AC_preContext(v_fn_2036_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2086_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2086_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2086_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
if (lean_obj_tag(v_a_2047_) == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2052_, 0, v_e_1958_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*2, v___x_2044_);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2053_);
v___x_2055_ = v___x_2049_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
else
{
lean_object* v_val_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2085_; 
lean_inc_ref(v_arg_2037_);
lean_inc_ref(v_arg_2035_);
lean_del_object(v___x_2049_);
lean_dec_ref_known(v_e_1958_, 2);
v_val_2057_ = lean_ctor_get(v_a_2047_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_a_2047_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2059_ = v_a_2047_;
v_isShared_2060_ = v_isSharedCheck_2085_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_val_2057_);
lean_dec(v_a_2047_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2085_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Meta_AC_buildNormProof(v_val_2057_, v_arg_2037_, v_arg_2035_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2076_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2076_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2076_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_fst_2066_; lean_object* v_snd_2067_; lean_object* v___x_2069_; 
v_fst_2066_ = lean_ctor_get(v_a_2062_, 0);
lean_inc(v_fst_2066_);
v_snd_2067_ = lean_ctor_get(v_a_2062_, 1);
lean_inc(v_snd_2067_);
lean_dec(v_a_2062_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v_fst_2066_);
v___x_2069_ = v___x_2059_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_fst_2066_);
v___x_2069_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2070_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2070_, 0, v_snd_2067_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
lean_ctor_set_uint8(v___x_2070_, sizeof(void*)*2, v___x_2044_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2071_);
v___x_2073_ = v___x_2064_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_del_object(v___x_2059_);
v_a_2077_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2061_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2061_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref_known(v_e_1958_, 2);
v_a_2087_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2046_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2046_);
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
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2095_ = lean_box(0);
v___x_2096_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2096_, 0, v_e_1958_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*2, v___x_2044_);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2097_);
v___x_2099_ = v___x_2042_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec_ref_known(v_e_1958_, 2);
v_a_2102_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2039_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2039_);
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
lean_object* v_arg_2110_; lean_object* v_fn_2111_; lean_object* v_arg_2112_; 
v_arg_2110_ = lean_ctor_get(v_e_1958_, 1);
v_fn_2111_ = lean_ctor_get(v_fn_2031_, 0);
v_arg_2112_ = lean_ctor_get(v_fn_2031_, 1);
lean_inc_ref(v_arg_2110_);
lean_inc_ref(v_arg_2112_);
lean_inc_ref(v_fn_2111_);
v_op_1973_ = v_fn_2111_;
v_l_1974_ = v_arg_2112_;
v_r_1975_ = v_arg_2110_;
v___y_1976_ = v_a_1960_;
v___y_1977_ = v_a_1961_;
v___y_1978_ = v_a_1962_;
v___y_1979_ = v_a_1963_;
goto v___jp_1972_;
}
}
else
{
lean_object* v_arg_2113_; lean_object* v_fn_2114_; lean_object* v_arg_2115_; 
v_arg_2113_ = lean_ctor_get(v_e_1958_, 1);
v_fn_2114_ = lean_ctor_get(v_fn_2031_, 0);
v_arg_2115_ = lean_ctor_get(v_fn_2031_, 1);
lean_inc_ref(v_arg_2113_);
lean_inc_ref(v_arg_2115_);
lean_inc_ref(v_fn_2114_);
v_op_1973_ = v_fn_2114_;
v_l_1974_ = v_arg_2115_;
v_r_1975_ = v_arg_2113_;
v___y_1976_ = v_a_1960_;
v___y_1977_ = v_a_1961_;
v___y_1978_ = v_a_1962_;
v___y_1979_ = v_a_1963_;
goto v___jp_1972_;
}
}
else
{
lean_object* v_arg_2116_; lean_object* v_fn_2117_; lean_object* v_arg_2118_; 
v_arg_2116_ = lean_ctor_get(v_e_1958_, 1);
v_fn_2117_ = lean_ctor_get(v_fn_2031_, 0);
v_arg_2118_ = lean_ctor_get(v_fn_2031_, 1);
lean_inc_ref(v_arg_2116_);
lean_inc_ref(v_arg_2118_);
lean_inc_ref(v_fn_2117_);
v_op_1973_ = v_fn_2117_;
v_l_1974_ = v_arg_2118_;
v_r_1975_ = v_arg_2116_;
v___y_1976_ = v_a_1960_;
v___y_1977_ = v_a_1961_;
v___y_1978_ = v_a_1962_;
v___y_1979_ = v_a_1963_;
goto v___jp_1972_;
}
}
else
{
v_e_1966_ = v_e_1958_;
goto v___jp_1965_;
}
}
else
{
v_e_1966_ = v_e_1958_;
goto v___jp_1965_;
}
v___jp_1965_:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1967_ = lean_box(0);
v___x_1968_ = 1;
v___x_1969_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1969_, 0, v_e_1966_);
lean_ctor_set(v___x_1969_, 1, v___x_1967_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*2, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
v___jp_1972_:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Meta_AC_preContext(v_op_1973_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2022_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_2022_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2022_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
if (lean_obj_tag(v_a_1981_) == 0)
{
lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_dec_ref(v_r_1975_);
lean_dec_ref(v_l_1974_);
v___x_1985_ = lean_box(0);
v___x_1986_ = 1;
v___x_1987_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1987_, 0, v_e_1958_);
lean_ctor_set(v___x_1987_, 1, v___x_1985_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*2, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1988_);
v___x_1990_ = v___x_1983_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
else
{
lean_object* v_val_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2021_; 
lean_del_object(v___x_1983_);
lean_dec_ref(v_e_1958_);
v_val_1992_ = lean_ctor_get(v_a_1981_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_a_1981_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1994_ = v_a_1981_;
v_isShared_1995_ = v_isSharedCheck_2021_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_val_1992_);
lean_dec(v_a_1981_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2021_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Meta_AC_buildNormProof(v_val_1992_, v_l_1974_, v_r_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2012_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2012_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2012_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v_fst_2001_; lean_object* v_snd_2002_; lean_object* v___x_2004_; 
v_fst_2001_ = lean_ctor_get(v_a_1997_, 0);
lean_inc(v_fst_2001_);
v_snd_2002_ = lean_ctor_get(v_a_1997_, 1);
lean_inc(v_snd_2002_);
lean_dec(v_a_1997_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v_fst_2001_);
v___x_2004_ = v___x_1994_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_fst_2001_);
v___x_2004_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
uint8_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2005_ = 1;
v___x_2006_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2006_, 0, v_snd_2002_);
lean_ctor_set(v___x_2006_, 1, v___x_2004_);
lean_ctor_set_uint8(v___x_2006_, sizeof(void*)*2, v___x_2005_);
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2007_);
v___x_2009_ = v___x_1999_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_del_object(v___x_1994_);
v_a_2013_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1996_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1996_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_r_1975_);
lean_dec_ref(v_l_1974_);
lean_dec_ref(v_e_1958_);
v_a_2023_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1980_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1980_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
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
}
}
LEAN_EXPORT void l_Lean_Meta_AC_post___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1958_ = stack[0].m_obj;
lean_object* v_a_1959_ = stack[1].m_obj;
lean_object* v_a_1960_ = stack[2].m_obj;
lean_object* v_a_1961_ = stack[3].m_obj;
lean_object* v_a_1962_ = stack[4].m_obj;
lean_object* v_a_1963_ = stack[5].m_obj;
lean_object* v_res_2119_;
v_res_2119_ = l_Lean_Meta_AC_post___redArg(v_e_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
stack->m_obj
 = v_res_2119_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___redArg___boxed(lean_object* v_e_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_Meta_AC_post___redArg(v_e_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec_ref(v_a_2121_);
return v_res_2127_;
}
}
lean_object* l_Lean_Meta_AC_post(lean_object* v_e_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_Meta_AC_post___redArg(v_e_2128_, v_a_2130_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_post_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2128_ = stack[0].m_obj;
lean_object* v_a_2129_ = stack[1].m_obj;
lean_object* v_a_2130_ = stack[2].m_obj;
lean_object* v_a_2131_ = stack[3].m_obj;
lean_object* v_a_2132_ = stack[4].m_obj;
lean_object* v_a_2133_ = stack[5].m_obj;
lean_object* v_a_2134_ = stack[6].m_obj;
lean_object* v_a_2135_ = stack[7].m_obj;
lean_object* v_res_2138_;
v_res_2138_ = l_Lean_Meta_AC_post(v_e_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
stack->m_obj
 = v_res_2138_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_post___boxed(lean_object* v_e_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Meta_AC_post(v_e_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
return v_res_2148_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(lean_object* v_e_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = l_Lean_Expr_hasMVar(v_e_2149_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_e_2149_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; lean_object* v_mctx_2155_; lean_object* v___x_2156_; lean_object* v_fst_2157_; lean_object* v_snd_2158_; lean_object* v___x_2159_; lean_object* v_cache_2160_; lean_object* v_zetaDeltaFVarIds_2161_; lean_object* v_postponed_2162_; lean_object* v_diag_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2172_; 
v___x_2154_ = lean_st_ref_get(v___y_2150_);
v_mctx_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc_ref(v_mctx_2155_);
lean_dec(v___x_2154_);
v___x_2156_ = l_Lean_instantiateMVarsCore(v_mctx_2155_, v_e_2149_);
v_fst_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_fst_2157_);
v_snd_2158_ = lean_ctor_get(v___x_2156_, 1);
lean_inc(v_snd_2158_);
lean_dec_ref(v___x_2156_);
v___x_2159_ = lean_st_ref_take(v___y_2150_);
v_cache_2160_ = lean_ctor_get(v___x_2159_, 1);
v_zetaDeltaFVarIds_2161_ = lean_ctor_get(v___x_2159_, 2);
v_postponed_2162_ = lean_ctor_get(v___x_2159_, 3);
v_diag_2163_ = lean_ctor_get(v___x_2159_, 4);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; 
v_unused_2173_ = lean_ctor_get(v___x_2159_, 0);
lean_dec(v_unused_2173_);
v___x_2165_ = v___x_2159_;
v_isShared_2166_ = v_isSharedCheck_2172_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_diag_2163_);
lean_inc(v_postponed_2162_);
lean_inc(v_zetaDeltaFVarIds_2161_);
lean_inc(v_cache_2160_);
lean_dec(v___x_2159_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2172_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v_snd_2158_);
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_snd_2158_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_cache_2160_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_zetaDeltaFVarIds_2161_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_postponed_2162_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v_diag_2163_);
v___x_2168_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = lean_st_ref_put(v___y_2150_, v___x_2168_);
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v_fst_2157_);
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2149_ = stack[0].m_obj;
lean_object* v___y_2150_ = stack[1].m_obj;
lean_object* v_res_2174_;
v_res_2174_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_e_2149_, v___y_2150_);
stack->m_obj
 = v_res_2174_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg___boxed(lean_object* v_e_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_e_2175_, v___y_2176_);
lean_dec(v___y_2176_);
return v_res_2178_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(lean_object* v_e_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_e_2179_, v___y_2181_);
return v___x_2185_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2179_ = stack[0].m_obj;
lean_object* v___y_2180_ = stack[1].m_obj;
lean_object* v___y_2181_ = stack[2].m_obj;
lean_object* v___y_2182_ = stack[3].m_obj;
lean_object* v___y_2183_ = stack[4].m_obj;
lean_object* v_res_2186_;
v_res_2186_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(v_e_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
stack->m_obj
 = v_res_2186_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___boxed(lean_object* v_e_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(v_e_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
return v_res_2193_;
}
}
lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__0(lean_object* v_x_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0));
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_rewriteUnnormalized___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2196_ = stack[0].m_obj;
lean_object* v___y_2197_ = stack[1].m_obj;
lean_object* v___y_2198_ = stack[2].m_obj;
lean_object* v___y_2199_ = stack[3].m_obj;
lean_object* v___y_2200_ = stack[4].m_obj;
lean_object* v___y_2201_ = stack[5].m_obj;
lean_object* v___y_2202_ = stack[6].m_obj;
lean_object* v___y_2203_ = stack[7].m_obj;
lean_object* v_res_2207_;
v_res_2207_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__0(v_x_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
stack->m_obj
 = v_res_2207_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__0___boxed(lean_object* v_x_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__0(v_x_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v_x_2208_);
return v_res_2217_;
}
}
lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__1(lean_object* v_x_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0));
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_rewriteUnnormalized___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2220_ = stack[0].m_obj;
lean_object* v___y_2221_ = stack[1].m_obj;
lean_object* v___y_2222_ = stack[2].m_obj;
lean_object* v___y_2223_ = stack[3].m_obj;
lean_object* v___y_2224_ = stack[4].m_obj;
lean_object* v___y_2225_ = stack[5].m_obj;
lean_object* v___y_2226_ = stack[6].m_obj;
lean_object* v___y_2227_ = stack[7].m_obj;
lean_object* v_res_2231_;
v_res_2231_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__1(v_x_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
stack->m_obj
 = v_res_2231_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__1___boxed(lean_object* v_x_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__1(v_x_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v_x_2232_);
return v_res_2241_;
}
}
lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__2(lean_object* v_e_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_e_2242_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_rewriteUnnormalized___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2242_ = stack[0].m_obj;
lean_object* v___y_2243_ = stack[1].m_obj;
lean_object* v___y_2244_ = stack[2].m_obj;
lean_object* v___y_2245_ = stack[3].m_obj;
lean_object* v___y_2246_ = stack[4].m_obj;
lean_object* v___y_2247_ = stack[5].m_obj;
lean_object* v___y_2248_ = stack[6].m_obj;
lean_object* v___y_2249_ = stack[7].m_obj;
lean_object* v_res_2253_;
v_res_2253_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__2(v_e_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
stack->m_obj
 = v_res_2253_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__2___boxed(lean_object* v_e_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__2(v_e_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
return v_res_2263_;
}
}
lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__3(lean_object* v_x_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_rewriteUnnormalized___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2264_ = stack[0].m_obj;
lean_object* v___y_2265_ = stack[1].m_obj;
lean_object* v___y_2266_ = stack[2].m_obj;
lean_object* v___y_2267_ = stack[3].m_obj;
lean_object* v___y_2268_ = stack[4].m_obj;
lean_object* v___y_2269_ = stack[5].m_obj;
lean_object* v___y_2270_ = stack[6].m_obj;
lean_object* v___y_2271_ = stack[7].m_obj;
lean_object* v_res_2275_;
v_res_2275_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__3(v_x_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
stack->m_obj
 = v_res_2275_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___lam__3___boxed(lean_object* v_x_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__3(v_x_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v_x_2276_);
return v_res_2285_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__5(void){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__5, &l_Lean_Meta_AC_rewriteUnnormalized___closed__5_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__5);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__7(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__6, &l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v___x_2295_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__8(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_unsigned_to_nat(32u);
v___x_2299_ = lean_mk_empty_array_with_capacity(v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__9(void){
_start:
{
size_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = ((size_t)5ULL);
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = lean_unsigned_to_nat(32u);
v___x_2304_ = lean_mk_empty_array_with_capacity(v___x_2303_);
v___x_2305_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__8, &l_Lean_Meta_AC_rewriteUnnormalized___closed__8_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__8);
v___x_2306_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___x_2304_);
lean_ctor_set(v___x_2306_, 2, v___x_2302_);
lean_ctor_set(v___x_2306_, 3, v___x_2302_);
lean_ctor_set_usize(v___x_2306_, 4, v___x_2301_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__10(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__9, &l_Lean_Meta_AC_rewriteUnnormalized___closed__9_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__9);
v___x_2308_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__6, &l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6);
v___x_2309_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
lean_ctor_set(v___x_2309_, 2, v___x_2308_);
lean_ctor_set(v___x_2309_, 3, v___x_2307_);
return v___x_2309_;
}
}
static lean_object* _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__10, &l_Lean_Meta_AC_rewriteUnnormalized___closed__10_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__10);
v___x_2311_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__7, &l_Lean_Meta_AC_rewriteUnnormalized___closed__7_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__7);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___x_2310_);
return v___x_2312_;
}
}
lean_object* l_Lean_Meta_AC_rewriteUnnormalized(lean_object* v_mvarId_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_2325_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = l_Lean_Meta_Simp_neutralConfig;
v___x_2330_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__4));
v___x_2331_ = l_Lean_Options_empty;
v___x_2332_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2329_, v___x_2330_, v_a_2328_, v___x_2331_, v_a_2322_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
lean_inc(v_mvarId_2321_);
v___x_2334_ = l_Lean_MVarId_getType(v_mvarId_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v_a_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_a_2335_, v_a_2323_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc_n(v_a_2337_, 2);
lean_dec_ref(v___x_2336_);
v___x_2338_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__11, &l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11);
v___x_2339_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__13));
v___x_2340_ = l_Lean_Meta_Simp_main(v_a_2337_, v_a_2333_, v___x_2338_, v___x_2339_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v_fst_2342_; lean_object* v___x_2343_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v_fst_2342_ = lean_ctor_get(v_a_2341_, 0);
lean_inc(v_fst_2342_);
lean_dec(v_a_2341_);
v___x_2343_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_2321_, v_a_2337_, v_fst_2342_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
lean_dec(v_a_2337_);
return v___x_2343_;
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_a_2337_);
lean_dec(v_mvarId_2321_);
v_a_2344_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2340_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2340_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_a_2333_);
lean_dec(v_mvarId_2321_);
v_a_2352_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2334_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2334_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_mvarId_2321_);
v_a_2360_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2332_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2332_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_mvarId_2321_);
v_a_2368_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2327_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2327_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_rewriteUnnormalized_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2321_ = stack[0].m_obj;
lean_object* v_a_2322_ = stack[1].m_obj;
lean_object* v_a_2323_ = stack[2].m_obj;
lean_object* v_a_2324_ = stack[3].m_obj;
lean_object* v_a_2325_ = stack[4].m_obj;
lean_object* v_res_2376_;
v_res_2376_ = l_Lean_Meta_AC_rewriteUnnormalized(v_mvarId_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
stack->m_obj
 = v_res_2376_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalized___boxed(lean_object* v_mvarId_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Meta_AC_rewriteUnnormalized(v_mvarId_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
return v_res_2383_;
}
}
lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object* v_goal_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_Meta_AC_rewriteUnnormalized(v_goal_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = 1;
v___x_2393_ = l_Lean_MVarId_refl(v_a_2391_, v___x_2392_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
return v___x_2393_;
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
v_a_2394_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2390_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2390_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_rewriteUnnormalizedRefl_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2384_ = stack[0].m_obj;
lean_object* v_a_2385_ = stack[1].m_obj;
lean_object* v_a_2386_ = stack[2].m_obj;
lean_object* v_a_2387_ = stack[3].m_obj;
lean_object* v_a_2388_ = stack[4].m_obj;
lean_object* v_res_2402_;
v_res_2402_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v_goal_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
stack->m_obj
 = v_res_2402_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl___boxed(lean_object* v_goal_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v_goal_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
return v_res_2409_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
lean_inc(v___y_2414_);
lean_inc_ref(v___y_2413_);
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
v___x_2420_ = lean_apply_9(v_x_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, lean_box(0));
return v___x_2420_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2410_ = stack[0].m_obj;
lean_object* v___y_2411_ = stack[1].m_obj;
lean_object* v___y_2412_ = stack[2].m_obj;
lean_object* v___y_2413_ = stack[3].m_obj;
lean_object* v___y_2414_ = stack[4].m_obj;
lean_object* v___y_2415_ = stack[5].m_obj;
lean_object* v___y_2416_ = stack[6].m_obj;
lean_object* v___y_2417_ = stack[7].m_obj;
lean_object* v___y_2418_ = stack[8].m_obj;
lean_object* v_res_2421_;
v_res_2421_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(v_x_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
stack->m_obj
 = v_res_2421_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0___boxed(lean_object* v_x_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(v_x_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2432_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(lean_object* v_mvarId_2433_, lean_object* v_x_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___f_2444_; lean_object* v___x_2445_; 
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
lean_inc(v___y_2436_);
lean_inc_ref(v___y_2435_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2444_, 0, v_x_2434_);
lean_closure_set(v___f_2444_, 1, v___y_2435_);
lean_closure_set(v___f_2444_, 2, v___y_2436_);
lean_closure_set(v___f_2444_, 3, v___y_2437_);
lean_closure_set(v___f_2444_, 4, v___y_2438_);
v___x_2445_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2433_, v___f_2444_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2445_) == 0)
{
return v___x_2445_;
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2433_ = stack[0].m_obj;
lean_object* v_x_2434_ = stack[1].m_obj;
lean_object* v___y_2435_ = stack[2].m_obj;
lean_object* v___y_2436_ = stack[3].m_obj;
lean_object* v___y_2437_ = stack[4].m_obj;
lean_object* v___y_2438_ = stack[5].m_obj;
lean_object* v___y_2439_ = stack[6].m_obj;
lean_object* v___y_2440_ = stack[7].m_obj;
lean_object* v___y_2441_ = stack[8].m_obj;
lean_object* v___y_2442_ = stack[9].m_obj;
lean_object* v_res_2454_;
v_res_2454_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_mvarId_2433_, v_x_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
stack->m_obj
 = v_res_2454_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___boxed(lean_object* v_mvarId_2455_, lean_object* v_x_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_mvarId_2455_, v_x_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
return v_res_2466_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(lean_object* v_00_u03b1_2467_, lean_object* v_mvarId_2468_, lean_object* v_x_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_mvarId_2468_, v_x_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
return v___x_2479_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2468_ = stack[1].m_obj;
lean_object* v_x_2469_ = stack[2].m_obj;
lean_object* v___y_2470_ = stack[3].m_obj;
lean_object* v___y_2471_ = stack[4].m_obj;
lean_object* v___y_2472_ = stack[5].m_obj;
lean_object* v___y_2473_ = stack[6].m_obj;
lean_object* v___y_2474_ = stack[7].m_obj;
lean_object* v___y_2475_ = stack[8].m_obj;
lean_object* v___y_2476_ = stack[9].m_obj;
lean_object* v___y_2477_ = stack[10].m_obj;
lean_object* v_res_2480_;
v_res_2480_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(lean_box(0), v_mvarId_2468_, v_x_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
stack->m_obj
 = v_res_2480_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___boxed(lean_object* v_00_u03b1_2481_, lean_object* v_mvarId_2482_, lean_object* v_x_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(v_00_u03b1_2481_, v_mvarId_2482_, v_x_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
return v_res_2493_;
}
}
lean_object* l_Lean_Meta_AC_acRflTactic___redArg___lam__0(lean_object* v_a_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v_a_2494_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
return v___x_2504_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_acRflTactic___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2494_ = stack[0].m_obj;
lean_object* v___y_2495_ = stack[1].m_obj;
lean_object* v___y_2496_ = stack[2].m_obj;
lean_object* v___y_2497_ = stack[3].m_obj;
lean_object* v___y_2498_ = stack[4].m_obj;
lean_object* v___y_2499_ = stack[5].m_obj;
lean_object* v___y_2500_ = stack[6].m_obj;
lean_object* v___y_2501_ = stack[7].m_obj;
lean_object* v___y_2502_ = stack[8].m_obj;
lean_object* v_res_2505_;
v_res_2505_ = l_Lean_Meta_AC_acRflTactic___redArg___lam__0(v_a_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
stack->m_obj
 = v_res_2505_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___lam__0___boxed(lean_object* v_a_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Meta_AC_acRflTactic___redArg___lam__0(v_a_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
return v_res_2516_;
}
}
lean_object* l_Lean_Meta_AC_acRflTactic___redArg(lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_2518_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___f_2528_; lean_object* v___x_2529_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc_n(v_a_2527_, 2);
lean_dec_ref_known(v___x_2526_, 1);
v___f_2528_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acRflTactic___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2528_, 0, v_a_2527_);
v___x_2529_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_a_2527_, v___f_2528_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
return v___x_2529_;
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
v_a_2530_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2526_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2526_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_acRflTactic___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2517_ = stack[0].m_obj;
lean_object* v_a_2518_ = stack[1].m_obj;
lean_object* v_a_2519_ = stack[2].m_obj;
lean_object* v_a_2520_ = stack[3].m_obj;
lean_object* v_a_2521_ = stack[4].m_obj;
lean_object* v_a_2522_ = stack[5].m_obj;
lean_object* v_a_2523_ = stack[6].m_obj;
lean_object* v_a_2524_ = stack[7].m_obj;
lean_object* v_res_2538_;
v_res_2538_ = l_Lean_Meta_AC_acRflTactic___redArg(v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
stack->m_obj
 = v_res_2538_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___redArg___boxed(lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Meta_AC_acRflTactic___redArg(v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
return v_res_2548_;
}
}
lean_object* l_Lean_Meta_AC_acRflTactic(lean_object* v_x_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Meta_AC_acRflTactic___redArg(v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
return v___x_2559_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_acRflTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2549_ = stack[0].m_obj;
lean_object* v_a_2550_ = stack[1].m_obj;
lean_object* v_a_2551_ = stack[2].m_obj;
lean_object* v_a_2552_ = stack[3].m_obj;
lean_object* v_a_2553_ = stack[4].m_obj;
lean_object* v_a_2554_ = stack[5].m_obj;
lean_object* v_a_2555_ = stack[6].m_obj;
lean_object* v_a_2556_ = stack[7].m_obj;
lean_object* v_a_2557_ = stack[8].m_obj;
lean_object* v_res_2560_;
v_res_2560_ = l_Lean_Meta_AC_acRflTactic(v_x_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
stack->m_obj
 = v_res_2560_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acRflTactic___boxed(lean_object* v_x_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Meta_AC_acRflTactic(v_x_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_x_2561_);
return v_res_2571_;
}
}
lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1(){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2587_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3));
v___x_2589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5));
v___x_2590_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acRflTactic___boxed), 10, 0);
v___x_2591_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2587_, v___x_2588_, v___x_2589_, v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2592_;
v_res_2592_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
stack->m_obj
 = v_res_2592_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___boxed(lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
return v_res_2594_;
}
}
lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3(){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5));
v___x_2622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6));
v___x_2623_ = l_Lean_addBuiltinDeclarationRanges(v___x_2621_, v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2624_;
v_res_2624_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
stack->m_obj
 = v_res_2624_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___boxed(lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
return v_res_2626_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(lean_object* v_mvarId_2627_, lean_object* v_x_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2627_, v_x_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
v_a_2643_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2634_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2634_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2627_ = stack[0].m_obj;
lean_object* v_x_2628_ = stack[1].m_obj;
lean_object* v___y_2629_ = stack[2].m_obj;
lean_object* v___y_2630_ = stack[3].m_obj;
lean_object* v___y_2631_ = stack[4].m_obj;
lean_object* v___y_2632_ = stack[5].m_obj;
lean_object* v_res_2651_;
v_res_2651_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_mvarId_2627_, v_x_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
stack->m_obj
 = v_res_2651_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg___boxed(lean_object* v_mvarId_2652_, lean_object* v_x_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_mvarId_2652_, v_x_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
return v_res_2659_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(lean_object* v_00_u03b1_2660_, lean_object* v_mvarId_2661_, lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_mvarId_2661_, v_x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2661_ = stack[1].m_obj;
lean_object* v_x_2662_ = stack[2].m_obj;
lean_object* v___y_2663_ = stack[3].m_obj;
lean_object* v___y_2664_ = stack[4].m_obj;
lean_object* v___y_2665_ = stack[5].m_obj;
lean_object* v___y_2666_ = stack[6].m_obj;
lean_object* v_res_2669_;
v_res_2669_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(lean_box(0), v_mvarId_2661_, v_x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
stack->m_obj
 = v_res_2669_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___boxed(lean_object* v_00_u03b1_2670_, lean_object* v_mvarId_2671_, lean_object* v_x_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(v_00_u03b1_2670_, v_mvarId_2671_, v_x_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
return v_res_2678_;
}
}
lean_object* l_Lean_Meta_AC_acNfHypMeta___lam__4(lean_object* v_fvarId_2679_, lean_object* v___f_2680_, lean_object* v___f_2681_, lean_object* v___f_2682_, lean_object* v___f_2683_, lean_object* v_goal_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2688_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
v___x_2692_ = l_Lean_Meta_Simp_neutralConfig;
v___x_2693_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__4));
v___x_2694_ = l_Lean_Options_empty;
v___x_2695_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2692_, v___x_2693_, v_a_2691_, v___x_2694_, v___y_2685_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
lean_inc(v_fvarId_2679_);
v___x_2697_ = l_Lean_FVarId_getType___redArg(v_fvarId_2679_, v___y_2685_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; lean_object* v_a_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_a_2698_, v___y_2686_);
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2699_);
v___x_2701_ = lean_unsigned_to_nat(32u);
v___x_2702_ = lean_mk_empty_array_with_capacity(v___x_2701_);
lean_dec_ref(v___x_2702_);
v___x_2703_ = lean_obj_once(&l_Lean_Meta_AC_rewriteUnnormalized___closed__11, &l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once, _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11);
v___x_2704_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__12));
v___x_2705_ = 1;
v___x_2706_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2706_, 0, v___f_2680_);
lean_ctor_set(v___x_2706_, 1, v___x_2704_);
lean_ctor_set(v___x_2706_, 2, v___f_2681_);
lean_ctor_set(v___x_2706_, 3, v___f_2682_);
lean_ctor_set(v___x_2706_, 4, v___f_2683_);
lean_ctor_set_uint8(v___x_2706_, sizeof(void*)*5, v___x_2705_);
v___x_2707_ = l_Lean_Meta_Simp_main(v_a_2700_, v_a_2696_, v___x_2703_, v___x_2706_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v_fst_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
v_fst_2709_ = lean_ctor_get(v_a_2708_, 0);
lean_inc(v_fst_2709_);
lean_dec(v_a_2708_);
v___x_2710_ = 0;
v___x_2711_ = l_Lean_Meta_applySimpResultToLocalDecl(v_goal_2684_, v_fvarId_2679_, v_fst_2709_, v___x_2710_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2732_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2732_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2732_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
if (lean_obj_tag(v_a_2712_) == 0)
{
lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2716_ = lean_box(0);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2716_);
v___x_2718_ = v___x_2714_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
else
{
lean_object* v_val_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2731_; 
v_val_2720_ = lean_ctor_get(v_a_2712_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_a_2712_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2722_ = v_a_2712_;
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_val_2720_);
lean_dec(v_a_2712_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v_snd_2724_; lean_object* v___x_2726_; 
v_snd_2724_ = lean_ctor_get(v_val_2720_, 1);
lean_inc(v_snd_2724_);
lean_dec(v_val_2720_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v_snd_2724_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_snd_2724_);
v___x_2726_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2728_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2726_);
v___x_2728_ = v___x_2714_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
v_a_2733_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2711_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2711_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_goal_2684_);
lean_dec(v_fvarId_2679_);
v_a_2741_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2707_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2707_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v_a_2696_);
lean_dec(v_goal_2684_);
lean_dec_ref(v___f_2683_);
lean_dec_ref(v___f_2682_);
lean_dec_ref(v___f_2681_);
lean_dec_ref(v___f_2680_);
lean_dec(v_fvarId_2679_);
v_a_2749_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2697_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2697_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_goal_2684_);
lean_dec_ref(v___f_2683_);
lean_dec_ref(v___f_2682_);
lean_dec_ref(v___f_2681_);
lean_dec_ref(v___f_2680_);
lean_dec(v_fvarId_2679_);
v_a_2757_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2695_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2695_);
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
lean_dec(v_goal_2684_);
lean_dec_ref(v___f_2683_);
lean_dec_ref(v___f_2682_);
lean_dec_ref(v___f_2681_);
lean_dec_ref(v___f_2680_);
lean_dec(v_fvarId_2679_);
v_a_2765_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2690_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2690_);
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
LEAN_EXPORT void l_Lean_Meta_AC_acNfHypMeta___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2679_ = stack[0].m_obj;
lean_object* v___f_2680_ = stack[1].m_obj;
lean_object* v___f_2681_ = stack[2].m_obj;
lean_object* v___f_2682_ = stack[3].m_obj;
lean_object* v___f_2683_ = stack[4].m_obj;
lean_object* v_goal_2684_ = stack[5].m_obj;
lean_object* v___y_2685_ = stack[6].m_obj;
lean_object* v___y_2686_ = stack[7].m_obj;
lean_object* v___y_2687_ = stack[8].m_obj;
lean_object* v___y_2688_ = stack[9].m_obj;
lean_object* v_res_2773_;
v_res_2773_ = l_Lean_Meta_AC_acNfHypMeta___lam__4(v_fvarId_2679_, v___f_2680_, v___f_2681_, v___f_2682_, v___f_2683_, v_goal_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
stack->m_obj
 = v_res_2773_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___lam__4___boxed(lean_object* v_fvarId_2774_, lean_object* v___f_2775_, lean_object* v___f_2776_, lean_object* v___f_2777_, lean_object* v___f_2778_, lean_object* v_goal_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Meta_AC_acNfHypMeta___lam__4(v_fvarId_2774_, v___f_2775_, v___f_2776_, v___f_2777_, v___f_2778_, v_goal_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
return v_res_2785_;
}
}
lean_object* l_Lean_Meta_AC_acNfHypMeta(lean_object* v_goal_2786_, lean_object* v_fvarId_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___f_2793_; lean_object* v___f_2794_; lean_object* v___f_2795_; lean_object* v___f_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; 
v___f_2793_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__3));
v___f_2794_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__2));
v___f_2795_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__1));
v___f_2796_ = ((lean_object*)(l_Lean_Meta_AC_rewriteUnnormalized___closed__0));
lean_inc(v_goal_2786_);
v___f_2797_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acNfHypMeta___lam__4___boxed), 11, 6);
lean_closure_set(v___f_2797_, 0, v_fvarId_2787_);
lean_closure_set(v___f_2797_, 1, v___f_2796_);
lean_closure_set(v___f_2797_, 2, v___f_2795_);
lean_closure_set(v___f_2797_, 3, v___f_2794_);
lean_closure_set(v___f_2797_, 4, v___f_2793_);
lean_closure_set(v___f_2797_, 5, v_goal_2786_);
v___x_2798_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(v_goal_2786_, v___f_2797_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
return v___x_2798_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_acNfHypMeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2786_ = stack[0].m_obj;
lean_object* v_fvarId_2787_ = stack[1].m_obj;
lean_object* v_a_2788_ = stack[2].m_obj;
lean_object* v_a_2789_ = stack[3].m_obj;
lean_object* v_a_2790_ = stack[4].m_obj;
lean_object* v_a_2791_ = stack[5].m_obj;
lean_object* v_res_2799_;
v_res_2799_ = l_Lean_Meta_AC_acNfHypMeta(v_goal_2786_, v_fvarId_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
stack->m_obj
 = v_res_2799_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypMeta___boxed(lean_object* v_goal_2800_, lean_object* v_fvarId_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Meta_AC_acNfHypMeta(v_goal_2800_, v_fvarId_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
return v_res_2807_;
}
}
lean_object* l_Lean_Meta_AC_acNfTargetTactic___lam__0(lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2809_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2819_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
v___x_2819_ = l_Lean_Meta_AC_rewriteUnnormalized(v_a_2818_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = lean_box(0);
v___x_2822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2820_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2822_, v___y_2809_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2823_;
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
v_a_2824_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2819_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2819_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v_a_2832_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2817_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2817_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_acNfTargetTactic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2808_ = stack[0].m_obj;
lean_object* v___y_2809_ = stack[1].m_obj;
lean_object* v___y_2810_ = stack[2].m_obj;
lean_object* v___y_2811_ = stack[3].m_obj;
lean_object* v___y_2812_ = stack[4].m_obj;
lean_object* v___y_2813_ = stack[5].m_obj;
lean_object* v___y_2814_ = stack[6].m_obj;
lean_object* v___y_2815_ = stack[7].m_obj;
lean_object* v_res_2840_;
v_res_2840_ = l_Lean_Meta_AC_acNfTargetTactic___lam__0(v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
stack->m_obj
 = v_res_2840_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___lam__0___boxed(lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_Meta_AC_acNfTargetTactic___lam__0(v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
return v_res_2850_;
}
}
lean_object* l_Lean_Meta_AC_acNfTargetTactic(lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v___f_2861_; lean_object* v___x_2862_; 
v___f_2861_ = ((lean_object*)(l_Lean_Meta_AC_acNfTargetTactic___closed__0));
v___x_2862_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2861_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
return v___x_2862_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_acNfTargetTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2852_ = stack[0].m_obj;
lean_object* v_a_2853_ = stack[1].m_obj;
lean_object* v_a_2854_ = stack[2].m_obj;
lean_object* v_a_2855_ = stack[3].m_obj;
lean_object* v_a_2856_ = stack[4].m_obj;
lean_object* v_a_2857_ = stack[5].m_obj;
lean_object* v_a_2858_ = stack[6].m_obj;
lean_object* v_a_2859_ = stack[7].m_obj;
lean_object* v_res_2863_;
v_res_2863_ = l_Lean_Meta_AC_acNfTargetTactic(v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
stack->m_obj
 = v_res_2863_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfTargetTactic___boxed(lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Meta_AC_acNfTargetTactic(v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
return v_res_2873_;
}
}
lean_object* l_Lean_Meta_AC_acNfHypTactic___lam__0(lean_object* v_fvarId_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2876_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2886_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2886_ = l_Lean_Meta_AC_acNfHypMeta(v_a_2885_, v_fvarId_2874_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
if (lean_obj_tag(v_a_2887_) == 1)
{
lean_object* v_val_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_val_2888_ = lean_ctor_get(v_a_2887_, 0);
lean_inc(v_val_2888_);
lean_dec_ref_known(v_a_2887_, 1);
v___x_2889_ = lean_box(0);
v___x_2890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2890_, 0, v_val_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2890_, v___y_2876_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
lean_dec(v_a_2887_);
v___x_2892_ = lean_box(0);
v___x_2893_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2892_, v___y_2876_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
return v___x_2893_;
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_a_2894_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2886_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2886_);
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
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_fvarId_2874_);
v_a_2902_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2884_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2884_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_acNfHypTactic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2874_ = stack[0].m_obj;
lean_object* v___y_2875_ = stack[1].m_obj;
lean_object* v___y_2876_ = stack[2].m_obj;
lean_object* v___y_2877_ = stack[3].m_obj;
lean_object* v___y_2878_ = stack[4].m_obj;
lean_object* v___y_2879_ = stack[5].m_obj;
lean_object* v___y_2880_ = stack[6].m_obj;
lean_object* v___y_2881_ = stack[7].m_obj;
lean_object* v___y_2882_ = stack[8].m_obj;
lean_object* v_res_2910_;
v_res_2910_ = l_Lean_Meta_AC_acNfHypTactic___lam__0(v_fvarId_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
stack->m_obj
 = v_res_2910_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___lam__0___boxed(lean_object* v_fvarId_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_Meta_AC_acNfHypTactic___lam__0(v_fvarId_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
return v_res_2921_;
}
}
lean_object* l_Lean_Meta_AC_acNfHypTactic(lean_object* v_fvarId_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v___f_2932_; lean_object* v___x_2933_; 
v___f_2932_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_acNfHypTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2932_, 0, v_fvarId_2922_);
v___x_2933_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2932_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_);
return v___x_2933_;
}
}
LEAN_EXPORT void l_Lean_Meta_AC_acNfHypTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2922_ = stack[0].m_obj;
lean_object* v_a_2923_ = stack[1].m_obj;
lean_object* v_a_2924_ = stack[2].m_obj;
lean_object* v_a_2925_ = stack[3].m_obj;
lean_object* v_a_2926_ = stack[4].m_obj;
lean_object* v_a_2927_ = stack[5].m_obj;
lean_object* v_a_2928_ = stack[6].m_obj;
lean_object* v_a_2929_ = stack[7].m_obj;
lean_object* v_a_2930_ = stack[8].m_obj;
lean_object* v_res_2934_;
v_res_2934_ = l_Lean_Meta_AC_acNfHypTactic(v_fvarId_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_);
stack->m_obj
 = v_res_2934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_acNfHypTactic___boxed(lean_object* v_fvarId_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Meta_AC_acNfHypTactic(v_fvarId_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
return v_res_2945_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = lean_box(0);
v___x_2947_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v___x_2946_);
return v___x_2948_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg(){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2952_;
v_res_2952_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
stack->m_obj
 = v_res_2952_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___boxed(lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v_res_2954_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(lean_object* v_00_u03b1_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v___x_2965_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2956_ = stack[1].m_obj;
lean_object* v___y_2957_ = stack[2].m_obj;
lean_object* v___y_2958_ = stack[3].m_obj;
lean_object* v___y_2959_ = stack[4].m_obj;
lean_object* v___y_2960_ = stack[5].m_obj;
lean_object* v___y_2961_ = stack[6].m_obj;
lean_object* v___y_2962_ = stack[7].m_obj;
lean_object* v___y_2963_ = stack[8].m_obj;
lean_object* v_res_2966_;
v_res_2966_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(lean_box(0), v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
stack->m_obj
 = v_res_2966_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___boxed(lean_object* v_00_u03b1_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(v_00_u03b1_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
return v_res_2977_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(lean_object* v_as_2978_, size_t v_i_2979_, size_t v_stop_2980_, lean_object* v_b_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_usize_dec_eq(v_i_2979_, v_stop_2980_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_array_uget_borrowed(v_as_2978_, v_i_2979_);
lean_inc(v___x_2992_);
v___x_2993_ = l_Lean_Meta_AC_acNfHypTactic(v___x_2992_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; size_t v___x_2995_; size_t v___x_2996_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = ((size_t)1ULL);
v___x_2996_ = lean_usize_add(v_i_2979_, v___x_2995_);
v_i_2979_ = v___x_2996_;
v_b_2981_ = v_a_2994_;
goto _start;
}
else
{
return v___x_2993_;
}
}
else
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_b_2981_);
return v___x_2998_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2978_ = stack[0].m_obj;
size_t v_i_2979_ = stack[1].m_num;
size_t v_stop_2980_ = stack[2].m_num;
lean_object* v_b_2981_ = stack[3].m_obj;
lean_object* v___y_2982_ = stack[4].m_obj;
lean_object* v___y_2983_ = stack[5].m_obj;
lean_object* v___y_2984_ = stack[6].m_obj;
lean_object* v___y_2985_ = stack[7].m_obj;
lean_object* v___y_2986_ = stack[8].m_obj;
lean_object* v___y_2987_ = stack[9].m_obj;
lean_object* v___y_2988_ = stack[10].m_obj;
lean_object* v___y_2989_ = stack[11].m_obj;
lean_object* v_res_2999_;
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_as_2978_, v_i_2979_, v_stop_2980_, v_b_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
stack->m_obj
 = v_res_2999_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1___boxed(lean_object* v_as_3000_, lean_object* v_i_3001_, lean_object* v_stop_3002_, lean_object* v_b_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
size_t v_i_boxed_3013_; size_t v_stop_boxed_3014_; lean_object* v_res_3015_; 
v_i_boxed_3013_ = lean_unbox_usize(v_i_3001_);
lean_dec(v_i_3001_);
v_stop_boxed_3014_ = lean_unbox_usize(v_stop_3002_);
lean_dec(v_stop_3002_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_as_3000_, v_i_boxed_3013_, v_stop_boxed_3014_, v_b_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec_ref(v_as_3000_);
return v_res_3015_;
}
}
lean_object* l_Lean_Meta_AC_evalNf0___lam__0(lean_object* v___y_3016_, lean_object* v___x_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
if (lean_obj_tag(v___y_3016_) == 0)
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_Meta_AC_acNfTargetTactic(v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3028_; 
lean_dec_ref_known(v___x_3027_, 1);
v___x_3028_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3019_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3030_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v___x_3030_ = l_Lean_MVarId_getNondepPropHyps(v_a_3029_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3051_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3051_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3051_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3035_ = lean_array_get_size(v_a_3031_);
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_nat_dec_lt(v___x_3017_, v___x_3035_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3039_; 
lean_dec(v_a_3031_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3036_);
v___x_3039_ = v___x_3033_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3036_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
else
{
uint8_t v___x_3041_; 
v___x_3041_ = lean_nat_dec_le(v___x_3035_, v___x_3035_);
if (v___x_3041_ == 0)
{
if (v___x_3037_ == 0)
{
lean_object* v___x_3043_; 
lean_dec(v_a_3031_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3036_);
v___x_3043_ = v___x_3033_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3036_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
size_t v___x_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
lean_del_object(v___x_3033_);
v___x_3045_ = ((size_t)0ULL);
v___x_3046_ = lean_usize_of_nat(v___x_3035_);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3031_, v___x_3045_, v___x_3046_, v___x_3036_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v_a_3031_);
return v___x_3047_;
}
}
else
{
size_t v___x_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
lean_del_object(v___x_3033_);
v___x_3048_ = ((size_t)0ULL);
v___x_3049_ = lean_usize_of_nat(v___x_3035_);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3031_, v___x_3048_, v___x_3049_, v___x_3036_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v_a_3031_);
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_a_3052_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3030_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3030_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
v_a_3060_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3028_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3028_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
else
{
return v___x_3027_;
}
}
else
{
lean_object* v_hypotheses_3068_; uint8_t v_type_3069_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; 
v_hypotheses_3068_ = lean_ctor_get(v___y_3016_, 0);
lean_inc_ref(v_hypotheses_3068_);
v_type_3069_ = lean_ctor_get_uint8(v___y_3016_, sizeof(void*)*1);
lean_dec_ref_known(v___y_3016_, 1);
if (v_type_3069_ == 0)
{
v___y_3071_ = v___y_3018_;
v___y_3072_ = v___y_3019_;
v___y_3073_ = v___y_3020_;
v___y_3074_ = v___y_3021_;
v___y_3075_ = v___y_3022_;
v___y_3076_ = v___y_3023_;
v___y_3077_ = v___y_3024_;
v___y_3078_ = v___y_3025_;
goto v___jp_3070_;
}
else
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_Meta_AC_acNfTargetTactic(v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_dec_ref_known(v___x_3109_, 1);
v___y_3071_ = v___y_3018_;
v___y_3072_ = v___y_3019_;
v___y_3073_ = v___y_3020_;
v___y_3074_ = v___y_3021_;
v___y_3075_ = v___y_3022_;
v___y_3076_ = v___y_3023_;
v___y_3077_ = v___y_3024_;
v___y_3078_ = v___y_3025_;
goto v___jp_3070_;
}
else
{
lean_dec_ref(v_hypotheses_3068_);
return v___x_3109_;
}
}
v___jp_3070_:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_3068_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3100_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3082_ = v___x_3079_;
v_isShared_3083_ = v_isSharedCheck_3100_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3079_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3100_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3084_ = lean_array_get_size(v_a_3080_);
v___x_3085_ = lean_box(0);
v___x_3086_ = lean_nat_dec_lt(v___x_3017_, v___x_3084_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3088_; 
lean_dec(v_a_3080_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3085_);
v___x_3088_ = v___x_3082_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3085_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
else
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_nat_dec_le(v___x_3084_, v___x_3084_);
if (v___x_3090_ == 0)
{
if (v___x_3086_ == 0)
{
lean_object* v___x_3092_; 
lean_dec(v_a_3080_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3085_);
v___x_3092_ = v___x_3082_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3085_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
else
{
size_t v___x_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
lean_del_object(v___x_3082_);
v___x_3094_ = ((size_t)0ULL);
v___x_3095_ = lean_usize_of_nat(v___x_3084_);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3080_, v___x_3094_, v___x_3095_, v___x_3085_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v_a_3080_);
return v___x_3096_;
}
}
else
{
size_t v___x_3097_; size_t v___x_3098_; lean_object* v___x_3099_; 
lean_del_object(v___x_3082_);
v___x_3097_ = ((size_t)0ULL);
v___x_3098_ = lean_usize_of_nat(v___x_3084_);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_3080_, v___x_3097_, v___x_3098_, v___x_3085_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v_a_3080_);
return v___x_3099_;
}
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3079_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3079_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_evalNf0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3016_ = stack[0].m_obj;
lean_object* v___x_3017_ = stack[1].m_obj;
lean_object* v___y_3018_ = stack[2].m_obj;
lean_object* v___y_3019_ = stack[3].m_obj;
lean_object* v___y_3020_ = stack[4].m_obj;
lean_object* v___y_3021_ = stack[5].m_obj;
lean_object* v___y_3022_ = stack[6].m_obj;
lean_object* v___y_3023_ = stack[7].m_obj;
lean_object* v___y_3024_ = stack[8].m_obj;
lean_object* v___y_3025_ = stack[9].m_obj;
lean_object* v_res_3110_;
v_res_3110_ = l_Lean_Meta_AC_evalNf0___lam__0(v___y_3016_, v___x_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
stack->m_obj
 = v_res_3110_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___lam__0___boxed(lean_object* v___y_3111_, lean_object* v___x_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Meta_AC_evalNf0___lam__0(v___y_3111_, v___x_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___x_3112_);
return v_res_3122_;
}
}
lean_object* l_Lean_Meta_AC_evalNf0(lean_object* v_stx_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3141_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___closed__1));
lean_inc(v_stx_3131_);
v___x_3142_ = l_Lean_Syntax_isOfKind(v_stx_3131_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; 
lean_dec(v_stx_3131_);
v___x_3143_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v___x_3143_;
}
else
{
lean_object* v___x_3144_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3144_ = lean_unsigned_to_nat(0u);
v___x_3157_ = lean_unsigned_to_nat(1u);
v___x_3158_ = l_Lean_Syntax_getArg(v_stx_3131_, v___x_3157_);
lean_dec(v_stx_3131_);
v___x_3159_ = l_Lean_Syntax_isNone(v___x_3158_);
if (v___x_3159_ == 0)
{
uint8_t v___x_3160_; 
lean_inc(v___x_3158_);
v___x_3160_ = l_Lean_Syntax_matchesNull(v___x_3158_, v___x_3157_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3161_; 
lean_dec(v___x_3158_);
v___x_3161_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
return v___x_3161_;
}
else
{
lean_object* v_loc_x3f_3162_; lean_object* v___x_3163_; 
v_loc_x3f_3162_ = l_Lean_Syntax_getArg(v___x_3158_, v___x_3144_);
lean_dec(v___x_3158_);
v___x_3163_ = l_Lean_Elab_Tactic_expandLocation(v_loc_x3f_3162_);
lean_dec(v_loc_x3f_3162_);
v___y_3146_ = v_a_3135_;
v___y_3147_ = v_a_3139_;
v___y_3148_ = v_a_3138_;
v___y_3149_ = v_a_3136_;
v___y_3150_ = v_a_3132_;
v___y_3151_ = v_a_3133_;
v___y_3152_ = v_a_3137_;
v___y_3153_ = v_a_3134_;
v___y_3154_ = v___x_3163_;
goto v___jp_3145_;
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec(v___x_3158_);
v___x_3164_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___closed__2));
v___x_3165_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set_uint8(v___x_3165_, sizeof(void*)*1, v___x_3142_);
v___y_3146_ = v_a_3135_;
v___y_3147_ = v_a_3139_;
v___y_3148_ = v_a_3138_;
v___y_3149_ = v_a_3136_;
v___y_3150_ = v_a_3132_;
v___y_3151_ = v_a_3133_;
v___y_3152_ = v_a_3137_;
v___y_3153_ = v_a_3134_;
v___y_3154_ = v___x_3165_;
goto v___jp_3145_;
}
v___jp_3145_:
{
lean_object* v___y_3155_; lean_object* v___x_3156_; 
v___y_3155_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_evalNf0___lam__0___boxed), 11, 2);
lean_closure_set(v___y_3155_, 0, v___y_3154_);
lean_closure_set(v___y_3155_, 1, v___x_3144_);
v___x_3156_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_3155_, v___y_3150_, v___y_3151_, v___y_3153_, v___y_3146_, v___y_3149_, v___y_3152_, v___y_3148_, v___y_3147_);
return v___x_3156_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AC_evalNf0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3131_ = stack[0].m_obj;
lean_object* v_a_3132_ = stack[1].m_obj;
lean_object* v_a_3133_ = stack[2].m_obj;
lean_object* v_a_3134_ = stack[3].m_obj;
lean_object* v_a_3135_ = stack[4].m_obj;
lean_object* v_a_3136_ = stack[5].m_obj;
lean_object* v_a_3137_ = stack[6].m_obj;
lean_object* v_a_3138_ = stack[7].m_obj;
lean_object* v_a_3139_ = stack[8].m_obj;
lean_object* v_res_3166_;
v_res_3166_ = l_Lean_Meta_AC_evalNf0(v_stx_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_);
stack->m_obj
 = v_res_3166_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AC_evalNf0___boxed(lean_object* v_stx_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Lean_Meta_AC_evalNf0(v_stx_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec(v_a_3173_);
lean_dec_ref(v_a_3172_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
return v_res_3177_;
}
}
lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1(){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3185_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3186_ = ((lean_object*)(l_Lean_Meta_AC_evalNf0___closed__1));
v___x_3187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1));
v___x_3188_ = lean_alloc_closure((void*)(l_Lean_Meta_AC_evalNf0___boxed), 10, 0);
v___x_3189_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3185_, v___x_3186_, v___x_3187_, v___x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3190_;
v_res_3190_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
stack->m_obj
 = v_res_3190_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___boxed(lean_object* v_a_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
return v_res_3192_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = lean_unsigned_to_nat(4236260923u);
v___x_3249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_));
v___x_3250_ = l_Lean_Name_num___override(v___x_3249_, v___x_3248_);
return v___x_3250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_));
v___x_3253_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3254_ = l_Lean_Name_str___override(v___x_3253_, v___x_3252_);
return v___x_3254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_));
v___x_3257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3258_ = l_Lean_Name_str___override(v___x_3257_, v___x_3256_);
return v___x_3258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = lean_unsigned_to_nat(2u);
v___x_3260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3261_ = l_Lean_Name_num___override(v___x_3260_, v___x_3259_);
return v___x_3261_;
}
}
lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3263_; uint8_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3263_ = ((lean_object*)(l_Lean_Meta_AC_getInstance___closed__2));
v___x_3264_ = 0;
v___x_3265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
v___x_3266_ = l_Lean_registerTraceClass(v___x_3263_, v___x_3264_, v___x_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3267_;
v_res_3267_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3267_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2____boxed(lean_object* v_a_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_();
return v_res_3269_;
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
