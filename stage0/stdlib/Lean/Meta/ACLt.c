// Lean compiler output
// Module: Lean.Meta.ACLt
// Imports: public import Lean.Meta.DiscrTree.Main import Init.Data.Range.Polymorphic.Iterators import Lean.Meta.FunInfo
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
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21(lean_object*);
lean_object* l_Lean_FVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
uint8_t l_Lean_Level_normLt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letValue_x21(lean_object*);
lean_object* l_Lean_Expr_letBody_x21(lean_object*);
lean_object* l_Lean_Expr_litValue_x21(lean_object*);
uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_ctorWeight(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorWeight___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 2, 0, 1, 0, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0 = (const lean_object*)&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0 = (const lean_object*)&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2 = (const lean_object*)&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2_value;
static const lean_string_object l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1 = (const lean_object*)&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1_value;
static const lean_string_object l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0 = (const lean_object*)&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3;
static lean_once_cell_t l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6 = (const lean_object*)&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6_value;
static const lean_string_object l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "_private.Lean.Meta.ACLt.0.Lean.Meta.ACLt.main.lexSameCtor"};
static const lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5 = (const lean_object*)&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5_value;
static const lean_string_object l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Meta.ACLt"};
static const lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4 = (const lean_object*)&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_acLt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_acLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_ctorWeight(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
case 1:
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
case 2:
{
uint8_t v___x_4_; 
v___x_4_ = 2;
return v___x_4_;
}
case 3:
{
uint8_t v___x_5_; 
v___x_5_ = 3;
return v___x_5_;
}
case 4:
{
uint8_t v___x_6_; 
v___x_6_ = 4;
return v___x_6_;
}
case 5:
{
uint8_t v___x_7_; 
v___x_7_ = 8;
return v___x_7_;
}
case 6:
{
uint8_t v___x_8_; 
v___x_8_ = 9;
return v___x_8_;
}
case 7:
{
uint8_t v___x_9_; 
v___x_9_ = 10;
return v___x_9_;
}
case 8:
{
uint8_t v___x_10_; 
v___x_10_ = 11;
return v___x_10_;
}
case 9:
{
uint8_t v___x_11_; 
v___x_11_ = 5;
return v___x_11_;
}
case 10:
{
uint8_t v___x_12_; 
v___x_12_ = 6;
return v___x_12_;
}
default: 
{
uint8_t v___x_13_; 
v___x_13_ = 7;
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorWeight___boxed(lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_Expr_ctorWeight(v_x_14_);
lean_dec_ref(v_x_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx(uint8_t v_x_17_){
_start:
{
switch(v_x_17_)
{
case 0:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(0u);
return v___x_18_;
}
case 1:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(1u);
return v___x_19_;
}
default: 
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(2u);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx___boxed(lean_object* v_x_21_){
_start:
{
uint8_t v_x_boxed_22_; lean_object* v_res_23_; 
v_x_boxed_22_ = lean_unbox(v_x_21_);
v_res_23_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx(v_x_boxed_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_toCtorIdx(uint8_t v_x_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx(v_x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_toCtorIdx___boxed(lean_object* v_x_26_){
_start:
{
uint8_t v_x_4__boxed_27_; lean_object* v_res_28_; 
v_x_4__boxed_27_ = lean_unbox(v_x_26_);
v_res_28_ = l_Lean_Meta_ACLt_ReduceMode_toCtorIdx(v_x_4__boxed_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(lean_object* v_k_29_){
_start:
{
lean_inc(v_k_29_);
return v_k_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg___boxed(lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(v_k_30_);
lean_dec(v_k_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim(lean_object* v_motive_32_, lean_object* v_ctorIdx_33_, uint8_t v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_inc(v_k_36_);
return v_k_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___boxed(lean_object* v_motive_37_, lean_object* v_ctorIdx_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_k_41_){
_start:
{
uint8_t v_t_boxed_42_; lean_object* v_res_43_; 
v_t_boxed_42_ = lean_unbox(v_t_39_);
v_res_43_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim(v_motive_37_, v_ctorIdx_38_, v_t_boxed_42_, v_h_40_, v_k_41_);
lean_dec(v_k_41_);
lean_dec(v_ctorIdx_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(lean_object* v_reduce_44_){
_start:
{
lean_inc(v_reduce_44_);
return v_reduce_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg___boxed(lean_object* v_reduce_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(v_reduce_45_);
lean_dec(v_reduce_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim(lean_object* v_motive_47_, uint8_t v_t_48_, lean_object* v_h_49_, lean_object* v_reduce_50_){
_start:
{
lean_inc(v_reduce_50_);
return v_reduce_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___boxed(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_reduce_54_){
_start:
{
uint8_t v_t_boxed_55_; lean_object* v_res_56_; 
v_t_boxed_55_ = lean_unbox(v_t_52_);
v_res_56_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim(v_motive_51_, v_t_boxed_55_, v_h_53_, v_reduce_54_);
lean_dec(v_reduce_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(lean_object* v_reduceSimpleOnly_57_){
_start:
{
lean_inc(v_reduceSimpleOnly_57_);
return v_reduceSimpleOnly_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg___boxed(lean_object* v_reduceSimpleOnly_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(v_reduceSimpleOnly_58_);
lean_dec(v_reduceSimpleOnly_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(lean_object* v_motive_60_, uint8_t v_t_61_, lean_object* v_h_62_, lean_object* v_reduceSimpleOnly_63_){
_start:
{
lean_inc(v_reduceSimpleOnly_63_);
return v_reduceSimpleOnly_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___boxed(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_reduceSimpleOnly_67_){
_start:
{
uint8_t v_t_boxed_68_; lean_object* v_res_69_; 
v_t_boxed_68_ = lean_unbox(v_t_65_);
v_res_69_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(v_motive_64_, v_t_boxed_68_, v_h_66_, v_reduceSimpleOnly_67_);
lean_dec(v_reduceSimpleOnly_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(lean_object* v_none_70_){
_start:
{
lean_inc(v_none_70_);
return v_none_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg___boxed(lean_object* v_none_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(v_none_71_);
lean_dec(v_none_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim(lean_object* v_motive_73_, uint8_t v_t_74_, lean_object* v_h_75_, lean_object* v_none_76_){
_start:
{
lean_inc(v_none_76_);
return v_none_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___boxed(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_none_80_){
_start:
{
uint8_t v_t_boxed_81_; lean_object* v_res_82_; 
v_t_boxed_81_ = lean_unbox(v_t_78_);
v_res_82_ = l_Lean_Meta_ACLt_ReduceMode_none_elim(v_motive_77_, v_t_boxed_81_, v_h_79_, v_none_80_);
lean_dec(v_none_80_);
return v_res_82_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0));
v___x_90_ = l_Lean_Meta_Config_toConfigWithKey(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(uint8_t v_mode_92_, lean_object* v_e_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Lean_Expr_hasLooseBVars(v_e_93_);
if (v___x_99_ == 0)
{
switch(v_mode_92_)
{
case 0:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Meta_DiscrTree_reduce(v_e_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
return v___x_100_;
}
case 1:
{
lean_object* v___x_101_; lean_object* v_config_102_; uint8_t v_trackZetaDelta_103_; lean_object* v_zetaDeltaSet_104_; lean_object* v_lctx_105_; lean_object* v_localInstances_106_; lean_object* v_defEqCtx_x3f_107_; lean_object* v_synthPendingDepth_108_; lean_object* v_canUnfold_x3f_109_; uint8_t v_univApprox_110_; uint8_t v_inTypeClassResolution_111_; uint8_t v_cacheInferType_112_; uint64_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_101_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config;
v_config_102_ = lean_ctor_get(v___x_101_, 0);
v_trackZetaDelta_103_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7);
v_zetaDeltaSet_104_ = lean_ctor_get(v_a_94_, 1);
v_lctx_105_ = lean_ctor_get(v_a_94_, 2);
v_localInstances_106_ = lean_ctor_get(v_a_94_, 3);
v_defEqCtx_x3f_107_ = lean_ctor_get(v_a_94_, 4);
v_synthPendingDepth_108_ = lean_ctor_get(v_a_94_, 5);
v_canUnfold_x3f_109_ = lean_ctor_get(v_a_94_, 6);
v_univApprox_110_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_111_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7 + 2);
v_cacheInferType_112_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7 + 3);
v___x_113_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_102_);
lean_inc_ref(v_config_102_);
v___x_114_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_114_, 0, v_config_102_);
lean_ctor_set_uint64(v___x_114_, sizeof(void*)*1, v___x_113_);
lean_inc(v_canUnfold_x3f_109_);
lean_inc(v_synthPendingDepth_108_);
lean_inc(v_defEqCtx_x3f_107_);
lean_inc_ref(v_localInstances_106_);
lean_inc_ref(v_lctx_105_);
lean_inc(v_zetaDeltaSet_104_);
v___x_115_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_zetaDeltaSet_104_);
lean_ctor_set(v___x_115_, 2, v_lctx_105_);
lean_ctor_set(v___x_115_, 3, v_localInstances_106_);
lean_ctor_set(v___x_115_, 4, v_defEqCtx_x3f_107_);
lean_ctor_set(v___x_115_, 5, v_synthPendingDepth_108_);
lean_ctor_set(v___x_115_, 6, v_canUnfold_x3f_109_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*7, v_trackZetaDelta_103_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*7 + 1, v_univApprox_110_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*7 + 2, v_inTypeClassResolution_111_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*7 + 3, v_cacheInferType_112_);
v___x_116_ = l_Lean_Meta_DiscrTree_reduce(v_e_93_, v___x_115_, v_a_95_, v_a_96_, v_a_97_);
lean_dec_ref(v___x_115_);
return v___x_116_;
}
default: 
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v_e_93_);
return v___x_117_;
}
}
}
else
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v_e_93_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce___boxed(lean_object* v_mode_119_, lean_object* v_e_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
uint8_t v_mode_boxed_126_; lean_object* v_res_127_; 
v_mode_boxed_126_ = lean_unbox(v_mode_119_);
v_res_127_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_boxed_126_, v_e_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(lean_object* v_f_130_, lean_object* v_numArgs_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
uint8_t v___x_137_; 
v___x_137_ = l_Lean_Expr_hasLooseBVars(v_f_130_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_getFunInfoNArgs(v_f_130_, v_numArgs_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_147_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_147_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_paramInfo_143_; lean_object* v___x_145_; 
v_paramInfo_143_ = lean_ctor_get(v_a_139_, 0);
lean_inc_ref(v_paramInfo_143_);
lean_dec(v_a_139_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v_paramInfo_143_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_paramInfo_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_148_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_138_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_138_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
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
else
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v_numArgs_131_);
lean_dec_ref(v_f_130_);
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0));
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___boxed(lean_object* v_f_158_, lean_object* v_numArgs_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_f_158_, v_numArgs_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(lean_object* v_msg_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___f_173_; lean_object* v___x_16129__overap_174_; lean_object* v___x_175_; 
v___f_173_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0));
v___x_16129__overap_174_ = lean_panic_fn_borrowed(v___f_173_, v_msg_167_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
v___x_175_ = lean_apply_5(v___x_16129__overap_174_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, lean_box(0));
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v_msg_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(lean_object* v_msg_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = l_Lean_instInhabitedLocalDecl_default;
v___x_185_ = lean_panic_fn_borrowed(v___x_184_, v_msg_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(uint8_t v_mode_186_, lean_object* v_a_u2081_187_, lean_object* v_a_u2082_188_, lean_object* v_b_u2081_189_, lean_object* v_b_u2082_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; 
lean_inc_ref(v_b_u2081_189_);
lean_inc_ref(v_a_u2081_187_);
v___x_196_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_186_, v_a_u2081_187_, v_b_u2081_189_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; uint8_t v___x_198_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
v___x_198_ = lean_unbox(v_a_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_dec_ref(v___x_196_);
v___x_199_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_186_, v_b_u2081_189_, v_a_u2081_187_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_209_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_209_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_209_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_209_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
uint8_t v___x_204_; 
v___x_204_ = lean_unbox(v_a_200_);
lean_dec(v_a_200_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_del_object(v___x_202_);
lean_dec(v_a_197_);
v___x_205_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_186_, v_a_u2082_188_, v_b_u2082_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
return v___x_205_;
}
else
{
lean_object* v___x_207_; 
lean_dec_ref(v_b_u2082_190_);
lean_dec_ref(v_a_u2082_188_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v_a_197_);
v___x_207_ = v___x_202_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_197_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_dec(v_a_197_);
lean_dec_ref(v_b_u2082_190_);
lean_dec_ref(v_a_u2082_188_);
return v___x_199_;
}
}
else
{
lean_dec(v_a_197_);
lean_dec_ref(v_b_u2082_190_);
lean_dec_ref(v_b_u2081_189_);
lean_dec_ref(v_a_u2082_188_);
lean_dec_ref(v_a_u2081_187_);
return v___x_196_;
}
}
else
{
lean_dec_ref(v_b_u2082_190_);
lean_dec_ref(v_b_u2081_189_);
lean_dec_ref(v_a_u2082_188_);
lean_dec_ref(v_a_u2081_187_);
return v___x_196_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_213_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2));
v___x_214_ = lean_unsigned_to_nat(14u);
v___x_215_ = lean_unsigned_to_nat(22u);
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1));
v___x_217_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0));
v___x_218_ = l_mkPanicMessageWithDecl(v___x_217_, v___x_216_, v___x_215_, v___x_214_, v___x_213_);
return v___x_218_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0(void){
_start:
{
lean_object* v___x_219_; lean_object* v_dummy_220_; 
v___x_219_ = lean_box(0);
v_dummy_220_ = l_Lean_Expr_sort___override(v___x_219_);
return v_dummy_220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(lean_object* v_upperBound_224_, lean_object* v_a_225_, lean_object* v___x_226_, lean_object* v___x_227_, uint8_t v_mode_228_, lean_object* v_a_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_a_237_; uint8_t v___x_241_; 
v___x_241_ = lean_nat_dec_lt(v_a_229_, v_upperBound_224_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_dec(v_a_229_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v_b_230_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v_isInstance_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref(v_b_230_);
v___x_243_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_244_ = lean_array_get_borrowed(v___x_243_, v_a_225_, v_a_229_);
v_isInstance_245_ = lean_ctor_get_uint8(v___x_244_, sizeof(void*)*1 + 4);
v___x_246_ = lean_box(0);
v___x_247_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_245_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_248_ = l_Lean_instInhabitedExpr;
v___x_249_ = lean_array_get_borrowed(v___x_248_, v___x_226_, v_a_229_);
v___x_250_ = lean_array_get_borrowed(v___x_248_, v___x_227_, v_a_229_);
lean_inc(v___x_250_);
lean_inc(v___x_249_);
v___x_251_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_228_, v___x_249_, v___x_250_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_282_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_282_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_282_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_282_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; 
v___x_256_ = lean_unbox(v_a_252_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_del_object(v___x_254_);
lean_inc(v___x_249_);
lean_inc(v___x_250_);
v___x_257_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_228_, v___x_250_, v___x_249_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_268_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_268_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_268_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_268_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
uint8_t v___x_262_; 
v___x_262_ = lean_unbox(v_a_258_);
lean_dec(v_a_258_);
if (v___x_262_ == 0)
{
lean_del_object(v___x_260_);
lean_dec(v_a_252_);
v_a_237_ = v___x_247_;
goto v___jp_236_;
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
lean_dec(v_a_229_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_a_252_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_246_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_264_);
v___x_266_ = v___x_260_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_252_);
lean_dec(v_a_229_);
v_a_269_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_257_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_257_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
lean_dec(v_a_229_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v_a_252_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_246_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_278_);
v___x_280_ = v___x_254_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v_a_229_);
v_a_283_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_251_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_251_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
v_a_237_ = v___x_247_;
goto v___jp_236_;
}
}
v___jp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_a_229_, v___x_238_);
lean_dec(v_a_229_);
lean_inc_ref(v_a_237_);
v_a_229_ = v___x_239_;
v_b_230_ = v_a_237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(lean_object* v_upperBound_291_, lean_object* v___x_292_, lean_object* v___x_293_, uint8_t v_mode_294_, lean_object* v_a_295_, lean_object* v_b_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_nat_dec_lt(v_a_295_, v_upperBound_291_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_dec(v_a_295_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v_b_296_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref(v_b_296_);
v___x_304_ = l_Lean_instInhabitedExpr;
v___x_305_ = lean_array_get_borrowed(v___x_304_, v___x_292_, v_a_295_);
v___x_306_ = lean_array_get_borrowed(v___x_304_, v___x_293_, v_a_295_);
lean_inc(v___x_306_);
lean_inc(v___x_305_);
v___x_307_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_294_, v___x_305_, v___x_306_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_343_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_343_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_343_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_343_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = lean_box(0);
v___x_313_ = lean_unbox(v_a_308_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_del_object(v___x_310_);
lean_inc(v___x_305_);
lean_inc(v___x_306_);
v___x_314_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_294_, v___x_306_, v___x_305_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_329_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_329_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_329_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_329_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
uint8_t v___x_319_; 
v___x_319_ = lean_unbox(v_a_315_);
lean_dec(v_a_315_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_317_);
lean_dec(v_a_308_);
v___x_320_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_a_295_, v___x_321_);
lean_dec(v_a_295_);
v_a_295_ = v___x_322_;
v_b_296_ = v___x_320_;
goto _start;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
lean_dec(v_a_295_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_a_308_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_312_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_325_);
v___x_327_ = v___x_317_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_a_308_);
lean_dec(v_a_295_);
v_a_330_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_314_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_314_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec(v_a_295_);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v_a_308_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_312_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_339_);
v___x_341_ = v___x_310_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_a_295_);
v_a_344_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_307_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_307_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(uint8_t v_mode_352_, lean_object* v_a_353_, lean_object* v_b_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_aFn_360_; lean_object* v_bFn_361_; lean_object* v___x_362_; 
v_aFn_360_ = l_Lean_Expr_getAppFn(v_a_353_);
v_bFn_361_ = l_Lean_Expr_getAppFn(v_b_354_);
lean_inc_ref(v_bFn_361_);
lean_inc_ref(v_aFn_360_);
v___x_362_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_352_, v_aFn_360_, v_bFn_361_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_461_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_461_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_461_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_461_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
uint8_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 1;
v___x_368_ = lean_unbox(v_a_363_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_del_object(v___x_365_);
lean_inc_ref(v_aFn_360_);
v___x_369_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_352_, v_bFn_361_, v_aFn_360_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; uint8_t v___x_371_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
v___x_371_ = lean_unbox(v_a_370_);
if (v___x_371_ == 0)
{
lean_object* v_dummy_372_; lean_object* v_nargs_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_nargs_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
lean_dec(v_a_363_);
v_dummy_372_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_373_ = l_Lean_Expr_getAppNumArgs(v_a_353_);
lean_inc(v_nargs_373_);
v___x_374_ = lean_mk_array(v_nargs_373_, v_dummy_372_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_sub(v_nargs_373_, v___x_375_);
lean_dec(v_nargs_373_);
v___x_377_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_353_, v___x_374_, v___x_376_);
v_nargs_378_ = l_Lean_Expr_getAppNumArgs(v_b_354_);
lean_inc(v_nargs_378_);
v___x_379_ = lean_mk_array(v_nargs_378_, v_dummy_372_);
v___x_380_ = lean_nat_sub(v_nargs_378_, v___x_375_);
lean_dec(v_nargs_378_);
v___x_381_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_b_354_, v___x_379_, v___x_380_);
v___x_382_ = lean_array_get_size(v___x_377_);
v___x_383_ = lean_array_get_size(v___x_381_);
v___x_384_ = lean_nat_dec_lt(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = lean_nat_dec_lt(v___x_383_, v___x_382_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v___x_369_);
v___x_386_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_360_, v___x_382_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref(v___x_386_);
v___x_388_ = lean_array_get_size(v_a_387_);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_391_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_388_, v_a_387_, v___x_377_, v___x_381_, v_mode_352_, v___x_389_, v___x_390_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_387_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_423_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_423_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_423_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_423_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_fst_396_; 
v_fst_396_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_fst_396_);
lean_dec(v_a_392_);
if (lean_obj_tag(v_fst_396_) == 0)
{
lean_object* v___x_397_; 
lean_del_object(v___x_394_);
v___x_397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_382_, v___x_377_, v___x_381_, v_mode_352_, v___x_388_, v___x_390_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_410_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_410_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_fst_402_; 
v_fst_402_ = lean_ctor_get(v_a_398_, 0);
lean_inc(v_fst_402_);
lean_dec(v_a_398_);
if (lean_obj_tag(v_fst_402_) == 0)
{
lean_object* v___x_404_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_a_370_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_370_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_object* v_val_406_; lean_object* v___x_408_; 
lean_dec(v_a_370_);
v_val_406_ = lean_ctor_get(v_fst_402_, 0);
lean_inc(v_val_406_);
lean_dec_ref(v_fst_402_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_val_406_);
v___x_408_ = v___x_400_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_val_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_a_370_);
v_a_411_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_397_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_397_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v_val_419_; lean_object* v___x_421_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
lean_dec(v_a_370_);
v_val_419_ = lean_ctor_get(v_fst_396_, 0);
lean_inc(v_val_419_);
lean_dec_ref(v_fst_396_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_val_419_);
v___x_421_ = v___x_394_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_val_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
lean_dec(v_a_370_);
v_a_424_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_391_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_391_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
lean_dec(v_a_370_);
v_a_432_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_386_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_386_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
else
{
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
lean_dec(v_a_370_);
lean_dec_ref(v_aFn_360_);
return v___x_369_;
}
}
else
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
lean_dec(v_a_370_);
lean_dec_ref(v_aFn_360_);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v___x_369_, 0);
lean_dec(v_unused_448_);
v___x_441_ = v___x_369_;
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
else
{
lean_dec(v___x_369_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_447_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = lean_box(v___x_367_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_443_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_a_370_);
lean_dec_ref(v_aFn_360_);
lean_dec_ref(v_b_354_);
lean_dec_ref(v_a_353_);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v___x_369_, 0);
lean_dec(v_unused_456_);
v___x_450_ = v___x_369_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_dec(v___x_369_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v_a_363_);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_363_);
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
lean_dec(v_a_363_);
lean_dec_ref(v_aFn_360_);
lean_dec_ref(v_b_354_);
lean_dec_ref(v_a_353_);
return v___x_369_;
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec(v_a_363_);
lean_dec_ref(v_bFn_361_);
lean_dec_ref(v_aFn_360_);
lean_dec_ref(v_b_354_);
lean_dec_ref(v_a_353_);
v___x_457_ = lean_box(v___x_367_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_457_);
v___x_459_ = v___x_365_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_dec_ref(v_bFn_361_);
lean_dec_ref(v_aFn_360_);
lean_dec_ref(v_b_354_);
lean_dec_ref(v_a_353_);
return v___x_362_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6));
v___x_466_ = lean_unsigned_to_nat(27u);
v___x_467_ = lean_unsigned_to_nat(152u);
v___x_468_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5));
v___x_469_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4));
v___x_470_ = l_mkPanicMessageWithDecl(v___x_469_, v___x_468_, v___x_467_, v___x_466_, v___x_465_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(uint8_t v_mode_471_, lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_d_480_; lean_object* v_e_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; 
switch(lean_obj_tag(v_a_472_))
{
case 0:
{
lean_object* v_deBruijnIndex_489_; lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_deBruijnIndex_489_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_deBruijnIndex_489_);
lean_dec_ref(v_a_472_);
v___x_490_ = l_Lean_Expr_bvarIdx_x21(v_b_473_);
lean_dec_ref(v_b_473_);
v___x_491_ = lean_nat_dec_lt(v_deBruijnIndex_489_, v___x_490_);
lean_dec(v___x_490_);
lean_dec(v_deBruijnIndex_489_);
v___x_492_ = lean_box(v___x_491_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
case 1:
{
lean_object* v_fvarId_494_; lean_object* v___x_495_; 
v_fvarId_494_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_fvarId_494_);
lean_dec_ref(v_a_472_);
v___x_495_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_494_, v_a_474_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
v___x_497_ = l_Lean_Expr_fvarId_x21(v_b_473_);
lean_dec_ref(v_b_473_);
v___x_498_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_497_, v_a_474_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_521_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_521_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_521_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_521_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_513_; 
if (lean_obj_tag(v_a_496_) == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_519_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_518_);
v___y_513_ = v___x_519_;
goto v___jp_512_;
}
else
{
lean_object* v_val_520_; 
v_val_520_ = lean_ctor_get(v_a_496_, 0);
lean_inc(v_val_520_);
lean_dec_ref(v_a_496_);
v___y_513_ = v_val_520_;
goto v___jp_512_;
}
v___jp_503_:
{
lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_506_ = l_Lean_LocalDecl_index(v___y_505_);
lean_dec_ref(v___y_505_);
v___x_507_ = lean_nat_dec_lt(v___y_504_, v___x_506_);
lean_dec(v___x_506_);
lean_dec(v___y_504_);
v___x_508_ = lean_box(v___x_507_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_508_);
v___x_510_ = v___x_501_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
v___jp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_LocalDecl_index(v___y_513_);
lean_dec_ref(v___y_513_);
if (lean_obj_tag(v_a_499_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_516_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_515_);
v___y_504_ = v___x_514_;
v___y_505_ = v___x_516_;
goto v___jp_503_;
}
else
{
lean_object* v_val_517_; 
v_val_517_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_val_517_);
lean_dec_ref(v_a_499_);
v___y_504_ = v___x_514_;
v___y_505_ = v_val_517_;
goto v___jp_503_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_a_496_);
v_a_522_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_498_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_498_);
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
lean_dec_ref(v_b_473_);
v_a_530_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_495_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_495_);
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
case 2:
{
lean_object* v_mvarId_538_; lean_object* v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_mvarId_538_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_mvarId_538_);
lean_dec_ref(v_a_472_);
v___x_539_ = l_Lean_Expr_mvarId_x21(v_b_473_);
lean_dec_ref(v_b_473_);
v___x_540_ = l_Lean_Name_lt(v_mvarId_538_, v___x_539_);
lean_dec(v___x_539_);
lean_dec(v_mvarId_538_);
v___x_541_ = lean_box(v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
case 3:
{
lean_object* v_u_543_; lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_u_543_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_u_543_);
lean_dec_ref(v_a_472_);
v___x_544_ = l_Lean_Expr_sortLevel_x21(v_b_473_);
lean_dec_ref(v_b_473_);
v___x_545_ = l_Lean_Level_normLt(v_u_543_, v___x_544_);
lean_dec(v___x_544_);
lean_dec(v_u_543_);
v___x_546_ = lean_box(v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
case 4:
{
lean_object* v_declName_548_; lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_declName_548_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_declName_548_);
lean_dec_ref(v_a_472_);
v___x_549_ = l_Lean_Expr_constName_x21(v_b_473_);
lean_dec_ref(v_b_473_);
v___x_550_ = l_Lean_Name_lt(v_declName_548_, v___x_549_);
lean_dec(v___x_549_);
lean_dec(v_declName_548_);
v___x_551_ = lean_box(v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
case 5:
{
lean_object* v___x_553_; 
v___x_553_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_471_, v_a_472_, v_b_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_553_;
}
case 8:
{
lean_object* v_value_554_; lean_object* v_body_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_value_554_ = lean_ctor_get(v_a_472_, 2);
lean_inc_ref(v_value_554_);
v_body_555_ = lean_ctor_get(v_a_472_, 3);
lean_inc_ref(v_body_555_);
lean_dec_ref(v_a_472_);
v___x_556_ = l_Lean_Expr_letValue_x21(v_b_473_);
v___x_557_ = l_Lean_Expr_letBody_x21(v_b_473_);
lean_dec_ref(v_b_473_);
v___x_558_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_471_, v_value_554_, v_body_555_, v___x_556_, v___x_557_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_558_;
}
case 9:
{
lean_object* v_a_559_; lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_a_559_ = lean_ctor_get(v_a_472_, 0);
lean_inc_ref(v_a_559_);
lean_dec_ref(v_a_472_);
v___x_560_ = l_Lean_Expr_litValue_x21(v_b_473_);
lean_dec_ref(v_b_473_);
v___x_561_ = l_Lean_Literal_lt(v_a_559_, v___x_560_);
lean_dec_ref(v___x_560_);
lean_dec_ref(v_a_559_);
v___x_562_ = lean_box(v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
case 10:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec_ref(v_a_472_);
lean_dec_ref(v_b_473_);
v___x_564_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
v___x_565_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_564_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_565_;
}
case 11:
{
lean_object* v_idx_566_; lean_object* v_struct_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_idx_566_ = lean_ctor_get(v_a_472_, 1);
lean_inc(v_idx_566_);
v_struct_567_ = lean_ctor_get(v_a_472_, 2);
lean_inc_ref(v_struct_567_);
lean_dec_ref(v_a_472_);
v___x_568_ = l_Lean_Expr_projIdx_x21(v_b_473_);
v___x_569_ = lean_nat_dec_eq(v_idx_566_, v___x_568_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec_ref(v_struct_567_);
lean_dec_ref(v_b_473_);
v___x_570_ = lean_nat_dec_lt(v_idx_566_, v___x_568_);
lean_dec(v___x_568_);
lean_dec(v_idx_566_);
v___x_571_ = lean_box(v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_568_);
lean_dec(v_idx_566_);
v___x_573_ = l_Lean_Expr_projExpr_x21(v_b_473_);
lean_dec_ref(v_b_473_);
v___x_574_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_471_, v_struct_567_, v___x_573_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_574_;
}
}
default: 
{
lean_object* v_binderType_575_; lean_object* v_body_576_; 
v_binderType_575_ = lean_ctor_get(v_a_472_, 1);
lean_inc_ref(v_binderType_575_);
v_body_576_ = lean_ctor_get(v_a_472_, 2);
lean_inc_ref(v_body_576_);
lean_dec_ref(v_a_472_);
v_d_480_ = v_binderType_575_;
v_e_481_ = v_body_576_;
v___y_482_ = v_a_474_;
v___y_483_ = v_a_475_;
v___y_484_ = v_a_476_;
v___y_485_ = v_a_477_;
goto v___jp_479_;
}
}
v___jp_479_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = l_Lean_Expr_bindingDomain_x21(v_b_473_);
v___x_487_ = l_Lean_Expr_bindingBody_x21(v_b_473_);
lean_dec_ref(v_b_473_);
v___x_488_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_471_, v_d_480_, v_e_481_, v___x_486_, v___x_487_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(uint8_t v_mode_577_, lean_object* v_a_578_, lean_object* v_b_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
lean_inc_ref(v_a_578_);
lean_inc_ref(v_b_579_);
v___x_585_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_577_, v_b_579_, v_a_578_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; uint8_t v___x_587_; uint8_t v___x_588_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
v___x_587_ = 1;
v___x_588_ = lean_unbox(v_a_586_);
if (v___x_588_ == 0)
{
uint8_t v___x_589_; uint8_t v___x_590_; uint8_t v___x_591_; 
v___x_589_ = l_Lean_Expr_ctorWeight(v_b_579_);
v___x_590_ = l_Lean_Expr_ctorWeight(v_a_578_);
v___x_591_ = lean_uint8_dec_lt(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
lean_dec_ref(v___x_585_);
lean_inc_ref(v_b_579_);
lean_inc_ref(v_a_578_);
v___x_592_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_577_, v_a_578_, v_b_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_607_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_607_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v___x_597_; 
v___x_597_ = lean_unbox(v_a_593_);
lean_dec(v_a_593_);
if (v___x_597_ == 0)
{
lean_object* v___x_599_; 
lean_dec_ref(v_b_579_);
lean_dec_ref(v_a_578_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_a_586_);
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_586_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
uint8_t v___x_601_; 
lean_dec(v_a_586_);
v___x_601_ = lean_uint8_dec_lt(v___x_590_, v___x_589_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_del_object(v___x_595_);
v___x_602_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_577_, v_a_578_, v_b_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_605_; 
lean_dec_ref(v_b_579_);
lean_dec_ref(v_a_578_);
v___x_603_ = lean_box(v___x_587_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_603_);
v___x_605_ = v___x_595_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
else
{
lean_dec(v_a_586_);
lean_dec_ref(v_b_579_);
lean_dec_ref(v_a_578_);
return v___x_592_;
}
}
else
{
lean_dec(v_a_586_);
lean_dec_ref(v_b_579_);
lean_dec_ref(v_a_578_);
return v___x_585_;
}
}
else
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_a_586_);
lean_dec_ref(v_b_579_);
lean_dec_ref(v_a_578_);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_585_, 0);
lean_dec(v_unused_616_);
v___x_609_ = v___x_585_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_dec(v___x_585_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_box(v___x_587_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
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
lean_dec_ref(v_b_579_);
lean_dec_ref(v_a_578_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(uint8_t v_mode_617_, lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_expr_eqv(v_a_618_, v_b_619_);
if (v___x_625_ == 0)
{
uint8_t v___x_626_; 
v___x_626_ = l_Lean_Expr_isMData(v_a_618_);
if (v___x_626_ == 0)
{
uint8_t v___x_627_; 
v___x_627_ = l_Lean_Expr_isMData(v_b_619_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_617_, v_a_618_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref(v___x_628_);
v___x_630_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_617_, v_b_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref(v___x_630_);
v___x_632_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_617_, v_a_629_, v_a_631_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
return v___x_632_;
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_a_629_);
v_a_633_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_630_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_630_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v_b_619_);
v_a_641_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_628_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_628_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Expr_mdataExpr_x21(v_b_619_);
lean_dec_ref(v_b_619_);
v_b_619_ = v___x_649_;
goto _start;
}
}
else
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Expr_mdataExpr_x21(v_a_618_);
lean_dec_ref(v_a_618_);
v_a_618_ = v___x_651_;
goto _start;
}
}
else
{
uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec_ref(v_b_619_);
lean_dec_ref(v_a_618_);
v___x_653_ = 0;
v___x_654_ = lean_box(v___x_653_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(lean_object* v_upperBound_656_, lean_object* v_a_657_, lean_object* v_args_658_, uint8_t v_mode_659_, lean_object* v_b_660_, lean_object* v_a_661_, lean_object* v_b_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_a_669_; uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_lt(v_a_661_, v_upperBound_656_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec(v_a_661_);
lean_dec_ref(v_b_660_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v_b_662_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v_isInstance_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec_ref(v_b_662_);
v___x_675_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_676_ = lean_array_get_borrowed(v___x_675_, v_a_657_, v_a_661_);
v_isInstance_677_ = lean_ctor_get_uint8(v___x_676_, sizeof(void*)*1 + 4);
v___x_678_ = lean_box(0);
v___x_679_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_677_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = l_Lean_instInhabitedExpr;
v___x_681_ = lean_array_get_borrowed(v___x_680_, v_args_658_, v_a_661_);
lean_inc_ref(v_b_660_);
lean_inc(v___x_681_);
v___x_682_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_659_, v___x_681_, v_b_660_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_693_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_693_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
uint8_t v___x_687_; 
v___x_687_ = lean_unbox(v_a_683_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
lean_dec(v_a_661_);
lean_dec_ref(v_b_660_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_a_683_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_678_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_689_);
v___x_691_ = v___x_685_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_del_object(v___x_685_);
lean_dec(v_a_683_);
v_a_669_ = v___x_679_;
goto v___jp_668_;
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec(v_a_661_);
lean_dec_ref(v_b_660_);
v_a_694_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_682_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_682_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
else
{
v_a_669_ = v___x_679_;
goto v___jp_668_;
}
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_add(v_a_661_, v___x_670_);
lean_dec(v_a_661_);
lean_inc_ref(v_a_669_);
v_a_661_ = v___x_671_;
v_b_662_ = v_a_669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(lean_object* v_upperBound_702_, lean_object* v_args_703_, uint8_t v_mode_704_, lean_object* v_b_705_, lean_object* v_a_706_, lean_object* v_b_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = lean_nat_dec_lt(v_a_706_, v_upperBound_702_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec(v_a_706_);
lean_dec_ref(v_b_705_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_b_707_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec_ref(v_b_707_);
v___x_715_ = lean_array_fget_borrowed(v_args_703_, v_a_706_);
lean_inc_ref(v_b_705_);
lean_inc(v___x_715_);
v___x_716_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_704_, v___x_715_, v_b_705_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_732_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_732_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_732_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_732_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_box(0);
v___x_722_ = lean_unbox(v_a_717_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
lean_dec(v_a_706_);
lean_dec_ref(v_b_705_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v_a_717_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_721_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_724_);
v___x_726_ = v___x_719_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_del_object(v___x_719_);
lean_dec(v_a_717_);
v___x_728_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_a_706_, v___x_729_);
lean_dec(v_a_706_);
v_a_706_ = v___x_730_;
v_b_707_ = v___x_728_;
goto _start;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v_a_706_);
lean_dec_ref(v_b_705_);
v_a_733_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_716_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_716_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(uint8_t v_mode_741_, lean_object* v_b_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
if (lean_obj_tag(v_x_743_) == 5)
{
lean_object* v_fn_751_; lean_object* v_arg_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_fn_751_ = lean_ctor_get(v_x_743_, 0);
lean_inc_ref(v_fn_751_);
v_arg_752_ = lean_ctor_get(v_x_743_, 1);
lean_inc_ref(v_arg_752_);
lean_dec_ref(v_x_743_);
v___x_753_ = lean_array_set(v_x_744_, v_x_745_, v_arg_752_);
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_sub(v_x_745_, v___x_754_);
lean_dec(v_x_745_);
v_x_743_ = v_fn_751_;
v_x_744_ = v___x_753_;
v_x_745_ = v___x_755_;
goto _start;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec(v_x_745_);
v___x_757_ = lean_array_get_size(v_x_744_);
v___x_758_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_x_743_, v___x_757_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref(v___x_758_);
v___x_760_ = lean_array_get_size(v_a_759_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
lean_inc_ref(v_b_742_);
v___x_763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_760_, v_a_759_, v_x_744_, v_mode_741_, v_b_742_, v___x_761_, v___x_762_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v_a_759_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_797_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_797_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_797_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_797_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_fst_768_; 
v_fst_768_ = lean_ctor_get(v_a_764_, 0);
lean_inc(v_fst_768_);
lean_dec(v_a_764_);
if (lean_obj_tag(v_fst_768_) == 0)
{
lean_object* v___x_769_; 
lean_del_object(v___x_766_);
v___x_769_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_757_, v_x_744_, v_mode_741_, v_b_742_, v___x_760_, v___x_762_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec_ref(v_x_744_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_784_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_784_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_784_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_784_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_fst_774_; 
v_fst_774_ = lean_ctor_get(v_a_770_, 0);
lean_inc(v_fst_774_);
lean_dec(v_a_770_);
if (lean_obj_tag(v_fst_774_) == 0)
{
uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_775_ = 1;
v___x_776_ = lean_box(v___x_775_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_776_);
v___x_778_ = v___x_772_;
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
else
{
lean_object* v_val_780_; lean_object* v___x_782_; 
v_val_780_ = lean_ctor_get(v_fst_774_, 0);
lean_inc(v_val_780_);
lean_dec_ref(v_fst_774_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_val_780_);
v___x_782_ = v___x_772_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_val_780_);
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
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_a_785_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_769_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_769_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v_val_793_; lean_object* v___x_795_; 
lean_dec_ref(v_x_744_);
lean_dec_ref(v_b_742_);
v_val_793_ = lean_ctor_get(v_fst_768_, 0);
lean_inc(v_val_793_);
lean_dec_ref(v_fst_768_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v_val_793_);
v___x_795_ = v___x_766_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_val_793_);
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
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v_x_744_);
lean_dec_ref(v_b_742_);
v_a_798_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_763_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_763_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v_x_744_);
lean_dec_ref(v_b_742_);
v_a_806_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_758_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_758_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(uint8_t v_mode_814_, lean_object* v_a_815_, lean_object* v_b_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_d_823_; lean_object* v_e_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; 
switch(lean_obj_tag(v_a_815_))
{
case 11:
{
lean_object* v_struct_833_; lean_object* v___x_834_; 
v_struct_833_ = lean_ctor_get(v_a_815_, 2);
lean_inc_ref(v_struct_833_);
lean_dec_ref(v_a_815_);
v___x_834_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_814_, v_struct_833_, v_b_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_834_;
}
case 5:
{
lean_object* v_dummy_835_; lean_object* v_nargs_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_dummy_835_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_836_ = l_Lean_Expr_getAppNumArgs(v_a_815_);
lean_inc(v_nargs_836_);
v___x_837_ = lean_mk_array(v_nargs_836_, v_dummy_835_);
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_sub(v_nargs_836_, v___x_838_);
lean_dec(v_nargs_836_);
v___x_840_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_814_, v_b_816_, v_a_815_, v___x_837_, v___x_839_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_840_;
}
case 6:
{
lean_object* v_binderType_841_; lean_object* v_body_842_; 
v_binderType_841_ = lean_ctor_get(v_a_815_, 1);
lean_inc_ref(v_binderType_841_);
v_body_842_ = lean_ctor_get(v_a_815_, 2);
lean_inc_ref(v_body_842_);
lean_dec_ref(v_a_815_);
v_d_823_ = v_binderType_841_;
v_e_824_ = v_body_842_;
v___y_825_ = v_a_817_;
v___y_826_ = v_a_818_;
v___y_827_ = v_a_819_;
v___y_828_ = v_a_820_;
goto v___jp_822_;
}
case 7:
{
lean_object* v_binderType_843_; lean_object* v_body_844_; 
v_binderType_843_ = lean_ctor_get(v_a_815_, 1);
lean_inc_ref(v_binderType_843_);
v_body_844_ = lean_ctor_get(v_a_815_, 2);
lean_inc_ref(v_body_844_);
lean_dec_ref(v_a_815_);
v_d_823_ = v_binderType_843_;
v_e_824_ = v_body_844_;
v___y_825_ = v_a_817_;
v___y_826_ = v_a_818_;
v___y_827_ = v_a_819_;
v___y_828_ = v_a_820_;
goto v___jp_822_;
}
case 8:
{
lean_object* v_value_845_; lean_object* v_body_846_; lean_object* v___x_847_; 
v_value_845_ = lean_ctor_get(v_a_815_, 2);
lean_inc_ref(v_value_845_);
v_body_846_ = lean_ctor_get(v_a_815_, 3);
lean_inc_ref(v_body_846_);
lean_dec_ref(v_a_815_);
lean_inc_ref(v_b_816_);
v___x_847_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_814_, v_value_845_, v_b_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; uint8_t v___x_849_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
v___x_849_ = lean_unbox(v_a_848_);
lean_dec(v_a_848_);
if (v___x_849_ == 0)
{
lean_dec_ref(v_body_846_);
lean_dec_ref(v_b_816_);
return v___x_847_;
}
else
{
lean_object* v___x_850_; 
lean_dec_ref(v___x_847_);
v___x_850_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_814_, v_body_846_, v_b_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_850_;
}
}
else
{
lean_dec_ref(v_body_846_);
lean_dec_ref(v_b_816_);
return v___x_847_;
}
}
default: 
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec_ref(v_b_816_);
lean_dec_ref(v_a_815_);
v___x_851_ = 1;
v___x_852_ = lean_box(v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
v___jp_822_:
{
lean_object* v___x_829_; 
lean_inc_ref(v_b_816_);
v___x_829_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_814_, v_d_823_, v_b_816_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; uint8_t v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
v___x_831_ = lean_unbox(v_a_830_);
lean_dec(v_a_830_);
if (v___x_831_ == 0)
{
lean_dec_ref(v_e_824_);
lean_dec_ref(v_b_816_);
return v___x_829_;
}
else
{
lean_object* v___x_832_; 
lean_dec_ref(v___x_829_);
v___x_832_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_814_, v_e_824_, v_b_816_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_832_;
}
}
else
{
lean_dec_ref(v_e_824_);
lean_dec_ref(v_b_816_);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(uint8_t v_mode_854_, lean_object* v_a_855_, lean_object* v_b_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_854_, v_a_855_, v_b_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_878_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_878_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_878_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_878_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v___x_867_; 
v___x_867_ = lean_unbox(v_a_863_);
lean_dec(v_a_863_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_868_ = 1;
v___x_869_ = lean_box(v___x_868_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_869_);
v___x_871_ = v___x_865_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_873_ = 0;
v___x_874_ = lean_box(v___x_873_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_874_);
v___x_876_ = v___x_865_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(lean_object* v_mode_879_, lean_object* v_a_880_, lean_object* v_b_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
uint8_t v_mode_boxed_887_; lean_object* v_res_888_; 
v_mode_boxed_887_ = lean_unbox(v_mode_879_);
v_res_888_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_boxed_887_, v_a_880_, v_b_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(lean_object* v_mode_889_, lean_object* v_a_u2081_890_, lean_object* v_a_u2082_891_, lean_object* v_b_u2081_892_, lean_object* v_b_u2082_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
uint8_t v_mode_boxed_899_; lean_object* v_res_900_; 
v_mode_boxed_899_ = lean_unbox(v_mode_889_);
v_res_900_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_boxed_899_, v_a_u2081_890_, v_a_u2082_891_, v_b_u2081_892_, v_b_u2082_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(lean_object* v_upperBound_901_, lean_object* v_args_902_, lean_object* v_mode_903_, lean_object* v_b_904_, lean_object* v_a_905_, lean_object* v_b_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
uint8_t v_mode_boxed_912_; lean_object* v_res_913_; 
v_mode_boxed_912_ = lean_unbox(v_mode_903_);
v_res_913_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_901_, v_args_902_, v_mode_boxed_912_, v_b_904_, v_a_905_, v_b_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec_ref(v_args_902_);
lean_dec(v_upperBound_901_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object* v_mode_914_, lean_object* v_a_915_, lean_object* v_b_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
uint8_t v_mode_boxed_922_; lean_object* v_res_923_; 
v_mode_boxed_922_ = lean_unbox(v_mode_914_);
v_res_923_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_boxed_922_, v_a_915_, v_b_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object* v_mode_924_, lean_object* v_a_925_, lean_object* v_b_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
uint8_t v_mode_boxed_932_; lean_object* v_res_933_; 
v_mode_boxed_932_ = lean_unbox(v_mode_924_);
v_res_933_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_boxed_932_, v_a_925_, v_b_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object* v_upperBound_934_, lean_object* v_a_935_, lean_object* v_args_936_, lean_object* v_mode_937_, lean_object* v_b_938_, lean_object* v_a_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint8_t v_mode_boxed_946_; lean_object* v_res_947_; 
v_mode_boxed_946_ = lean_unbox(v_mode_937_);
v_res_947_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_934_, v_a_935_, v_args_936_, v_mode_boxed_946_, v_b_938_, v_a_939_, v_b_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec_ref(v_args_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_upperBound_934_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object* v_mode_948_, lean_object* v_a_949_, lean_object* v_b_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
uint8_t v_mode_boxed_956_; lean_object* v_res_957_; 
v_mode_boxed_956_ = lean_unbox(v_mode_948_);
v_res_957_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_boxed_956_, v_a_949_, v_b_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(lean_object* v_upperBound_958_, lean_object* v___x_959_, lean_object* v___x_960_, lean_object* v_mode_961_, lean_object* v_a_962_, lean_object* v_b_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v_mode_boxed_969_; lean_object* v_res_970_; 
v_mode_boxed_969_ = lean_unbox(v_mode_961_);
v_res_970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_958_, v___x_959_, v___x_960_, v_mode_boxed_969_, v_a_962_, v_b_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec_ref(v___x_960_);
lean_dec_ref(v___x_959_);
lean_dec(v_upperBound_958_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(lean_object* v_mode_971_, lean_object* v_b_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v_mode_boxed_981_; lean_object* v_res_982_; 
v_mode_boxed_981_ = lean_unbox(v_mode_971_);
v_res_982_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_981_, v_b_972_, v_x_973_, v_x_974_, v_x_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(lean_object* v_upperBound_983_, lean_object* v_a_984_, lean_object* v___x_985_, lean_object* v___x_986_, lean_object* v_mode_987_, lean_object* v_a_988_, lean_object* v_b_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_mode_boxed_995_; lean_object* v_res_996_; 
v_mode_boxed_995_ = lean_unbox(v_mode_987_);
v_res_996_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_983_, v_a_984_, v___x_985_, v___x_986_, v_mode_boxed_995_, v_a_988_, v_b_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v___x_986_);
lean_dec_ref(v___x_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_upperBound_983_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(lean_object* v_mode_997_, lean_object* v_a_998_, lean_object* v_b_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
uint8_t v_mode_boxed_1005_; lean_object* v_res_1006_; 
v_mode_boxed_1005_ = lean_unbox(v_mode_997_);
v_res_1006_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_boxed_1005_, v_a_998_, v_b_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(lean_object* v_mode_1007_, lean_object* v_a_1008_, lean_object* v_b_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
uint8_t v_mode_boxed_1015_; lean_object* v_res_1016_; 
v_mode_boxed_1015_ = lean_unbox(v_mode_1007_);
v_res_1016_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_boxed_1015_, v_a_1008_, v_b_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(lean_object* v_upperBound_1017_, lean_object* v___x_1018_, lean_object* v___x_1019_, uint8_t v_mode_1020_, lean_object* v_inst_1021_, lean_object* v_R_1022_, lean_object* v_a_1023_, lean_object* v_b_1024_, lean_object* v_c_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_1017_, v___x_1018_, v___x_1019_, v_mode_1020_, v_a_1023_, v_b_1024_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(lean_object* v_upperBound_1032_, lean_object* v___x_1033_, lean_object* v___x_1034_, lean_object* v_mode_1035_, lean_object* v_inst_1036_, lean_object* v_R_1037_, lean_object* v_a_1038_, lean_object* v_b_1039_, lean_object* v_c_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v_mode_boxed_1046_; lean_object* v_res_1047_; 
v_mode_boxed_1046_ = lean_unbox(v_mode_1035_);
v_res_1047_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_1032_, v___x_1033_, v___x_1034_, v_mode_boxed_1046_, v_inst_1036_, v_R_1037_, v_a_1038_, v_b_1039_, v_c_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec_ref(v___x_1034_);
lean_dec_ref(v___x_1033_);
lean_dec(v_upperBound_1032_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(lean_object* v_upperBound_1048_, lean_object* v_a_1049_, lean_object* v___x_1050_, lean_object* v___x_1051_, uint8_t v_mode_1052_, lean_object* v_inst_1053_, lean_object* v_R_1054_, lean_object* v_a_1055_, lean_object* v_b_1056_, lean_object* v_c_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_1048_, v_a_1049_, v___x_1050_, v___x_1051_, v_mode_1052_, v_a_1055_, v_b_1056_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(lean_object* v_upperBound_1064_, lean_object* v_a_1065_, lean_object* v___x_1066_, lean_object* v___x_1067_, lean_object* v_mode_1068_, lean_object* v_inst_1069_, lean_object* v_R_1070_, lean_object* v_a_1071_, lean_object* v_b_1072_, lean_object* v_c_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
uint8_t v_mode_boxed_1079_; lean_object* v_res_1080_; 
v_mode_boxed_1079_ = lean_unbox(v_mode_1068_);
v_res_1080_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_1064_, v_a_1065_, v___x_1066_, v___x_1067_, v_mode_boxed_1079_, v_inst_1069_, v_R_1070_, v_a_1071_, v_b_1072_, v_c_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec_ref(v___x_1067_);
lean_dec_ref(v___x_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_upperBound_1064_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(lean_object* v_upperBound_1081_, lean_object* v_args_1082_, uint8_t v_mode_1083_, lean_object* v_b_1084_, lean_object* v_inst_1085_, lean_object* v_R_1086_, lean_object* v_a_1087_, lean_object* v_b_1088_, lean_object* v_c_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_1081_, v_args_1082_, v_mode_1083_, v_b_1084_, v_a_1087_, v_b_1088_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(lean_object* v_upperBound_1096_, lean_object* v_args_1097_, lean_object* v_mode_1098_, lean_object* v_b_1099_, lean_object* v_inst_1100_, lean_object* v_R_1101_, lean_object* v_a_1102_, lean_object* v_b_1103_, lean_object* v_c_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v_mode_boxed_1110_; lean_object* v_res_1111_; 
v_mode_boxed_1110_ = lean_unbox(v_mode_1098_);
v_res_1111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_1096_, v_args_1097_, v_mode_boxed_1110_, v_b_1099_, v_inst_1100_, v_R_1101_, v_a_1102_, v_b_1103_, v_c_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_args_1097_);
lean_dec(v_upperBound_1096_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(lean_object* v_upperBound_1112_, lean_object* v_a_1113_, lean_object* v_args_1114_, uint8_t v_mode_1115_, lean_object* v_b_1116_, lean_object* v_inst_1117_, lean_object* v_R_1118_, lean_object* v_a_1119_, lean_object* v_b_1120_, lean_object* v_c_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_1112_, v_a_1113_, v_args_1114_, v_mode_1115_, v_b_1116_, v_a_1119_, v_b_1120_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(lean_object* v_upperBound_1128_, lean_object* v_a_1129_, lean_object* v_args_1130_, lean_object* v_mode_1131_, lean_object* v_b_1132_, lean_object* v_inst_1133_, lean_object* v_R_1134_, lean_object* v_a_1135_, lean_object* v_b_1136_, lean_object* v_c_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v_mode_boxed_1143_; lean_object* v_res_1144_; 
v_mode_boxed_1143_ = lean_unbox(v_mode_1131_);
v_res_1144_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_1128_, v_a_1129_, v_args_1130_, v_mode_boxed_1143_, v_b_1132_, v_inst_1133_, v_R_1134_, v_a_1135_, v_b_1136_, v_c_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec_ref(v_args_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_upperBound_1128_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main(lean_object* v_a_1145_, lean_object* v_b_1146_, uint8_t v_mode_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1147_, v_a_1145_, v_b_1146_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main___boxed(lean_object* v_a_1154_, lean_object* v_b_1155_, lean_object* v_mode_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
uint8_t v_mode_boxed_1162_; lean_object* v_res_1163_; 
v_mode_boxed_1162_ = lean_unbox(v_mode_1156_);
v_res_1163_ = l_Lean_Meta_ACLt_main(v_a_1154_, v_b_1155_, v_mode_boxed_1162_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt(lean_object* v_a_1164_, lean_object* v_b_1165_, uint8_t v_mode_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1166_, v_a_1164_, v_b_1165_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt___boxed(lean_object* v_a_1173_, lean_object* v_b_1174_, lean_object* v_mode_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
uint8_t v_mode_boxed_1181_; lean_object* v_res_1182_; 
v_mode_boxed_1181_ = lean_unbox(v_mode_1175_);
v_res_1182_ = l_Lean_Meta_acLt(v_a_1173_, v_b_1174_, v_mode_boxed_1181_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v_res_1182_;
}
}
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ACLt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_DiscrTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config = _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config();
lean_mark_persistent(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_ACLt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ACLt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_DiscrTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ACLt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_ACLt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_ACLt(builtin);
}
#ifdef __cplusplus
}
#endif
