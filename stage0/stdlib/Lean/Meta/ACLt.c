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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* v___x_101_; lean_object* v_config_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_122_; 
v___x_101_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config;
v_config_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_122_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_122_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_config_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_122_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint8_t v_trackZetaDelta_106_; lean_object* v_zetaDeltaSet_107_; lean_object* v_lctx_108_; lean_object* v_localInstances_109_; lean_object* v_defEqCtx_x3f_110_; lean_object* v_synthPendingDepth_111_; lean_object* v_canUnfold_x3f_112_; uint8_t v_univApprox_113_; uint8_t v_inTypeClassResolution_114_; uint8_t v_cacheInferType_115_; uint64_t v___x_116_; lean_object* v___x_118_; 
v_trackZetaDelta_106_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7);
v_zetaDeltaSet_107_ = lean_ctor_get(v_a_94_, 1);
v_lctx_108_ = lean_ctor_get(v_a_94_, 2);
v_localInstances_109_ = lean_ctor_get(v_a_94_, 3);
v_defEqCtx_x3f_110_ = lean_ctor_get(v_a_94_, 4);
v_synthPendingDepth_111_ = lean_ctor_get(v_a_94_, 5);
v_canUnfold_x3f_112_ = lean_ctor_get(v_a_94_, 6);
v_univApprox_113_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_114_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7 + 2);
v_cacheInferType_115_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7 + 3);
v___x_116_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_102_);
if (v_isShared_105_ == 0)
{
v___x_118_ = v___x_104_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_config_102_);
v___x_118_ = v_reuseFailAlloc_121_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_ctor_set_uint64(v___x_118_, sizeof(void*)*1, v___x_116_);
lean_inc(v_canUnfold_x3f_112_);
lean_inc(v_synthPendingDepth_111_);
lean_inc(v_defEqCtx_x3f_110_);
lean_inc_ref(v_localInstances_109_);
lean_inc_ref(v_lctx_108_);
lean_inc(v_zetaDeltaSet_107_);
v___x_119_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_zetaDeltaSet_107_);
lean_ctor_set(v___x_119_, 2, v_lctx_108_);
lean_ctor_set(v___x_119_, 3, v_localInstances_109_);
lean_ctor_set(v___x_119_, 4, v_defEqCtx_x3f_110_);
lean_ctor_set(v___x_119_, 5, v_synthPendingDepth_111_);
lean_ctor_set(v___x_119_, 6, v_canUnfold_x3f_112_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*7, v_trackZetaDelta_106_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*7 + 1, v_univApprox_113_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*7 + 2, v_inTypeClassResolution_114_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*7 + 3, v_cacheInferType_115_);
v___x_120_ = l_Lean_Meta_DiscrTree_reduce(v_e_93_, v___x_119_, v_a_95_, v_a_96_, v_a_97_);
lean_dec_ref(v___x_119_);
return v___x_120_;
}
}
}
default: 
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v_e_93_);
return v___x_123_;
}
}
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v_e_93_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce___boxed(lean_object* v_mode_125_, lean_object* v_e_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
uint8_t v_mode_boxed_132_; lean_object* v_res_133_; 
v_mode_boxed_132_ = lean_unbox(v_mode_125_);
v_res_133_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_boxed_132_, v_e_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(lean_object* v_f_136_, lean_object* v_numArgs_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = l_Lean_Expr_hasLooseBVars(v_f_136_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_getFunInfoNArgs(v_f_136_, v_numArgs_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_153_; 
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
lean_object* v_paramInfo_149_; lean_object* v___x_151_; 
v_paramInfo_149_ = lean_ctor_get(v_a_145_, 0);
lean_inc_ref(v_paramInfo_149_);
lean_dec(v_a_145_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v_paramInfo_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_paramInfo_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_144_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_144_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
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
else
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_numArgs_137_);
lean_dec_ref(v_f_136_);
v___x_162_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0));
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___boxed(lean_object* v_f_164_, lean_object* v_numArgs_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_f_164_, v_numArgs_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(lean_object* v_msg_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___f_179_; lean_object* v___x_16129__overap_180_; lean_object* v___x_181_; 
v___f_179_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0));
v___x_16129__overap_180_ = lean_panic_fn(v___f_179_, v_msg_173_);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
v___x_181_ = lean_apply_5(v___x_16129__overap_180_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, lean_box(0));
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v_msg_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(lean_object* v_msg_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = l_Lean_instInhabitedLocalDecl_default;
v___x_191_ = lean_panic_fn(v___x_190_, v_msg_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(uint8_t v_mode_192_, lean_object* v_a_u2081_193_, lean_object* v_a_u2082_194_, lean_object* v_b_u2081_195_, lean_object* v_b_u2082_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; 
lean_inc_ref(v_b_u2081_195_);
lean_inc_ref(v_a_u2081_193_);
v___x_202_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_192_, v_a_u2081_193_, v_b_u2081_195_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; uint8_t v___x_204_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
v___x_204_ = lean_unbox(v_a_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec_ref(v___x_202_);
v___x_205_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_192_, v_b_u2081_195_, v_a_u2081_193_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_215_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
uint8_t v___x_210_; 
v___x_210_ = lean_unbox(v_a_206_);
lean_dec(v_a_206_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
lean_del_object(v___x_208_);
lean_dec(v_a_203_);
v___x_211_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_192_, v_a_u2082_194_, v_b_u2082_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
return v___x_211_;
}
else
{
lean_object* v___x_213_; 
lean_dec_ref(v_b_u2082_196_);
lean_dec_ref(v_a_u2082_194_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v_a_203_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_203_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_dec(v_a_203_);
lean_dec_ref(v_b_u2082_196_);
lean_dec_ref(v_a_u2082_194_);
return v___x_205_;
}
}
else
{
lean_dec(v_a_203_);
lean_dec_ref(v_b_u2082_196_);
lean_dec_ref(v_b_u2081_195_);
lean_dec_ref(v_a_u2082_194_);
lean_dec_ref(v_a_u2081_193_);
return v___x_202_;
}
}
else
{
lean_dec_ref(v_b_u2082_196_);
lean_dec_ref(v_b_u2081_195_);
lean_dec_ref(v_a_u2082_194_);
lean_dec_ref(v_a_u2081_193_);
return v___x_202_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_219_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2));
v___x_220_ = lean_unsigned_to_nat(14u);
v___x_221_ = lean_unsigned_to_nat(22u);
v___x_222_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1));
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0));
v___x_224_ = l_mkPanicMessageWithDecl(v___x_223_, v___x_222_, v___x_221_, v___x_220_, v___x_219_);
return v___x_224_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0(void){
_start:
{
lean_object* v___x_225_; lean_object* v_dummy_226_; 
v___x_225_ = lean_box(0);
v_dummy_226_ = l_Lean_Expr_sort___override(v___x_225_);
return v_dummy_226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(lean_object* v_upperBound_230_, lean_object* v_a_231_, lean_object* v___x_232_, lean_object* v___x_233_, uint8_t v_mode_234_, lean_object* v_a_235_, lean_object* v_b_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_a_243_; uint8_t v___x_247_; 
v___x_247_ = lean_nat_dec_lt(v_a_235_, v_upperBound_230_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v_a_235_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v_b_236_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v_isInstance_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v_b_236_);
v___x_249_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_250_ = lean_array_get_borrowed(v___x_249_, v_a_231_, v_a_235_);
v_isInstance_251_ = lean_ctor_get_uint8(v___x_250_, sizeof(void*)*1 + 4);
v___x_252_ = lean_box(0);
v___x_253_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_251_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = l_Lean_instInhabitedExpr;
v___x_255_ = lean_array_get_borrowed(v___x_254_, v___x_232_, v_a_235_);
v___x_256_ = lean_array_get_borrowed(v___x_254_, v___x_233_, v_a_235_);
lean_inc(v___x_256_);
lean_inc(v___x_255_);
v___x_257_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_234_, v___x_255_, v___x_256_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_288_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_288_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_288_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_288_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
uint8_t v___x_262_; 
v___x_262_ = lean_unbox(v_a_258_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_del_object(v___x_260_);
lean_inc(v___x_255_);
lean_inc(v___x_256_);
v___x_263_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_234_, v___x_256_, v___x_255_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_274_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_274_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_274_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_274_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
uint8_t v___x_268_; 
v___x_268_ = lean_unbox(v_a_264_);
lean_dec(v_a_264_);
if (v___x_268_ == 0)
{
lean_del_object(v___x_266_);
lean_dec(v_a_258_);
v_a_243_ = v___x_253_;
goto v___jp_242_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
lean_dec(v_a_235_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_a_258_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_252_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_270_);
v___x_272_ = v___x_266_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec(v_a_258_);
lean_dec(v_a_235_);
v_a_275_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_263_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_263_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
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
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
lean_dec(v_a_235_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v_a_258_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_252_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_284_);
v___x_286_ = v___x_260_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v_a_235_);
v_a_289_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_257_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_257_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
v_a_243_ = v___x_253_;
goto v___jp_242_;
}
}
v___jp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_a_235_, v___x_244_);
lean_dec(v_a_235_);
v_a_235_ = v___x_245_;
v_b_236_ = v_a_243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(lean_object* v_upperBound_297_, lean_object* v___x_298_, lean_object* v___x_299_, uint8_t v_mode_300_, lean_object* v_a_301_, lean_object* v_b_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = lean_nat_dec_lt(v_a_301_, v_upperBound_297_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec(v_a_301_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v_b_302_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec_ref(v_b_302_);
v___x_310_ = l_Lean_instInhabitedExpr;
v___x_311_ = lean_array_get_borrowed(v___x_310_, v___x_298_, v_a_301_);
v___x_312_ = lean_array_get_borrowed(v___x_310_, v___x_299_, v_a_301_);
lean_inc(v___x_312_);
lean_inc(v___x_311_);
v___x_313_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_300_, v___x_311_, v___x_312_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_349_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_349_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_349_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_349_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_box(0);
v___x_319_ = lean_unbox(v_a_314_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_del_object(v___x_316_);
lean_inc(v___x_311_);
lean_inc(v___x_312_);
v___x_320_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_300_, v___x_312_, v___x_311_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_335_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_335_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_335_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_335_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
uint8_t v___x_325_; 
v___x_325_ = lean_unbox(v_a_321_);
lean_dec(v_a_321_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_del_object(v___x_323_);
lean_dec(v_a_314_);
v___x_326_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_a_301_, v___x_327_);
lean_dec(v_a_301_);
v_a_301_ = v___x_328_;
v_b_302_ = v___x_326_;
goto _start;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
lean_dec(v_a_301_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_a_314_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_318_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_331_);
v___x_333_ = v___x_323_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v_a_314_);
lean_dec(v_a_301_);
v_a_336_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_320_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_320_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
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
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
lean_dec(v_a_301_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v_a_314_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_318_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_345_);
v___x_347_ = v___x_316_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_a_301_);
v_a_350_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_313_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_313_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(uint8_t v_mode_358_, lean_object* v_a_359_, lean_object* v_b_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_aFn_366_; lean_object* v_bFn_367_; lean_object* v___x_368_; 
v_aFn_366_ = l_Lean_Expr_getAppFn(v_a_359_);
v_bFn_367_ = l_Lean_Expr_getAppFn(v_b_360_);
lean_inc_ref(v_bFn_367_);
lean_inc_ref(v_aFn_366_);
v___x_368_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_358_, v_aFn_366_, v_bFn_367_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_467_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_467_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_467_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_467_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint8_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 1;
v___x_374_ = lean_unbox(v_a_369_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
lean_del_object(v___x_371_);
lean_inc_ref(v_aFn_366_);
v___x_375_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_358_, v_bFn_367_, v_aFn_366_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; uint8_t v___x_377_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
v___x_377_ = lean_unbox(v_a_376_);
if (v___x_377_ == 0)
{
lean_object* v_dummy_378_; lean_object* v_nargs_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_nargs_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
lean_dec(v_a_369_);
v_dummy_378_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_379_ = l_Lean_Expr_getAppNumArgs(v_a_359_);
lean_inc(v_nargs_379_);
v___x_380_ = lean_mk_array(v_nargs_379_, v_dummy_378_);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_sub(v_nargs_379_, v___x_381_);
lean_dec(v_nargs_379_);
v___x_383_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_359_, v___x_380_, v___x_382_);
v_nargs_384_ = l_Lean_Expr_getAppNumArgs(v_b_360_);
lean_inc(v_nargs_384_);
v___x_385_ = lean_mk_array(v_nargs_384_, v_dummy_378_);
v___x_386_ = lean_nat_sub(v_nargs_384_, v___x_381_);
lean_dec(v_nargs_384_);
v___x_387_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_b_360_, v___x_385_, v___x_386_);
v___x_388_ = lean_array_get_size(v___x_383_);
v___x_389_ = lean_array_get_size(v___x_387_);
v___x_390_ = lean_nat_dec_lt(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
uint8_t v___x_391_; 
v___x_391_ = lean_nat_dec_lt(v___x_389_, v___x_388_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
lean_dec_ref(v___x_375_);
v___x_392_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_366_, v___x_388_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref(v___x_392_);
v___x_394_ = lean_array_get_size(v_a_393_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_394_, v_a_393_, v___x_383_, v___x_387_, v_mode_358_, v___x_395_, v___x_396_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_393_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_429_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_429_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_429_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_429_;
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
lean_object* v___x_403_; 
lean_del_object(v___x_400_);
v___x_403_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_388_, v___x_383_, v___x_387_, v_mode_358_, v___x_394_, v___x_396_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_383_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_416_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_416_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_fst_408_; 
v_fst_408_ = lean_ctor_get(v_a_404_, 0);
lean_inc(v_fst_408_);
lean_dec(v_a_404_);
if (lean_obj_tag(v_fst_408_) == 0)
{
lean_object* v___x_410_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_a_376_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_376_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v_val_412_; lean_object* v___x_414_; 
lean_dec(v_a_376_);
v_val_412_ = lean_ctor_get(v_fst_408_, 0);
lean_inc(v_val_412_);
lean_dec_ref(v_fst_408_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_val_412_);
v___x_414_ = v___x_406_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_val_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_a_376_);
v_a_417_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_403_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_403_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v_val_425_; lean_object* v___x_427_; 
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_383_);
lean_dec(v_a_376_);
v_val_425_ = lean_ctor_get(v_fst_402_, 0);
lean_inc(v_val_425_);
lean_dec_ref(v_fst_402_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_val_425_);
v___x_427_ = v___x_400_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_val_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_383_);
lean_dec(v_a_376_);
v_a_430_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_397_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_397_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_383_);
lean_dec(v_a_376_);
v_a_438_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_392_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_392_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_383_);
lean_dec(v_a_376_);
lean_dec_ref(v_aFn_366_);
return v___x_375_;
}
}
else
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_383_);
lean_dec(v_a_376_);
lean_dec_ref(v_aFn_366_);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v___x_375_, 0);
lean_dec(v_unused_454_);
v___x_447_ = v___x_375_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_dec(v___x_375_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_box(v___x_373_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_a_376_);
lean_dec_ref(v_aFn_366_);
lean_dec_ref(v_b_360_);
lean_dec_ref(v_a_359_);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v___x_375_, 0);
lean_dec(v_unused_462_);
v___x_456_ = v___x_375_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_dec(v___x_375_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_a_369_);
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_369_);
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
lean_dec(v_a_369_);
lean_dec_ref(v_aFn_366_);
lean_dec_ref(v_b_360_);
lean_dec_ref(v_a_359_);
return v___x_375_;
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_465_; 
lean_dec(v_a_369_);
lean_dec_ref(v_bFn_367_);
lean_dec_ref(v_aFn_366_);
lean_dec_ref(v_b_360_);
lean_dec_ref(v_a_359_);
v___x_463_ = lean_box(v___x_373_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_463_);
v___x_465_ = v___x_371_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_dec_ref(v_bFn_367_);
lean_dec_ref(v_aFn_366_);
lean_dec_ref(v_b_360_);
lean_dec_ref(v_a_359_);
return v___x_368_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6));
v___x_472_ = lean_unsigned_to_nat(27u);
v___x_473_ = lean_unsigned_to_nat(152u);
v___x_474_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5));
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4));
v___x_476_ = l_mkPanicMessageWithDecl(v___x_475_, v___x_474_, v___x_473_, v___x_472_, v___x_471_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(uint8_t v_mode_477_, lean_object* v_a_478_, lean_object* v_b_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_d_486_; lean_object* v_e_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; 
switch(lean_obj_tag(v_a_478_))
{
case 0:
{
lean_object* v_deBruijnIndex_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_deBruijnIndex_495_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_deBruijnIndex_495_);
lean_dec_ref(v_a_478_);
v___x_496_ = l_Lean_Expr_bvarIdx_x21(v_b_479_);
lean_dec_ref(v_b_479_);
v___x_497_ = lean_nat_dec_lt(v_deBruijnIndex_495_, v___x_496_);
lean_dec(v___x_496_);
lean_dec(v_deBruijnIndex_495_);
v___x_498_ = lean_box(v___x_497_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
case 1:
{
lean_object* v_fvarId_500_; lean_object* v___x_501_; 
v_fvarId_500_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_fvarId_500_);
lean_dec_ref(v_a_478_);
lean_inc_ref(v_a_480_);
v___x_501_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_500_, v_a_480_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = l_Lean_Expr_fvarId_x21(v_b_479_);
lean_dec_ref(v_b_479_);
lean_inc_ref(v_a_480_);
v___x_504_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_503_, v_a_480_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_527_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_527_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_527_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_527_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_519_; 
if (lean_obj_tag(v_a_502_) == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_525_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_524_);
v___y_519_ = v___x_525_;
goto v___jp_518_;
}
else
{
lean_object* v_val_526_; 
v_val_526_ = lean_ctor_get(v_a_502_, 0);
lean_inc(v_val_526_);
lean_dec_ref(v_a_502_);
v___y_519_ = v_val_526_;
goto v___jp_518_;
}
v___jp_509_:
{
lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_512_ = l_Lean_LocalDecl_index(v___y_511_);
lean_dec_ref(v___y_511_);
v___x_513_ = lean_nat_dec_lt(v___y_510_, v___x_512_);
lean_dec(v___x_512_);
lean_dec(v___y_510_);
v___x_514_ = lean_box(v___x_513_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_514_);
v___x_516_ = v___x_507_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
v___jp_518_:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_LocalDecl_index(v___y_519_);
lean_dec_ref(v___y_519_);
if (lean_obj_tag(v_a_505_) == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_522_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_521_);
v___y_510_ = v___x_520_;
v___y_511_ = v___x_522_;
goto v___jp_509_;
}
else
{
lean_object* v_val_523_; 
v_val_523_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_val_523_);
lean_dec_ref(v_a_505_);
v___y_510_ = v___x_520_;
v___y_511_ = v_val_523_;
goto v___jp_509_;
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_a_502_);
v_a_528_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_504_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_504_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v_b_479_);
v_a_536_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_501_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_501_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_mvarId_544_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_mvarId_544_);
lean_dec_ref(v_a_478_);
v___x_545_ = l_Lean_Expr_mvarId_x21(v_b_479_);
lean_dec_ref(v_b_479_);
v___x_546_ = l_Lean_Name_lt(v_mvarId_544_, v___x_545_);
lean_dec(v___x_545_);
lean_dec(v_mvarId_544_);
v___x_547_ = lean_box(v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
case 3:
{
lean_object* v_u_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_u_549_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_u_549_);
lean_dec_ref(v_a_478_);
v___x_550_ = l_Lean_Expr_sortLevel_x21(v_b_479_);
lean_dec_ref(v_b_479_);
v___x_551_ = l_Lean_Level_normLt(v_u_549_, v___x_550_);
lean_dec(v___x_550_);
lean_dec(v_u_549_);
v___x_552_ = lean_box(v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
case 4:
{
lean_object* v_declName_554_; lean_object* v___x_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_declName_554_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_declName_554_);
lean_dec_ref(v_a_478_);
v___x_555_ = l_Lean_Expr_constName_x21(v_b_479_);
lean_dec_ref(v_b_479_);
v___x_556_ = l_Lean_Name_lt(v_declName_554_, v___x_555_);
lean_dec(v___x_555_);
lean_dec(v_declName_554_);
v___x_557_ = lean_box(v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
case 5:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_477_, v_a_478_, v_b_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_559_;
}
case 8:
{
lean_object* v_value_560_; lean_object* v_body_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_value_560_ = lean_ctor_get(v_a_478_, 2);
lean_inc_ref(v_value_560_);
v_body_561_ = lean_ctor_get(v_a_478_, 3);
lean_inc_ref(v_body_561_);
lean_dec_ref(v_a_478_);
v___x_562_ = l_Lean_Expr_letValue_x21(v_b_479_);
v___x_563_ = l_Lean_Expr_letBody_x21(v_b_479_);
lean_dec_ref(v_b_479_);
v___x_564_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_477_, v_value_560_, v_body_561_, v___x_562_, v___x_563_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_564_;
}
case 9:
{
lean_object* v_a_565_; lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_a_565_ = lean_ctor_get(v_a_478_, 0);
lean_inc_ref(v_a_565_);
lean_dec_ref(v_a_478_);
v___x_566_ = l_Lean_Expr_litValue_x21(v_b_479_);
lean_dec_ref(v_b_479_);
v___x_567_ = l_Lean_Literal_lt(v_a_565_, v___x_566_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v_a_565_);
v___x_568_ = lean_box(v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
case 10:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v_a_478_);
lean_dec_ref(v_b_479_);
v___x_570_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
v___x_571_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_570_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_571_;
}
case 11:
{
lean_object* v_idx_572_; lean_object* v_struct_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_idx_572_ = lean_ctor_get(v_a_478_, 1);
lean_inc(v_idx_572_);
v_struct_573_ = lean_ctor_get(v_a_478_, 2);
lean_inc_ref(v_struct_573_);
lean_dec_ref(v_a_478_);
v___x_574_ = l_Lean_Expr_projIdx_x21(v_b_479_);
v___x_575_ = lean_nat_dec_eq(v_idx_572_, v___x_574_);
if (v___x_575_ == 0)
{
uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v_struct_573_);
lean_dec_ref(v_b_479_);
v___x_576_ = lean_nat_dec_lt(v_idx_572_, v___x_574_);
lean_dec(v___x_574_);
lean_dec(v_idx_572_);
v___x_577_ = lean_box(v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v___x_574_);
lean_dec(v_idx_572_);
v___x_579_ = l_Lean_Expr_projExpr_x21(v_b_479_);
lean_dec_ref(v_b_479_);
v___x_580_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_477_, v_struct_573_, v___x_579_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_580_;
}
}
default: 
{
lean_object* v_binderType_581_; lean_object* v_body_582_; 
v_binderType_581_ = lean_ctor_get(v_a_478_, 1);
lean_inc_ref(v_binderType_581_);
v_body_582_ = lean_ctor_get(v_a_478_, 2);
lean_inc_ref(v_body_582_);
lean_dec_ref(v_a_478_);
v_d_486_ = v_binderType_581_;
v_e_487_ = v_body_582_;
v___y_488_ = v_a_480_;
v___y_489_ = v_a_481_;
v___y_490_ = v_a_482_;
v___y_491_ = v_a_483_;
goto v___jp_485_;
}
}
v___jp_485_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = l_Lean_Expr_bindingDomain_x21(v_b_479_);
v___x_493_ = l_Lean_Expr_bindingBody_x21(v_b_479_);
lean_dec_ref(v_b_479_);
v___x_494_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_477_, v_d_486_, v_e_487_, v___x_492_, v___x_493_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(uint8_t v_mode_583_, lean_object* v_a_584_, lean_object* v_b_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; 
lean_inc_ref(v_a_584_);
lean_inc_ref(v_b_585_);
v___x_591_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_583_, v_b_585_, v_a_584_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; uint8_t v___x_593_; uint8_t v___x_594_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
v___x_593_ = 1;
v___x_594_ = lean_unbox(v_a_592_);
if (v___x_594_ == 0)
{
uint8_t v___x_595_; uint8_t v___x_596_; uint8_t v___x_597_; 
v___x_595_ = l_Lean_Expr_ctorWeight(v_b_585_);
v___x_596_ = l_Lean_Expr_ctorWeight(v_a_584_);
v___x_597_ = lean_uint8_dec_lt(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec_ref(v___x_591_);
lean_inc_ref(v_b_585_);
lean_inc_ref(v_a_584_);
v___x_598_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_583_, v_a_584_, v_b_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_613_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_613_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v___x_603_; 
v___x_603_ = lean_unbox(v_a_599_);
lean_dec(v_a_599_);
if (v___x_603_ == 0)
{
lean_object* v___x_605_; 
lean_dec_ref(v_b_585_);
lean_dec_ref(v_a_584_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_a_592_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_592_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
else
{
uint8_t v___x_607_; 
lean_dec(v_a_592_);
v___x_607_ = lean_uint8_dec_lt(v___x_596_, v___x_595_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
lean_del_object(v___x_601_);
v___x_608_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_583_, v_a_584_, v_b_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec_ref(v_b_585_);
lean_dec_ref(v_a_584_);
v___x_609_ = lean_box(v___x_593_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_609_);
v___x_611_ = v___x_601_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
else
{
lean_dec(v_a_592_);
lean_dec_ref(v_b_585_);
lean_dec_ref(v_a_584_);
return v___x_598_;
}
}
else
{
lean_dec(v_a_592_);
lean_dec_ref(v_b_585_);
lean_dec_ref(v_a_584_);
return v___x_591_;
}
}
else
{
lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_a_592_);
lean_dec_ref(v_b_585_);
lean_dec_ref(v_a_584_);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_622_);
v___x_615_ = v___x_591_;
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
else
{
lean_dec(v___x_591_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_box(v___x_593_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_617_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_dec_ref(v_b_585_);
lean_dec_ref(v_a_584_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(uint8_t v_mode_623_, lean_object* v_a_624_, lean_object* v_b_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = lean_expr_eqv(v_a_624_, v_b_625_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; 
v___x_632_ = l_Lean_Expr_isMData(v_a_624_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; 
v___x_633_ = l_Lean_Expr_isMData(v_b_625_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_623_, v_a_624_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref(v___x_634_);
v___x_636_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_623_, v_b_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref(v___x_636_);
v___x_638_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_623_, v_a_635_, v_a_637_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_638_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_a_635_);
v_a_639_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_636_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_636_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v_b_625_);
v_a_647_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_634_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_634_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Expr_mdataExpr_x21(v_b_625_);
lean_dec_ref(v_b_625_);
v_b_625_ = v___x_655_;
goto _start;
}
}
else
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Expr_mdataExpr_x21(v_a_624_);
lean_dec_ref(v_a_624_);
v_a_624_ = v___x_657_;
goto _start;
}
}
else
{
uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec_ref(v_b_625_);
lean_dec_ref(v_a_624_);
v___x_659_ = 0;
v___x_660_ = lean_box(v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(lean_object* v_upperBound_662_, lean_object* v_a_663_, lean_object* v_args_664_, uint8_t v_mode_665_, lean_object* v_b_666_, lean_object* v_a_667_, lean_object* v_b_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_a_675_; uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_lt(v_a_667_, v_upperBound_662_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec(v_a_667_);
lean_dec_ref(v_b_666_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v_b_668_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v_isInstance_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec_ref(v_b_668_);
v___x_681_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_682_ = lean_array_get_borrowed(v___x_681_, v_a_663_, v_a_667_);
v_isInstance_683_ = lean_ctor_get_uint8(v___x_682_, sizeof(void*)*1 + 4);
v___x_684_ = lean_box(0);
v___x_685_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_683_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = l_Lean_instInhabitedExpr;
v___x_687_ = lean_array_get_borrowed(v___x_686_, v_args_664_, v_a_667_);
lean_inc_ref(v_b_666_);
lean_inc(v___x_687_);
v___x_688_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_665_, v___x_687_, v_b_666_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_699_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_699_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; 
v___x_693_ = lean_unbox(v_a_689_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
lean_dec(v_a_667_);
lean_dec_ref(v_b_666_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v_a_689_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_684_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_695_);
v___x_697_ = v___x_691_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
else
{
lean_del_object(v___x_691_);
lean_dec(v_a_689_);
v_a_675_ = v___x_685_;
goto v___jp_674_;
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v_a_667_);
lean_dec_ref(v_b_666_);
v_a_700_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_688_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_688_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
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
else
{
v_a_675_ = v___x_685_;
goto v___jp_674_;
}
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_a_667_, v___x_676_);
lean_dec(v_a_667_);
v_a_667_ = v___x_677_;
v_b_668_ = v_a_675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(lean_object* v_upperBound_708_, lean_object* v_args_709_, uint8_t v_mode_710_, lean_object* v_b_711_, lean_object* v_a_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_nat_dec_lt(v_a_712_, v_upperBound_708_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v_a_712_);
lean_dec_ref(v_b_711_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v_b_713_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec_ref(v_b_713_);
v___x_721_ = lean_array_fget_borrowed(v_args_709_, v_a_712_);
lean_inc_ref(v_b_711_);
lean_inc(v___x_721_);
v___x_722_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_710_, v___x_721_, v_b_711_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_738_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_738_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_738_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_738_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = lean_box(0);
v___x_728_ = lean_unbox(v_a_723_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
lean_dec(v_a_712_);
lean_dec_ref(v_b_711_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v_a_723_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_727_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_730_);
v___x_732_ = v___x_725_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_del_object(v___x_725_);
lean_dec(v_a_723_);
v___x_734_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v_a_712_, v___x_735_);
lean_dec(v_a_712_);
v_a_712_ = v___x_736_;
v_b_713_ = v___x_734_;
goto _start;
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_a_712_);
lean_dec_ref(v_b_711_);
v_a_739_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_722_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_722_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(uint8_t v_mode_747_, lean_object* v_b_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
if (lean_obj_tag(v_x_749_) == 5)
{
lean_object* v_fn_757_; lean_object* v_arg_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_fn_757_ = lean_ctor_get(v_x_749_, 0);
lean_inc_ref(v_fn_757_);
v_arg_758_ = lean_ctor_get(v_x_749_, 1);
lean_inc_ref(v_arg_758_);
lean_dec_ref(v_x_749_);
v___x_759_ = lean_array_set(v_x_750_, v_x_751_, v_arg_758_);
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_sub(v_x_751_, v___x_760_);
lean_dec(v_x_751_);
v_x_749_ = v_fn_757_;
v_x_750_ = v___x_759_;
v_x_751_ = v___x_761_;
goto _start;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec(v_x_751_);
v___x_763_ = lean_array_get_size(v_x_750_);
v___x_764_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_x_749_, v___x_763_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_764_);
v___x_766_ = lean_array_get_size(v_a_765_);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
lean_inc_ref(v_b_748_);
v___x_769_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_766_, v_a_765_, v_x_750_, v_mode_747_, v_b_748_, v___x_767_, v___x_768_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v_a_765_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_803_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_803_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_803_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_803_;
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
lean_object* v___x_775_; 
lean_del_object(v___x_772_);
v___x_775_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_763_, v_x_750_, v_mode_747_, v_b_748_, v___x_766_, v___x_768_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec_ref(v_x_750_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_790_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_790_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_790_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_790_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_fst_780_; 
v_fst_780_ = lean_ctor_get(v_a_776_, 0);
lean_inc(v_fst_780_);
lean_dec(v_a_776_);
if (lean_obj_tag(v_fst_780_) == 0)
{
uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_781_ = 1;
v___x_782_ = lean_box(v___x_781_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_782_);
v___x_784_ = v___x_778_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
else
{
lean_object* v_val_786_; lean_object* v___x_788_; 
v_val_786_ = lean_ctor_get(v_fst_780_, 0);
lean_inc(v_val_786_);
lean_dec_ref(v_fst_780_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v_val_786_);
v___x_788_ = v___x_778_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_val_786_);
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
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_791_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_775_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_775_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_val_799_; lean_object* v___x_801_; 
lean_dec_ref(v_x_750_);
lean_dec_ref(v_b_748_);
v_val_799_ = lean_ctor_get(v_fst_774_, 0);
lean_inc(v_val_799_);
lean_dec_ref(v_fst_774_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_val_799_);
v___x_801_ = v___x_772_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_val_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_x_750_);
lean_dec_ref(v_b_748_);
v_a_804_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_769_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_769_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v_x_750_);
lean_dec_ref(v_b_748_);
v_a_812_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_764_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_764_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(uint8_t v_mode_820_, lean_object* v_a_821_, lean_object* v_b_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_d_829_; lean_object* v_e_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; 
switch(lean_obj_tag(v_a_821_))
{
case 11:
{
lean_object* v_struct_839_; lean_object* v___x_840_; 
v_struct_839_ = lean_ctor_get(v_a_821_, 2);
lean_inc_ref(v_struct_839_);
lean_dec_ref(v_a_821_);
v___x_840_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_820_, v_struct_839_, v_b_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_840_;
}
case 5:
{
lean_object* v_dummy_841_; lean_object* v_nargs_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_dummy_841_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_842_ = l_Lean_Expr_getAppNumArgs(v_a_821_);
lean_inc(v_nargs_842_);
v___x_843_ = lean_mk_array(v_nargs_842_, v_dummy_841_);
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_sub(v_nargs_842_, v___x_844_);
lean_dec(v_nargs_842_);
v___x_846_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_820_, v_b_822_, v_a_821_, v___x_843_, v___x_845_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_846_;
}
case 6:
{
lean_object* v_binderType_847_; lean_object* v_body_848_; 
v_binderType_847_ = lean_ctor_get(v_a_821_, 1);
lean_inc_ref(v_binderType_847_);
v_body_848_ = lean_ctor_get(v_a_821_, 2);
lean_inc_ref(v_body_848_);
lean_dec_ref(v_a_821_);
v_d_829_ = v_binderType_847_;
v_e_830_ = v_body_848_;
v___y_831_ = v_a_823_;
v___y_832_ = v_a_824_;
v___y_833_ = v_a_825_;
v___y_834_ = v_a_826_;
goto v___jp_828_;
}
case 7:
{
lean_object* v_binderType_849_; lean_object* v_body_850_; 
v_binderType_849_ = lean_ctor_get(v_a_821_, 1);
lean_inc_ref(v_binderType_849_);
v_body_850_ = lean_ctor_get(v_a_821_, 2);
lean_inc_ref(v_body_850_);
lean_dec_ref(v_a_821_);
v_d_829_ = v_binderType_849_;
v_e_830_ = v_body_850_;
v___y_831_ = v_a_823_;
v___y_832_ = v_a_824_;
v___y_833_ = v_a_825_;
v___y_834_ = v_a_826_;
goto v___jp_828_;
}
case 8:
{
lean_object* v_value_851_; lean_object* v_body_852_; lean_object* v___x_853_; 
v_value_851_ = lean_ctor_get(v_a_821_, 2);
lean_inc_ref(v_value_851_);
v_body_852_ = lean_ctor_get(v_a_821_, 3);
lean_inc_ref(v_body_852_);
lean_dec_ref(v_a_821_);
lean_inc_ref(v_b_822_);
v___x_853_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_820_, v_value_851_, v_b_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; uint8_t v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
v___x_855_ = lean_unbox(v_a_854_);
lean_dec(v_a_854_);
if (v___x_855_ == 0)
{
lean_dec_ref(v_body_852_);
lean_dec_ref(v_b_822_);
return v___x_853_;
}
else
{
lean_object* v___x_856_; 
lean_dec_ref(v___x_853_);
v___x_856_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_820_, v_body_852_, v_b_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_856_;
}
}
else
{
lean_dec_ref(v_body_852_);
lean_dec_ref(v_b_822_);
return v___x_853_;
}
}
default: 
{
uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec_ref(v_b_822_);
lean_dec_ref(v_a_821_);
v___x_857_ = 1;
v___x_858_ = lean_box(v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
v___jp_828_:
{
lean_object* v___x_835_; 
lean_inc_ref(v_b_822_);
v___x_835_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_820_, v_d_829_, v_b_822_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; uint8_t v___x_837_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
v___x_837_ = lean_unbox(v_a_836_);
lean_dec(v_a_836_);
if (v___x_837_ == 0)
{
lean_dec_ref(v_e_830_);
lean_dec_ref(v_b_822_);
return v___x_835_;
}
else
{
lean_object* v___x_838_; 
lean_dec_ref(v___x_835_);
v___x_838_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_820_, v_e_830_, v_b_822_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_838_;
}
}
else
{
lean_dec_ref(v_e_830_);
lean_dec_ref(v_b_822_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(uint8_t v_mode_860_, lean_object* v_a_861_, lean_object* v_b_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_860_, v_a_861_, v_b_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_884_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_884_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_884_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_884_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
uint8_t v___x_873_; 
v___x_873_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = 1;
v___x_875_ = lean_box(v___x_874_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_875_);
v___x_877_ = v___x_871_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
else
{
uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_879_ = 0;
v___x_880_ = lean_box(v___x_879_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_880_);
v___x_882_ = v___x_871_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
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
else
{
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(lean_object* v_mode_885_, lean_object* v_a_886_, lean_object* v_b_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
uint8_t v_mode_boxed_893_; lean_object* v_res_894_; 
v_mode_boxed_893_ = lean_unbox(v_mode_885_);
v_res_894_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_boxed_893_, v_a_886_, v_b_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(lean_object* v_mode_895_, lean_object* v_a_u2081_896_, lean_object* v_a_u2082_897_, lean_object* v_b_u2081_898_, lean_object* v_b_u2082_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
uint8_t v_mode_boxed_905_; lean_object* v_res_906_; 
v_mode_boxed_905_ = lean_unbox(v_mode_895_);
v_res_906_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_boxed_905_, v_a_u2081_896_, v_a_u2082_897_, v_b_u2081_898_, v_b_u2082_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(lean_object* v_upperBound_907_, lean_object* v_args_908_, lean_object* v_mode_909_, lean_object* v_b_910_, lean_object* v_a_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
uint8_t v_mode_boxed_918_; lean_object* v_res_919_; 
v_mode_boxed_918_ = lean_unbox(v_mode_909_);
v_res_919_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_907_, v_args_908_, v_mode_boxed_918_, v_b_910_, v_a_911_, v_b_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec_ref(v_args_908_);
lean_dec(v_upperBound_907_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object* v_mode_920_, lean_object* v_a_921_, lean_object* v_b_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
uint8_t v_mode_boxed_928_; lean_object* v_res_929_; 
v_mode_boxed_928_ = lean_unbox(v_mode_920_);
v_res_929_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_boxed_928_, v_a_921_, v_b_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object* v_mode_930_, lean_object* v_a_931_, lean_object* v_b_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
uint8_t v_mode_boxed_938_; lean_object* v_res_939_; 
v_mode_boxed_938_ = lean_unbox(v_mode_930_);
v_res_939_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_boxed_938_, v_a_931_, v_b_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object* v_upperBound_940_, lean_object* v_a_941_, lean_object* v_args_942_, lean_object* v_mode_943_, lean_object* v_b_944_, lean_object* v_a_945_, lean_object* v_b_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
uint8_t v_mode_boxed_952_; lean_object* v_res_953_; 
v_mode_boxed_952_ = lean_unbox(v_mode_943_);
v_res_953_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_940_, v_a_941_, v_args_942_, v_mode_boxed_952_, v_b_944_, v_a_945_, v_b_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec_ref(v_args_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_upperBound_940_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object* v_mode_954_, lean_object* v_a_955_, lean_object* v_b_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
uint8_t v_mode_boxed_962_; lean_object* v_res_963_; 
v_mode_boxed_962_ = lean_unbox(v_mode_954_);
v_res_963_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_boxed_962_, v_a_955_, v_b_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(lean_object* v_upperBound_964_, lean_object* v___x_965_, lean_object* v___x_966_, lean_object* v_mode_967_, lean_object* v_a_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v_mode_boxed_975_; lean_object* v_res_976_; 
v_mode_boxed_975_ = lean_unbox(v_mode_967_);
v_res_976_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_964_, v___x_965_, v___x_966_, v_mode_boxed_975_, v_a_968_, v_b_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v___x_966_);
lean_dec_ref(v___x_965_);
lean_dec(v_upperBound_964_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(lean_object* v_mode_977_, lean_object* v_b_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v_mode_boxed_987_; lean_object* v_res_988_; 
v_mode_boxed_987_ = lean_unbox(v_mode_977_);
v_res_988_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_987_, v_b_978_, v_x_979_, v_x_980_, v_x_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(lean_object* v_upperBound_989_, lean_object* v_a_990_, lean_object* v___x_991_, lean_object* v___x_992_, lean_object* v_mode_993_, lean_object* v_a_994_, lean_object* v_b_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
uint8_t v_mode_boxed_1001_; lean_object* v_res_1002_; 
v_mode_boxed_1001_ = lean_unbox(v_mode_993_);
v_res_1002_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_989_, v_a_990_, v___x_991_, v___x_992_, v_mode_boxed_1001_, v_a_994_, v_b_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec_ref(v___x_992_);
lean_dec_ref(v___x_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_upperBound_989_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(lean_object* v_mode_1003_, lean_object* v_a_1004_, lean_object* v_b_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
uint8_t v_mode_boxed_1011_; lean_object* v_res_1012_; 
v_mode_boxed_1011_ = lean_unbox(v_mode_1003_);
v_res_1012_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_boxed_1011_, v_a_1004_, v_b_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(lean_object* v_mode_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
uint8_t v_mode_boxed_1021_; lean_object* v_res_1022_; 
v_mode_boxed_1021_ = lean_unbox(v_mode_1013_);
v_res_1022_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_boxed_1021_, v_a_1014_, v_b_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(lean_object* v_upperBound_1023_, lean_object* v___x_1024_, lean_object* v___x_1025_, uint8_t v_mode_1026_, lean_object* v_inst_1027_, lean_object* v_R_1028_, lean_object* v_a_1029_, lean_object* v_b_1030_, lean_object* v_c_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_1023_, v___x_1024_, v___x_1025_, v_mode_1026_, v_a_1029_, v_b_1030_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(lean_object* v_upperBound_1038_, lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_mode_1041_, lean_object* v_inst_1042_, lean_object* v_R_1043_, lean_object* v_a_1044_, lean_object* v_b_1045_, lean_object* v_c_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
uint8_t v_mode_boxed_1052_; lean_object* v_res_1053_; 
v_mode_boxed_1052_ = lean_unbox(v_mode_1041_);
v_res_1053_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_1038_, v___x_1039_, v___x_1040_, v_mode_boxed_1052_, v_inst_1042_, v_R_1043_, v_a_1044_, v_b_1045_, v_c_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v___x_1040_);
lean_dec_ref(v___x_1039_);
lean_dec(v_upperBound_1038_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(lean_object* v_upperBound_1054_, lean_object* v_a_1055_, lean_object* v___x_1056_, lean_object* v___x_1057_, uint8_t v_mode_1058_, lean_object* v_inst_1059_, lean_object* v_R_1060_, lean_object* v_a_1061_, lean_object* v_b_1062_, lean_object* v_c_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_1054_, v_a_1055_, v___x_1056_, v___x_1057_, v_mode_1058_, v_a_1061_, v_b_1062_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(lean_object* v_upperBound_1070_, lean_object* v_a_1071_, lean_object* v___x_1072_, lean_object* v___x_1073_, lean_object* v_mode_1074_, lean_object* v_inst_1075_, lean_object* v_R_1076_, lean_object* v_a_1077_, lean_object* v_b_1078_, lean_object* v_c_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v_mode_boxed_1085_; lean_object* v_res_1086_; 
v_mode_boxed_1085_ = lean_unbox(v_mode_1074_);
v_res_1086_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_1070_, v_a_1071_, v___x_1072_, v___x_1073_, v_mode_boxed_1085_, v_inst_1075_, v_R_1076_, v_a_1077_, v_b_1078_, v_c_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec_ref(v___x_1073_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_upperBound_1070_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(lean_object* v_upperBound_1087_, lean_object* v_args_1088_, uint8_t v_mode_1089_, lean_object* v_b_1090_, lean_object* v_inst_1091_, lean_object* v_R_1092_, lean_object* v_a_1093_, lean_object* v_b_1094_, lean_object* v_c_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_1087_, v_args_1088_, v_mode_1089_, v_b_1090_, v_a_1093_, v_b_1094_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(lean_object* v_upperBound_1102_, lean_object* v_args_1103_, lean_object* v_mode_1104_, lean_object* v_b_1105_, lean_object* v_inst_1106_, lean_object* v_R_1107_, lean_object* v_a_1108_, lean_object* v_b_1109_, lean_object* v_c_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v_mode_boxed_1116_; lean_object* v_res_1117_; 
v_mode_boxed_1116_ = lean_unbox(v_mode_1104_);
v_res_1117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_1102_, v_args_1103_, v_mode_boxed_1116_, v_b_1105_, v_inst_1106_, v_R_1107_, v_a_1108_, v_b_1109_, v_c_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec_ref(v_args_1103_);
lean_dec(v_upperBound_1102_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(lean_object* v_upperBound_1118_, lean_object* v_a_1119_, lean_object* v_args_1120_, uint8_t v_mode_1121_, lean_object* v_b_1122_, lean_object* v_inst_1123_, lean_object* v_R_1124_, lean_object* v_a_1125_, lean_object* v_b_1126_, lean_object* v_c_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_1118_, v_a_1119_, v_args_1120_, v_mode_1121_, v_b_1122_, v_a_1125_, v_b_1126_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(lean_object* v_upperBound_1134_, lean_object* v_a_1135_, lean_object* v_args_1136_, lean_object* v_mode_1137_, lean_object* v_b_1138_, lean_object* v_inst_1139_, lean_object* v_R_1140_, lean_object* v_a_1141_, lean_object* v_b_1142_, lean_object* v_c_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v_mode_boxed_1149_; lean_object* v_res_1150_; 
v_mode_boxed_1149_ = lean_unbox(v_mode_1137_);
v_res_1150_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_1134_, v_a_1135_, v_args_1136_, v_mode_boxed_1149_, v_b_1138_, v_inst_1139_, v_R_1140_, v_a_1141_, v_b_1142_, v_c_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec_ref(v_args_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_upperBound_1134_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main(lean_object* v_a_1151_, lean_object* v_b_1152_, uint8_t v_mode_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1153_, v_a_1151_, v_b_1152_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main___boxed(lean_object* v_a_1160_, lean_object* v_b_1161_, lean_object* v_mode_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
uint8_t v_mode_boxed_1168_; lean_object* v_res_1169_; 
v_mode_boxed_1168_ = lean_unbox(v_mode_1162_);
v_res_1169_ = l_Lean_Meta_ACLt_main(v_a_1160_, v_b_1161_, v_mode_boxed_1168_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt(lean_object* v_a_1170_, lean_object* v_b_1171_, uint8_t v_mode_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1172_, v_a_1170_, v_b_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt___boxed(lean_object* v_a_1179_, lean_object* v_b_1180_, lean_object* v_mode_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
uint8_t v_mode_boxed_1187_; lean_object* v_res_1188_; 
v_mode_boxed_1187_ = lean_unbox(v_mode_1181_);
v_res_1188_ = l_Lean_Meta_acLt(v_a_1179_, v_b_1180_, v_mode_boxed_1187_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
return v_res_1188_;
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
