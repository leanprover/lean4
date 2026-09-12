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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_ctorWeight(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorWeight___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx___boxed(lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(lean_object*);
static const lean_string_object l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Meta.acLt"};
static const lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0 = (const lean_object*)&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(lean_object* v_k_24_){
_start:
{
lean_inc(v_k_24_);
return v_k_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg___boxed(lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(v_k_25_);
lean_dec(v_k_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim(lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, uint8_t v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_inc(v_k_31_);
return v_k_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___boxed(lean_object* v_motive_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
uint8_t v_t_boxed_37_; lean_object* v_res_38_; 
v_t_boxed_37_ = lean_unbox(v_t_34_);
v_res_38_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim(v_motive_32_, v_ctorIdx_33_, v_t_boxed_37_, v_h_35_, v_k_36_);
lean_dec(v_k_36_);
lean_dec(v_ctorIdx_33_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(lean_object* v_reduce_39_){
_start:
{
lean_inc(v_reduce_39_);
return v_reduce_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg___boxed(lean_object* v_reduce_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(v_reduce_40_);
lean_dec(v_reduce_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim(lean_object* v_motive_42_, uint8_t v_t_43_, lean_object* v_h_44_, lean_object* v_reduce_45_){
_start:
{
lean_inc(v_reduce_45_);
return v_reduce_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_reduce_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_reduce_49_);
lean_dec(v_reduce_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(lean_object* v_reduceSimpleOnly_52_){
_start:
{
lean_inc(v_reduceSimpleOnly_52_);
return v_reduceSimpleOnly_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg___boxed(lean_object* v_reduceSimpleOnly_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(v_reduceSimpleOnly_53_);
lean_dec(v_reduceSimpleOnly_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_reduceSimpleOnly_58_){
_start:
{
lean_inc(v_reduceSimpleOnly_58_);
return v_reduceSimpleOnly_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___boxed(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_reduceSimpleOnly_62_){
_start:
{
uint8_t v_t_boxed_63_; lean_object* v_res_64_; 
v_t_boxed_63_ = lean_unbox(v_t_60_);
v_res_64_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(v_motive_59_, v_t_boxed_63_, v_h_61_, v_reduceSimpleOnly_62_);
lean_dec(v_reduceSimpleOnly_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(lean_object* v_none_65_){
_start:
{
lean_inc(v_none_65_);
return v_none_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg___boxed(lean_object* v_none_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(v_none_66_);
lean_dec(v_none_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim(lean_object* v_motive_68_, uint8_t v_t_69_, lean_object* v_h_70_, lean_object* v_none_71_){
_start:
{
lean_inc(v_none_71_);
return v_none_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_none_75_){
_start:
{
uint8_t v_t_boxed_76_; lean_object* v_res_77_; 
v_t_boxed_76_ = lean_unbox(v_t_73_);
v_res_77_ = l_Lean_Meta_ACLt_ReduceMode_none_elim(v_motive_72_, v_t_boxed_76_, v_h_74_, v_none_75_);
lean_dec(v_none_75_);
return v_res_77_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0));
v___x_85_ = l_Lean_Meta_Config_toConfigWithKey(v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(uint8_t v_mode_87_, lean_object* v_e_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = l_Lean_Expr_hasLooseBVars(v_e_88_);
if (v___x_94_ == 0)
{
switch(v_mode_87_)
{
case 0:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_DiscrTree_reduce(v_e_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
return v___x_95_;
}
case 1:
{
lean_object* v___x_96_; lean_object* v_config_97_; uint8_t v_trackZetaDelta_98_; lean_object* v_zetaDeltaSet_99_; lean_object* v_lctx_100_; lean_object* v_localInstances_101_; lean_object* v_defEqCtx_x3f_102_; lean_object* v_synthPendingDepth_103_; lean_object* v_customCanUnfoldPredicate_x3f_104_; uint8_t v_univApprox_105_; uint8_t v_inTypeClassResolution_106_; uint8_t v_cacheInferType_107_; uint64_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_96_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config;
v_config_97_ = lean_ctor_get(v___x_96_, 0);
v_trackZetaDelta_98_ = lean_ctor_get_uint8(v_a_89_, sizeof(void*)*7);
v_zetaDeltaSet_99_ = lean_ctor_get(v_a_89_, 1);
v_lctx_100_ = lean_ctor_get(v_a_89_, 2);
v_localInstances_101_ = lean_ctor_get(v_a_89_, 3);
v_defEqCtx_x3f_102_ = lean_ctor_get(v_a_89_, 4);
v_synthPendingDepth_103_ = lean_ctor_get(v_a_89_, 5);
v_customCanUnfoldPredicate_x3f_104_ = lean_ctor_get(v_a_89_, 6);
v_univApprox_105_ = lean_ctor_get_uint8(v_a_89_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_106_ = lean_ctor_get_uint8(v_a_89_, sizeof(void*)*7 + 2);
v_cacheInferType_107_ = lean_ctor_get_uint8(v_a_89_, sizeof(void*)*7 + 3);
v___x_108_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_97_);
lean_inc_ref(v_config_97_);
v___x_109_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_109_, 0, v_config_97_);
lean_ctor_set_uint64(v___x_109_, sizeof(void*)*1, v___x_108_);
lean_inc(v_customCanUnfoldPredicate_x3f_104_);
lean_inc(v_synthPendingDepth_103_);
lean_inc(v_defEqCtx_x3f_102_);
lean_inc_ref(v_localInstances_101_);
lean_inc_ref(v_lctx_100_);
lean_inc(v_zetaDeltaSet_99_);
v___x_110_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v_zetaDeltaSet_99_);
lean_ctor_set(v___x_110_, 2, v_lctx_100_);
lean_ctor_set(v___x_110_, 3, v_localInstances_101_);
lean_ctor_set(v___x_110_, 4, v_defEqCtx_x3f_102_);
lean_ctor_set(v___x_110_, 5, v_synthPendingDepth_103_);
lean_ctor_set(v___x_110_, 6, v_customCanUnfoldPredicate_x3f_104_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*7, v_trackZetaDelta_98_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*7 + 1, v_univApprox_105_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*7 + 2, v_inTypeClassResolution_106_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*7 + 3, v_cacheInferType_107_);
v___x_111_ = l_Lean_Meta_DiscrTree_reduce(v_e_88_, v___x_110_, v_a_90_, v_a_91_, v_a_92_);
lean_dec_ref_known(v___x_110_, 7);
return v___x_111_;
}
default: 
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v_e_88_);
return v___x_112_;
}
}
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v_e_88_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce___boxed(lean_object* v_mode_114_, lean_object* v_e_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
uint8_t v_mode_boxed_121_; lean_object* v_res_122_; 
v_mode_boxed_121_ = lean_unbox(v_mode_114_);
v_res_122_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_boxed_121_, v_e_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(lean_object* v_f_125_, lean_object* v_numArgs_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
uint8_t v___x_132_; 
v___x_132_ = l_Lean_Expr_hasLooseBVars(v_f_125_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_getFunInfoNArgs(v_f_125_, v_numArgs_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_142_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_142_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_paramInfo_138_; lean_object* v___x_140_; 
v_paramInfo_138_ = lean_ctor_get(v_a_134_, 0);
lean_inc_ref(v_paramInfo_138_);
lean_dec(v_a_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v_paramInfo_138_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_paramInfo_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_133_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_133_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_numArgs_126_);
lean_dec_ref(v_f_125_);
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0));
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___boxed(lean_object* v_f_153_, lean_object* v_numArgs_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_f_153_, v_numArgs_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___f_168_; lean_object* v___x_13542__overap_169_; lean_object* v___x_170_; 
v___f_168_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0));
v___x_13542__overap_169_ = lean_panic_fn_borrowed(v___f_168_, v_msg_162_);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
v___x_170_ = lean_apply_5(v___x_13542__overap_169_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, lean_box(0));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v_msg_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(lean_object* v_msg_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = l_Lean_instInhabitedLocalDecl_default;
v___x_180_ = lean_panic_fn_borrowed(v___x_179_, v_msg_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(uint8_t v_mode_182_, lean_object* v_a_u2081_183_, lean_object* v_a_u2082_184_, lean_object* v_b_u2081_185_, lean_object* v_b_u2082_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; 
lean_inc_ref(v_b_u2081_185_);
lean_inc_ref(v_a_u2081_183_);
v___x_192_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_182_, v_a_u2081_183_, v_b_u2081_185_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; uint8_t v___x_194_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
v___x_194_ = lean_unbox(v_a_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec_ref_known(v___x_192_, 1);
v___x_195_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_182_, v_b_u2081_185_, v_a_u2081_183_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_205_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_205_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
uint8_t v___x_200_; 
v___x_200_ = lean_unbox(v_a_196_);
lean_dec(v_a_196_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_del_object(v___x_198_);
lean_dec(v_a_193_);
v___x_201_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_182_, v_a_u2082_184_, v_b_u2082_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
return v___x_201_;
}
else
{
lean_object* v___x_203_; 
lean_dec_ref(v_b_u2082_186_);
lean_dec_ref(v_a_u2082_184_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v_a_193_);
v___x_203_ = v___x_198_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_193_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_dec(v_a_193_);
lean_dec_ref(v_b_u2082_186_);
lean_dec_ref(v_a_u2082_184_);
return v___x_195_;
}
}
else
{
lean_dec(v_a_193_);
lean_dec_ref(v_b_u2082_186_);
lean_dec_ref(v_b_u2081_185_);
lean_dec_ref(v_a_u2082_184_);
lean_dec_ref(v_a_u2081_183_);
return v___x_192_;
}
}
else
{
lean_dec_ref(v_b_u2082_186_);
lean_dec_ref(v_b_u2081_185_);
lean_dec_ref(v_a_u2082_184_);
lean_dec_ref(v_a_u2081_183_);
return v___x_192_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_209_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2));
v___x_210_ = lean_unsigned_to_nat(14u);
v___x_211_ = lean_unsigned_to_nat(22u);
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1));
v___x_213_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0));
v___x_214_ = l_mkPanicMessageWithDecl(v___x_213_, v___x_212_, v___x_211_, v___x_210_, v___x_209_);
return v___x_214_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0(void){
_start:
{
lean_object* v___x_215_; lean_object* v_dummy_216_; 
v___x_215_ = lean_box(0);
v_dummy_216_ = l_Lean_Expr_sort___override(v___x_215_);
return v_dummy_216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(lean_object* v_upperBound_220_, lean_object* v_a_221_, lean_object* v___x_222_, lean_object* v___x_223_, uint8_t v_mode_224_, lean_object* v_a_225_, lean_object* v_b_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_a_233_; uint8_t v___x_237_; 
v___x_237_ = lean_nat_dec_lt(v_a_225_, v_upperBound_220_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
lean_dec(v_a_225_);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_b_226_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v_isInstance_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref(v_b_226_);
v___x_239_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_240_ = lean_array_get_borrowed(v___x_239_, v_a_221_, v_a_225_);
v_isInstance_241_ = lean_ctor_get_uint8(v___x_240_, sizeof(void*)*1 + 4);
v___x_242_ = lean_box(0);
v___x_243_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_241_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = l_Lean_instInhabitedExpr;
v___x_245_ = lean_array_get_borrowed(v___x_244_, v___x_222_, v_a_225_);
v___x_246_ = lean_array_get_borrowed(v___x_244_, v___x_223_, v_a_225_);
lean_inc(v___x_246_);
lean_inc(v___x_245_);
v___x_247_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_224_, v___x_245_, v___x_246_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_279_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_279_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_279_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_279_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
uint8_t v___x_252_; 
v___x_252_ = lean_unbox(v_a_248_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_del_object(v___x_250_);
lean_inc(v___x_245_);
lean_inc(v___x_246_);
v___x_253_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_224_, v___x_246_, v___x_245_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_264_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_264_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_264_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_264_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
uint8_t v___x_258_; 
v___x_258_ = lean_unbox(v_a_254_);
lean_dec(v_a_254_);
if (v___x_258_ == 0)
{
lean_del_object(v___x_256_);
lean_dec(v_a_248_);
v_a_233_ = v___x_243_;
goto v___jp_232_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec(v_a_225_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_a_248_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_242_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_260_);
v___x_262_ = v___x_256_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_a_248_);
lean_dec(v_a_225_);
v_a_265_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_253_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_253_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
lean_dec(v_a_248_);
lean_dec(v_a_225_);
v___x_273_ = lean_box(v___x_237_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_242_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_275_);
v___x_277_ = v___x_250_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec(v_a_225_);
v_a_280_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_247_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_247_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
v_a_233_ = v___x_243_;
goto v___jp_232_;
}
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_nat_add(v_a_225_, v___x_234_);
lean_dec(v_a_225_);
lean_inc_ref(v_a_233_);
v_a_225_ = v___x_235_;
v_b_226_ = v_a_233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(lean_object* v_upperBound_288_, lean_object* v___x_289_, lean_object* v___x_290_, uint8_t v_mode_291_, lean_object* v_a_292_, lean_object* v_b_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = lean_nat_dec_lt(v_a_292_, v_upperBound_288_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec(v_a_292_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v_b_293_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec_ref(v_b_293_);
v___x_301_ = l_Lean_instInhabitedExpr;
v___x_302_ = lean_box(0);
v___x_303_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_304_ = lean_array_get_borrowed(v___x_301_, v___x_289_, v_a_292_);
v___x_305_ = lean_array_get_borrowed(v___x_301_, v___x_290_, v_a_292_);
lean_inc(v___x_305_);
lean_inc(v___x_304_);
v___x_306_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_291_, v___x_304_, v___x_305_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_341_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_341_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_341_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_341_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
uint8_t v___x_311_; 
v___x_311_ = lean_unbox(v_a_307_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_del_object(v___x_309_);
lean_inc(v___x_304_);
lean_inc(v___x_305_);
v___x_312_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_291_, v___x_305_, v___x_304_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_326_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_326_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_326_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_326_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
uint8_t v___x_317_; 
v___x_317_ = lean_unbox(v_a_313_);
lean_dec(v_a_313_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_del_object(v___x_315_);
lean_dec(v_a_307_);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_a_292_, v___x_318_);
lean_dec(v_a_292_);
v_a_292_ = v___x_319_;
v_b_293_ = v___x_303_;
goto _start;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_dec(v_a_292_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v_a_307_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_302_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_322_);
v___x_324_ = v___x_315_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec(v_a_307_);
lean_dec(v_a_292_);
v_a_327_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_312_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_312_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
lean_dec(v_a_307_);
lean_dec(v_a_292_);
v___x_335_ = lean_box(v___x_299_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_302_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_337_);
v___x_339_ = v___x_309_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_292_);
v_a_342_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_306_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_306_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(uint8_t v_mode_350_, lean_object* v_a_351_, lean_object* v_b_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_aFn_358_; lean_object* v_bFn_359_; lean_object* v___x_360_; 
v_aFn_358_ = l_Lean_Expr_getAppFn(v_a_351_);
v_bFn_359_ = l_Lean_Expr_getAppFn(v_b_352_);
lean_inc_ref(v_bFn_359_);
lean_inc_ref(v_aFn_358_);
v___x_360_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_350_, v_aFn_358_, v_bFn_359_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_458_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_458_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_458_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_458_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
uint8_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 1;
v___x_366_ = lean_unbox(v_a_361_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_del_object(v___x_363_);
lean_inc_ref(v_aFn_358_);
v___x_367_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_350_, v_bFn_359_, v_aFn_358_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_453_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_453_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_453_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_453_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
uint8_t v___x_372_; 
v___x_372_ = lean_unbox(v_a_368_);
lean_dec(v_a_368_);
if (v___x_372_ == 0)
{
lean_object* v_dummy_373_; lean_object* v_nargs_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_nargs_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
lean_dec(v_a_361_);
v_dummy_373_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_374_ = l_Lean_Expr_getAppNumArgs(v_a_351_);
lean_inc(v_nargs_374_);
v___x_375_ = lean_mk_array(v_nargs_374_, v_dummy_373_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_sub(v_nargs_374_, v___x_376_);
lean_dec(v_nargs_374_);
v___x_378_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_351_, v___x_375_, v___x_377_);
v_nargs_379_ = l_Lean_Expr_getAppNumArgs(v_b_352_);
lean_inc(v_nargs_379_);
v___x_380_ = lean_mk_array(v_nargs_379_, v_dummy_373_);
v___x_381_ = lean_nat_sub(v_nargs_379_, v___x_376_);
lean_dec(v_nargs_379_);
v___x_382_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_b_352_, v___x_380_, v___x_381_);
v___x_383_ = lean_array_get_size(v___x_378_);
v___x_384_ = lean_array_get_size(v___x_382_);
v___x_385_ = lean_nat_dec_lt(v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; 
v___x_386_ = lean_nat_dec_lt(v___x_384_, v___x_383_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_del_object(v___x_370_);
v___x_387_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_358_, v___x_383_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v___x_389_ = lean_array_get_size(v_a_388_);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_389_, v_a_388_, v___x_378_, v___x_382_, v_mode_350_, v___x_390_, v___x_391_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_388_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_425_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_425_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_425_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_425_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_fst_397_; 
v_fst_397_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_fst_397_);
lean_dec(v_a_393_);
if (lean_obj_tag(v_fst_397_) == 0)
{
lean_object* v___x_398_; 
lean_del_object(v___x_395_);
v___x_398_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_383_, v___x_378_, v___x_382_, v_mode_350_, v___x_389_, v___x_391_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_412_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_412_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_412_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_412_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_fst_403_; 
v_fst_403_ = lean_ctor_get(v_a_399_, 0);
lean_inc(v_fst_403_);
lean_dec(v_a_399_);
if (lean_obj_tag(v_fst_403_) == 0)
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_box(v___x_386_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_404_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
else
{
lean_object* v_val_408_; lean_object* v___x_410_; 
v_val_408_ = lean_ctor_get(v_fst_403_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v_fst_403_, 1);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_val_408_);
v___x_410_ = v___x_401_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_val_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
v_a_413_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_398_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_398_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_val_421_; lean_object* v___x_423_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
v_val_421_ = lean_ctor_get(v_fst_397_, 0);
lean_inc(v_val_421_);
lean_dec_ref_known(v_fst_397_, 1);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v_val_421_);
v___x_423_ = v___x_395_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_val_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
v_a_426_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_392_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_392_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
v_a_434_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_387_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_387_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_444_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
lean_dec_ref(v_aFn_358_);
v___x_442_ = lean_box(v___x_385_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_442_);
v___x_444_ = v___x_370_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_448_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
lean_dec_ref(v_aFn_358_);
v___x_446_ = lean_box(v___x_365_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_446_);
v___x_448_ = v___x_370_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v___x_451_; 
lean_dec_ref(v_aFn_358_);
lean_dec_ref(v_b_352_);
lean_dec_ref(v_a_351_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_a_361_);
v___x_451_ = v___x_370_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_361_);
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
lean_dec(v_a_361_);
lean_dec_ref(v_aFn_358_);
lean_dec_ref(v_b_352_);
lean_dec_ref(v_a_351_);
return v___x_367_;
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_dec(v_a_361_);
lean_dec_ref(v_bFn_359_);
lean_dec_ref(v_aFn_358_);
lean_dec_ref(v_b_352_);
lean_dec_ref(v_a_351_);
v___x_454_ = lean_box(v___x_365_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_454_);
v___x_456_ = v___x_363_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_dec_ref(v_bFn_359_);
lean_dec_ref(v_aFn_358_);
lean_dec_ref(v_b_352_);
lean_dec_ref(v_a_351_);
return v___x_360_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6));
v___x_463_ = lean_unsigned_to_nat(27u);
v___x_464_ = lean_unsigned_to_nat(152u);
v___x_465_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5));
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4));
v___x_467_ = l_mkPanicMessageWithDecl(v___x_466_, v___x_465_, v___x_464_, v___x_463_, v___x_462_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(uint8_t v_mode_468_, lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_d_477_; lean_object* v_e_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; 
switch(lean_obj_tag(v_a_469_))
{
case 0:
{
lean_object* v_deBruijnIndex_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_deBruijnIndex_486_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_deBruijnIndex_486_);
lean_dec_ref_known(v_a_469_, 1);
v___x_487_ = l_Lean_Expr_bvarIdx_x21(v_b_470_);
lean_dec_ref(v_b_470_);
v___x_488_ = lean_nat_dec_lt(v_deBruijnIndex_486_, v___x_487_);
lean_dec(v___x_487_);
lean_dec(v_deBruijnIndex_486_);
v___x_489_ = lean_box(v___x_488_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
case 1:
{
lean_object* v_fvarId_491_; lean_object* v___x_492_; 
v_fvarId_491_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_fvarId_491_);
lean_dec_ref_known(v_a_469_, 1);
v___x_492_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_491_, v_a_471_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_492_, 1);
v___x_494_ = l_Lean_Expr_fvarId_x21(v_b_470_);
lean_dec_ref(v_b_470_);
v___x_495_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_494_, v_a_471_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_518_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_518_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_518_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_518_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_510_; 
if (lean_obj_tag(v_a_493_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_516_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_515_);
v___y_510_ = v___x_516_;
goto v___jp_509_;
}
else
{
lean_object* v_val_517_; 
v_val_517_ = lean_ctor_get(v_a_493_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v_a_493_, 1);
v___y_510_ = v_val_517_;
goto v___jp_509_;
}
v___jp_500_:
{
lean_object* v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_503_ = l_Lean_LocalDecl_index(v___y_502_);
lean_dec_ref(v___y_502_);
v___x_504_ = lean_nat_dec_lt(v___y_501_, v___x_503_);
lean_dec(v___x_503_);
lean_dec(v___y_501_);
v___x_505_ = lean_box(v___x_504_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_505_);
v___x_507_ = v___x_498_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
v___jp_509_:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_LocalDecl_index(v___y_510_);
lean_dec_ref(v___y_510_);
if (lean_obj_tag(v_a_496_) == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_513_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_512_);
v___y_501_ = v___x_511_;
v___y_502_ = v___x_513_;
goto v___jp_500_;
}
else
{
lean_object* v_val_514_; 
v_val_514_ = lean_ctor_get(v_a_496_, 0);
lean_inc(v_val_514_);
lean_dec_ref_known(v_a_496_, 1);
v___y_501_ = v___x_511_;
v___y_502_ = v_val_514_;
goto v___jp_500_;
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_a_493_);
v_a_519_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_495_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_495_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v_b_470_);
v_a_527_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_492_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_492_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_mvarId_535_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_mvarId_535_);
lean_dec_ref_known(v_a_469_, 1);
v___x_536_ = l_Lean_Expr_mvarId_x21(v_b_470_);
lean_dec_ref(v_b_470_);
v___x_537_ = l_Lean_Name_lt(v_mvarId_535_, v___x_536_);
lean_dec(v___x_536_);
lean_dec(v_mvarId_535_);
v___x_538_ = lean_box(v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
case 3:
{
lean_object* v_u_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_u_540_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_u_540_);
lean_dec_ref_known(v_a_469_, 1);
v___x_541_ = l_Lean_Expr_sortLevel_x21(v_b_470_);
lean_dec_ref(v_b_470_);
v___x_542_ = l_Lean_Level_normLt(v_u_540_, v___x_541_);
lean_dec(v___x_541_);
lean_dec(v_u_540_);
v___x_543_ = lean_box(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
case 4:
{
lean_object* v_declName_545_; lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_declName_545_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_declName_545_);
lean_dec_ref_known(v_a_469_, 2);
v___x_546_ = l_Lean_Expr_constName_x21(v_b_470_);
lean_dec_ref(v_b_470_);
v___x_547_ = l_Lean_Name_lt(v_declName_545_, v___x_546_);
lean_dec(v___x_546_);
lean_dec(v_declName_545_);
v___x_548_ = lean_box(v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
case 5:
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_468_, v_a_469_, v_b_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
return v___x_550_;
}
case 8:
{
lean_object* v_value_551_; lean_object* v_body_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_value_551_ = lean_ctor_get(v_a_469_, 2);
lean_inc_ref(v_value_551_);
v_body_552_ = lean_ctor_get(v_a_469_, 3);
lean_inc_ref(v_body_552_);
lean_dec_ref_known(v_a_469_, 4);
v___x_553_ = l_Lean_Expr_letValue_x21(v_b_470_);
v___x_554_ = l_Lean_Expr_letBody_x21(v_b_470_);
lean_dec_ref(v_b_470_);
v___x_555_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_468_, v_value_551_, v_body_552_, v___x_553_, v___x_554_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
return v___x_555_;
}
case 9:
{
lean_object* v_a_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_a_556_ = lean_ctor_get(v_a_469_, 0);
lean_inc_ref(v_a_556_);
lean_dec_ref_known(v_a_469_, 1);
v___x_557_ = l_Lean_Expr_litValue_x21(v_b_470_);
lean_dec_ref(v_b_470_);
v___x_558_ = l_Lean_Literal_lt(v_a_556_, v___x_557_);
lean_dec_ref(v___x_557_);
lean_dec_ref(v_a_556_);
v___x_559_ = lean_box(v___x_558_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
case 10:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref_known(v_a_469_, 2);
lean_dec_ref(v_b_470_);
v___x_561_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
v___x_562_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_561_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
return v___x_562_;
}
case 11:
{
lean_object* v_idx_563_; lean_object* v_struct_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_idx_563_ = lean_ctor_get(v_a_469_, 1);
lean_inc(v_idx_563_);
v_struct_564_ = lean_ctor_get(v_a_469_, 2);
lean_inc_ref(v_struct_564_);
lean_dec_ref_known(v_a_469_, 3);
v___x_565_ = l_Lean_Expr_projIdx_x21(v_b_470_);
v___x_566_ = lean_nat_dec_eq(v_idx_563_, v___x_565_);
if (v___x_566_ == 0)
{
uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec_ref(v_struct_564_);
lean_dec_ref(v_b_470_);
v___x_567_ = lean_nat_dec_lt(v_idx_563_, v___x_565_);
lean_dec(v___x_565_);
lean_dec(v_idx_563_);
v___x_568_ = lean_box(v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v___x_565_);
lean_dec(v_idx_563_);
v___x_570_ = l_Lean_Expr_projExpr_x21(v_b_470_);
lean_dec_ref(v_b_470_);
v___x_571_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_468_, v_struct_564_, v___x_570_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
return v___x_571_;
}
}
default: 
{
lean_object* v_binderType_572_; lean_object* v_body_573_; 
v_binderType_572_ = lean_ctor_get(v_a_469_, 1);
lean_inc_ref(v_binderType_572_);
v_body_573_ = lean_ctor_get(v_a_469_, 2);
lean_inc_ref(v_body_573_);
lean_dec_ref(v_a_469_);
v_d_477_ = v_binderType_572_;
v_e_478_ = v_body_573_;
v___y_479_ = v_a_471_;
v___y_480_ = v_a_472_;
v___y_481_ = v_a_473_;
v___y_482_ = v_a_474_;
goto v___jp_476_;
}
}
v___jp_476_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_Expr_bindingDomain_x21(v_b_470_);
v___x_484_ = l_Lean_Expr_bindingBody_x21(v_b_470_);
lean_dec_ref(v_b_470_);
v___x_485_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_468_, v_d_477_, v_e_478_, v___x_483_, v___x_484_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(uint8_t v_mode_574_, lean_object* v_a_575_, lean_object* v_b_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0));
v___x_583_ = l_Lean_Core_checkSystem(v___x_582_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_584_; 
lean_dec_ref_known(v___x_583_, 1);
lean_inc_ref(v_a_575_);
lean_inc_ref(v_b_576_);
v___x_584_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_574_, v_b_576_, v_a_575_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; uint8_t v___x_586_; uint8_t v___x_587_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
v___x_586_ = 1;
v___x_587_ = lean_unbox(v_a_585_);
lean_dec(v_a_585_);
if (v___x_587_ == 0)
{
uint8_t v___x_588_; uint8_t v___x_589_; uint8_t v___x_590_; 
v___x_588_ = l_Lean_Expr_ctorWeight(v_b_576_);
v___x_589_ = l_Lean_Expr_ctorWeight(v_a_575_);
v___x_590_ = lean_uint8_dec_lt(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; lean_object* v___x_592_; 
lean_dec_ref_known(v___x_584_, 1);
v___x_591_ = lean_uint8_dec_lt(v___x_589_, v___x_588_);
lean_inc_ref(v_b_576_);
lean_inc_ref(v_a_575_);
v___x_592_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_574_, v_a_575_, v_b_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
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
lean_object* v___x_598_; lean_object* v___x_600_; 
lean_dec_ref(v_b_576_);
lean_dec_ref(v_a_575_);
v___x_598_ = lean_box(v___x_590_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_598_);
v___x_600_ = v___x_595_;
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
else
{
if (v___x_591_ == 0)
{
lean_object* v___x_602_; 
lean_del_object(v___x_595_);
v___x_602_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_574_, v_a_575_, v_b_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_605_; 
lean_dec_ref(v_b_576_);
lean_dec_ref(v_a_575_);
v___x_603_ = lean_box(v___x_586_);
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
lean_dec_ref(v_b_576_);
lean_dec_ref(v_a_575_);
return v___x_592_;
}
}
else
{
lean_dec_ref(v_b_576_);
lean_dec_ref(v_a_575_);
return v___x_584_;
}
}
else
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_b_576_);
lean_dec_ref(v_a_575_);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_616_);
v___x_609_ = v___x_584_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_dec(v___x_584_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_box(v___x_586_);
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
lean_dec_ref(v_b_576_);
lean_dec_ref(v_a_575_);
return v___x_584_;
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref(v_b_576_);
lean_dec_ref(v_a_575_);
v_a_617_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_583_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_583_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(uint8_t v_mode_625_, lean_object* v_a_626_, lean_object* v_b_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = lean_expr_eqv(v_a_626_, v_b_627_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
v___x_634_ = l_Lean_Expr_isMData(v_a_626_);
if (v___x_634_ == 0)
{
uint8_t v___x_635_; 
v___x_635_ = l_Lean_Expr_isMData(v_b_627_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_625_, v_a_626_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_625_, v_b_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_625_, v_a_637_, v_a_639_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
return v___x_640_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_a_637_);
v_a_641_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_638_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_638_);
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
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v_b_627_);
v_a_649_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_636_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_636_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Expr_mdataExpr_x21(v_b_627_);
lean_dec_ref(v_b_627_);
v_b_627_ = v___x_657_;
goto _start;
}
}
else
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Expr_mdataExpr_x21(v_a_626_);
lean_dec_ref(v_a_626_);
v_a_626_ = v___x_659_;
goto _start;
}
}
else
{
uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec_ref(v_b_627_);
lean_dec_ref(v_a_626_);
v___x_661_ = 0;
v___x_662_ = lean_box(v___x_661_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(lean_object* v_upperBound_664_, lean_object* v_a_665_, lean_object* v_args_666_, uint8_t v_mode_667_, lean_object* v_b_668_, lean_object* v_a_669_, lean_object* v_b_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_a_677_; uint8_t v___x_681_; 
v___x_681_ = lean_nat_dec_lt(v_a_669_, v_upperBound_664_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec(v_a_669_);
lean_dec_ref(v_b_668_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_b_670_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v_isInstance_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec_ref(v_b_670_);
v___x_683_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_684_ = lean_array_get_borrowed(v___x_683_, v_a_665_, v_a_669_);
v_isInstance_685_ = lean_ctor_get_uint8(v___x_684_, sizeof(void*)*1 + 4);
v___x_686_ = lean_box(0);
v___x_687_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_685_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = l_Lean_instInhabitedExpr;
v___x_689_ = lean_array_get_borrowed(v___x_688_, v_args_666_, v_a_669_);
lean_inc_ref(v_b_668_);
lean_inc(v___x_689_);
v___x_690_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_667_, v___x_689_, v_b_668_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_701_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_701_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
uint8_t v___x_695_; 
v___x_695_ = lean_unbox(v_a_691_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
lean_dec(v_a_669_);
lean_dec_ref(v_b_668_);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_a_691_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_686_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_697_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
lean_del_object(v___x_693_);
lean_dec(v_a_691_);
v_a_677_ = v___x_687_;
goto v___jp_676_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec(v_a_669_);
lean_dec_ref(v_b_668_);
v_a_702_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_690_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_690_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
v_a_677_ = v___x_687_;
goto v___jp_676_;
}
}
v___jp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_add(v_a_669_, v___x_678_);
lean_dec(v_a_669_);
lean_inc_ref(v_a_677_);
v_a_669_ = v___x_679_;
v_b_670_ = v_a_677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(lean_object* v_upperBound_710_, lean_object* v_args_711_, uint8_t v_mode_712_, lean_object* v_b_713_, lean_object* v_a_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_nat_dec_lt(v_a_714_, v_upperBound_710_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v_a_714_);
lean_dec_ref(v_b_713_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_b_715_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref(v_b_715_);
v___x_723_ = lean_box(0);
v___x_724_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_725_ = lean_array_fget_borrowed(v_args_711_, v_a_714_);
lean_inc_ref(v_b_713_);
lean_inc(v___x_725_);
v___x_726_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_712_, v___x_725_, v_b_713_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_740_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_740_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_740_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_740_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v___x_731_; 
v___x_731_ = lean_unbox(v_a_727_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
lean_dec(v_a_714_);
lean_dec_ref(v_b_713_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v_a_727_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_723_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_733_);
v___x_735_ = v___x_729_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_del_object(v___x_729_);
lean_dec(v_a_727_);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_a_714_, v___x_737_);
lean_dec(v_a_714_);
v_a_714_ = v___x_738_;
v_b_715_ = v___x_724_;
goto _start;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_714_);
lean_dec_ref(v_b_713_);
v_a_741_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_726_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_726_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(uint8_t v_mode_749_, lean_object* v_b_750_, lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
if (lean_obj_tag(v_x_751_) == 5)
{
lean_object* v_fn_759_; lean_object* v_arg_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_fn_759_ = lean_ctor_get(v_x_751_, 0);
lean_inc_ref(v_fn_759_);
v_arg_760_ = lean_ctor_get(v_x_751_, 1);
lean_inc_ref(v_arg_760_);
lean_dec_ref_known(v_x_751_, 2);
v___x_761_ = lean_array_set(v_x_752_, v_x_753_, v_arg_760_);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_sub(v_x_753_, v___x_762_);
lean_dec(v_x_753_);
v_x_751_ = v_fn_759_;
v_x_752_ = v___x_761_;
v_x_753_ = v___x_763_;
goto _start;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v_x_753_);
v___x_765_ = lean_array_get_size(v_x_752_);
v___x_766_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_x_751_, v___x_765_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = lean_array_get_size(v_a_767_);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
lean_inc_ref(v_b_750_);
v___x_771_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_768_, v_a_767_, v_x_752_, v_mode_749_, v_b_750_, v___x_769_, v___x_770_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v_a_767_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_805_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_805_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_805_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_805_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_fst_776_; 
v_fst_776_ = lean_ctor_get(v_a_772_, 0);
lean_inc(v_fst_776_);
lean_dec(v_a_772_);
if (lean_obj_tag(v_fst_776_) == 0)
{
lean_object* v___x_777_; 
lean_del_object(v___x_774_);
v___x_777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_765_, v_x_752_, v_mode_749_, v_b_750_, v___x_768_, v___x_770_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref(v_x_752_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_792_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_792_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_792_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_792_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_fst_782_; 
v_fst_782_ = lean_ctor_get(v_a_778_, 0);
lean_inc(v_fst_782_);
lean_dec(v_a_778_);
if (lean_obj_tag(v_fst_782_) == 0)
{
uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_783_ = 1;
v___x_784_ = lean_box(v___x_783_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_784_);
v___x_786_ = v___x_780_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
else
{
lean_object* v_val_788_; lean_object* v___x_790_; 
v_val_788_ = lean_ctor_get(v_fst_782_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_fst_782_, 1);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v_val_788_);
v___x_790_ = v___x_780_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_788_);
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
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_a_793_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_777_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_777_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_object* v_val_801_; lean_object* v___x_803_; 
lean_dec_ref(v_x_752_);
lean_dec_ref(v_b_750_);
v_val_801_ = lean_ctor_get(v_fst_776_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_fst_776_, 1);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_val_801_);
v___x_803_ = v___x_774_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_val_801_);
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
lean_dec_ref(v_x_752_);
lean_dec_ref(v_b_750_);
v_a_806_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_771_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_771_);
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
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v_x_752_);
lean_dec_ref(v_b_750_);
v_a_814_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_766_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_766_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(uint8_t v_mode_822_, lean_object* v_a_823_, lean_object* v_b_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_d_831_; lean_object* v_e_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; 
switch(lean_obj_tag(v_a_823_))
{
case 11:
{
lean_object* v_struct_841_; lean_object* v___x_842_; 
v_struct_841_ = lean_ctor_get(v_a_823_, 2);
lean_inc_ref(v_struct_841_);
lean_dec_ref_known(v_a_823_, 3);
v___x_842_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_822_, v_struct_841_, v_b_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_842_;
}
case 5:
{
lean_object* v_dummy_843_; lean_object* v_nargs_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_dummy_843_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_844_ = l_Lean_Expr_getAppNumArgs(v_a_823_);
lean_inc(v_nargs_844_);
v___x_845_ = lean_mk_array(v_nargs_844_, v_dummy_843_);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_sub(v_nargs_844_, v___x_846_);
lean_dec(v_nargs_844_);
v___x_848_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_822_, v_b_824_, v_a_823_, v___x_845_, v___x_847_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_848_;
}
case 6:
{
lean_object* v_binderType_849_; lean_object* v_body_850_; 
v_binderType_849_ = lean_ctor_get(v_a_823_, 1);
lean_inc_ref(v_binderType_849_);
v_body_850_ = lean_ctor_get(v_a_823_, 2);
lean_inc_ref(v_body_850_);
lean_dec_ref_known(v_a_823_, 3);
v_d_831_ = v_binderType_849_;
v_e_832_ = v_body_850_;
v___y_833_ = v_a_825_;
v___y_834_ = v_a_826_;
v___y_835_ = v_a_827_;
v___y_836_ = v_a_828_;
goto v___jp_830_;
}
case 7:
{
lean_object* v_binderType_851_; lean_object* v_body_852_; 
v_binderType_851_ = lean_ctor_get(v_a_823_, 1);
lean_inc_ref(v_binderType_851_);
v_body_852_ = lean_ctor_get(v_a_823_, 2);
lean_inc_ref(v_body_852_);
lean_dec_ref_known(v_a_823_, 3);
v_d_831_ = v_binderType_851_;
v_e_832_ = v_body_852_;
v___y_833_ = v_a_825_;
v___y_834_ = v_a_826_;
v___y_835_ = v_a_827_;
v___y_836_ = v_a_828_;
goto v___jp_830_;
}
case 8:
{
lean_object* v_value_853_; lean_object* v_body_854_; lean_object* v___x_855_; 
v_value_853_ = lean_ctor_get(v_a_823_, 2);
lean_inc_ref(v_value_853_);
v_body_854_ = lean_ctor_get(v_a_823_, 3);
lean_inc_ref(v_body_854_);
lean_dec_ref_known(v_a_823_, 4);
lean_inc_ref(v_b_824_);
v___x_855_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_822_, v_value_853_, v_b_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; uint8_t v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
v___x_857_ = lean_unbox(v_a_856_);
lean_dec(v_a_856_);
if (v___x_857_ == 0)
{
lean_dec_ref(v_body_854_);
lean_dec_ref(v_b_824_);
return v___x_855_;
}
else
{
lean_object* v___x_858_; 
lean_dec_ref_known(v___x_855_, 1);
v___x_858_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_822_, v_body_854_, v_b_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_858_;
}
}
else
{
lean_dec_ref(v_body_854_);
lean_dec_ref(v_b_824_);
return v___x_855_;
}
}
default: 
{
uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref(v_b_824_);
lean_dec_ref(v_a_823_);
v___x_859_ = 1;
v___x_860_ = lean_box(v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
v___jp_830_:
{
lean_object* v___x_837_; 
lean_inc_ref(v_b_824_);
v___x_837_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_822_, v_d_831_, v_b_824_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; uint8_t v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
v___x_839_ = lean_unbox(v_a_838_);
lean_dec(v_a_838_);
if (v___x_839_ == 0)
{
lean_dec_ref(v_e_832_);
lean_dec_ref(v_b_824_);
return v___x_837_;
}
else
{
lean_object* v___x_840_; 
lean_dec_ref_known(v___x_837_, 1);
v___x_840_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_822_, v_e_832_, v_b_824_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
return v___x_840_;
}
}
else
{
lean_dec_ref(v_e_832_);
lean_dec_ref(v_b_824_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(uint8_t v_mode_862_, lean_object* v_a_863_, lean_object* v_b_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_862_, v_a_863_, v_b_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_886_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_886_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_886_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_886_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
uint8_t v___x_875_; 
v___x_875_ = lean_unbox(v_a_871_);
lean_dec(v_a_871_);
if (v___x_875_ == 0)
{
uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_876_ = 1;
v___x_877_ = lean_box(v___x_876_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_879_ = v___x_873_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_881_ = 0;
v___x_882_ = lean_box(v___x_881_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_882_);
v___x_884_ = v___x_873_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(lean_object* v_mode_887_, lean_object* v_a_888_, lean_object* v_b_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
uint8_t v_mode_boxed_895_; lean_object* v_res_896_; 
v_mode_boxed_895_ = lean_unbox(v_mode_887_);
v_res_896_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_boxed_895_, v_a_888_, v_b_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(lean_object* v_mode_897_, lean_object* v_a_u2081_898_, lean_object* v_a_u2082_899_, lean_object* v_b_u2081_900_, lean_object* v_b_u2082_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
uint8_t v_mode_boxed_907_; lean_object* v_res_908_; 
v_mode_boxed_907_ = lean_unbox(v_mode_897_);
v_res_908_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_boxed_907_, v_a_u2081_898_, v_a_u2082_899_, v_b_u2081_900_, v_b_u2082_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(lean_object* v_upperBound_909_, lean_object* v_args_910_, lean_object* v_mode_911_, lean_object* v_b_912_, lean_object* v_a_913_, lean_object* v_b_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v_mode_boxed_920_; lean_object* v_res_921_; 
v_mode_boxed_920_ = lean_unbox(v_mode_911_);
v_res_921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_909_, v_args_910_, v_mode_boxed_920_, v_b_912_, v_a_913_, v_b_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec_ref(v_args_910_);
lean_dec(v_upperBound_909_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object* v_mode_922_, lean_object* v_a_923_, lean_object* v_b_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
uint8_t v_mode_boxed_930_; lean_object* v_res_931_; 
v_mode_boxed_930_ = lean_unbox(v_mode_922_);
v_res_931_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_boxed_930_, v_a_923_, v_b_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object* v_upperBound_932_, lean_object* v_a_933_, lean_object* v_args_934_, lean_object* v_mode_935_, lean_object* v_b_936_, lean_object* v_a_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v_mode_boxed_944_; lean_object* v_res_945_; 
v_mode_boxed_944_ = lean_unbox(v_mode_935_);
v_res_945_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_932_, v_a_933_, v_args_934_, v_mode_boxed_944_, v_b_936_, v_a_937_, v_b_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec_ref(v_args_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_upperBound_932_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object* v_mode_946_, lean_object* v_a_947_, lean_object* v_b_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
uint8_t v_mode_boxed_954_; lean_object* v_res_955_; 
v_mode_boxed_954_ = lean_unbox(v_mode_946_);
v_res_955_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_boxed_954_, v_a_947_, v_b_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object* v_mode_956_, lean_object* v_a_957_, lean_object* v_b_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
uint8_t v_mode_boxed_964_; lean_object* v_res_965_; 
v_mode_boxed_964_ = lean_unbox(v_mode_956_);
v_res_965_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_boxed_964_, v_a_957_, v_b_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(lean_object* v_upperBound_966_, lean_object* v___x_967_, lean_object* v___x_968_, lean_object* v_mode_969_, lean_object* v_a_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
uint8_t v_mode_boxed_977_; lean_object* v_res_978_; 
v_mode_boxed_977_ = lean_unbox(v_mode_969_);
v_res_978_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_966_, v___x_967_, v___x_968_, v_mode_boxed_977_, v_a_970_, v_b_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec_ref(v___x_968_);
lean_dec_ref(v___x_967_);
lean_dec(v_upperBound_966_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(lean_object* v_mode_979_, lean_object* v_b_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
uint8_t v_mode_boxed_989_; lean_object* v_res_990_; 
v_mode_boxed_989_ = lean_unbox(v_mode_979_);
v_res_990_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_989_, v_b_980_, v_x_981_, v_x_982_, v_x_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(lean_object* v_upperBound_991_, lean_object* v_a_992_, lean_object* v___x_993_, lean_object* v___x_994_, lean_object* v_mode_995_, lean_object* v_a_996_, lean_object* v_b_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
uint8_t v_mode_boxed_1003_; lean_object* v_res_1004_; 
v_mode_boxed_1003_ = lean_unbox(v_mode_995_);
v_res_1004_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_991_, v_a_992_, v___x_993_, v___x_994_, v_mode_boxed_1003_, v_a_996_, v_b_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec_ref(v___x_994_);
lean_dec_ref(v___x_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_upperBound_991_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(lean_object* v_mode_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
uint8_t v_mode_boxed_1013_; lean_object* v_res_1014_; 
v_mode_boxed_1013_ = lean_unbox(v_mode_1005_);
v_res_1014_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_boxed_1013_, v_a_1006_, v_b_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(lean_object* v_mode_1015_, lean_object* v_a_1016_, lean_object* v_b_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
uint8_t v_mode_boxed_1023_; lean_object* v_res_1024_; 
v_mode_boxed_1023_ = lean_unbox(v_mode_1015_);
v_res_1024_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_boxed_1023_, v_a_1016_, v_b_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(lean_object* v_upperBound_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, uint8_t v_mode_1028_, lean_object* v_inst_1029_, lean_object* v_R_1030_, lean_object* v_a_1031_, lean_object* v_b_1032_, lean_object* v_c_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_1025_, v___x_1026_, v___x_1027_, v_mode_1028_, v_a_1031_, v_b_1032_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(lean_object* v_upperBound_1040_, lean_object* v___x_1041_, lean_object* v___x_1042_, lean_object* v_mode_1043_, lean_object* v_inst_1044_, lean_object* v_R_1045_, lean_object* v_a_1046_, lean_object* v_b_1047_, lean_object* v_c_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v_mode_boxed_1054_; lean_object* v_res_1055_; 
v_mode_boxed_1054_ = lean_unbox(v_mode_1043_);
v_res_1055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_1040_, v___x_1041_, v___x_1042_, v_mode_boxed_1054_, v_inst_1044_, v_R_1045_, v_a_1046_, v_b_1047_, v_c_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v___x_1041_);
lean_dec(v_upperBound_1040_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(lean_object* v_upperBound_1056_, lean_object* v_a_1057_, lean_object* v___x_1058_, lean_object* v___x_1059_, uint8_t v_mode_1060_, lean_object* v_inst_1061_, lean_object* v_R_1062_, lean_object* v_a_1063_, lean_object* v_b_1064_, lean_object* v_c_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_1056_, v_a_1057_, v___x_1058_, v___x_1059_, v_mode_1060_, v_a_1063_, v_b_1064_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(lean_object* v_upperBound_1072_, lean_object* v_a_1073_, lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v_mode_1076_, lean_object* v_inst_1077_, lean_object* v_R_1078_, lean_object* v_a_1079_, lean_object* v_b_1080_, lean_object* v_c_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
uint8_t v_mode_boxed_1087_; lean_object* v_res_1088_; 
v_mode_boxed_1087_ = lean_unbox(v_mode_1076_);
v_res_1088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_1072_, v_a_1073_, v___x_1074_, v___x_1075_, v_mode_boxed_1087_, v_inst_1077_, v_R_1078_, v_a_1079_, v_b_1080_, v_c_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v___x_1075_);
lean_dec_ref(v___x_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_upperBound_1072_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(lean_object* v_upperBound_1089_, lean_object* v_args_1090_, uint8_t v_mode_1091_, lean_object* v_b_1092_, lean_object* v_inst_1093_, lean_object* v_R_1094_, lean_object* v_a_1095_, lean_object* v_b_1096_, lean_object* v_c_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_1089_, v_args_1090_, v_mode_1091_, v_b_1092_, v_a_1095_, v_b_1096_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(lean_object* v_upperBound_1104_, lean_object* v_args_1105_, lean_object* v_mode_1106_, lean_object* v_b_1107_, lean_object* v_inst_1108_, lean_object* v_R_1109_, lean_object* v_a_1110_, lean_object* v_b_1111_, lean_object* v_c_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v_mode_boxed_1118_; lean_object* v_res_1119_; 
v_mode_boxed_1118_ = lean_unbox(v_mode_1106_);
v_res_1119_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_1104_, v_args_1105_, v_mode_boxed_1118_, v_b_1107_, v_inst_1108_, v_R_1109_, v_a_1110_, v_b_1111_, v_c_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v_args_1105_);
lean_dec(v_upperBound_1104_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(lean_object* v_upperBound_1120_, lean_object* v_a_1121_, lean_object* v_args_1122_, uint8_t v_mode_1123_, lean_object* v_b_1124_, lean_object* v_inst_1125_, lean_object* v_R_1126_, lean_object* v_a_1127_, lean_object* v_b_1128_, lean_object* v_c_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_1120_, v_a_1121_, v_args_1122_, v_mode_1123_, v_b_1124_, v_a_1127_, v_b_1128_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(lean_object* v_upperBound_1136_, lean_object* v_a_1137_, lean_object* v_args_1138_, lean_object* v_mode_1139_, lean_object* v_b_1140_, lean_object* v_inst_1141_, lean_object* v_R_1142_, lean_object* v_a_1143_, lean_object* v_b_1144_, lean_object* v_c_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
uint8_t v_mode_boxed_1151_; lean_object* v_res_1152_; 
v_mode_boxed_1151_ = lean_unbox(v_mode_1139_);
v_res_1152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_1136_, v_a_1137_, v_args_1138_, v_mode_boxed_1151_, v_b_1140_, v_inst_1141_, v_R_1142_, v_a_1143_, v_b_1144_, v_c_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v_args_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_upperBound_1136_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main(lean_object* v_a_1153_, lean_object* v_b_1154_, uint8_t v_mode_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1155_, v_a_1153_, v_b_1154_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main___boxed(lean_object* v_a_1162_, lean_object* v_b_1163_, lean_object* v_mode_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
uint8_t v_mode_boxed_1170_; lean_object* v_res_1171_; 
v_mode_boxed_1170_ = lean_unbox(v_mode_1164_);
v_res_1171_ = l_Lean_Meta_ACLt_main(v_a_1162_, v_b_1163_, v_mode_boxed_1170_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt(lean_object* v_a_1172_, lean_object* v_b_1173_, uint8_t v_mode_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1174_, v_a_1172_, v_b_1173_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt___boxed(lean_object* v_a_1181_, lean_object* v_b_1182_, lean_object* v_mode_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
uint8_t v_mode_boxed_1189_; lean_object* v_res_1190_; 
v_mode_boxed_1189_ = lean_unbox(v_mode_1183_);
v_res_1190_ = l_Lean_Meta_acLt(v_a_1181_, v_b_1182_, v_mode_boxed_1189_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
return v_res_1190_;
}
}
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ACLt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
