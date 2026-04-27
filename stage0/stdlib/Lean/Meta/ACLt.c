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
lean_object* v___f_173_; lean_object* v___x_16292__overap_174_; lean_object* v___x_175_; 
v___f_173_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0));
v___x_16292__overap_174_ = lean_panic_fn_borrowed(v___f_173_, v_msg_167_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
v___x_175_ = lean_apply_5(v___x_16292__overap_174_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(uint8_t v_mode_187_, lean_object* v_a_u2081_188_, lean_object* v_a_u2082_189_, lean_object* v_b_u2081_190_, lean_object* v_b_u2082_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_197_; 
lean_inc_ref(v_b_u2081_190_);
lean_inc_ref(v_a_u2081_188_);
v___x_197_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_187_, v_a_u2081_188_, v_b_u2081_190_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; uint8_t v___x_199_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
v___x_199_ = lean_unbox(v_a_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
lean_dec_ref(v___x_197_);
v___x_200_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_187_, v_b_u2081_190_, v_a_u2081_188_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_210_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_210_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_210_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_210_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
uint8_t v___x_205_; 
v___x_205_ = lean_unbox(v_a_201_);
lean_dec(v_a_201_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_del_object(v___x_203_);
lean_dec(v_a_198_);
v___x_206_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_187_, v_a_u2082_189_, v_b_u2082_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
return v___x_206_;
}
else
{
lean_object* v___x_208_; 
lean_dec_ref(v_b_u2082_191_);
lean_dec_ref(v_a_u2082_189_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v_a_198_);
v___x_208_ = v___x_203_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_198_);
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
else
{
lean_dec(v_a_198_);
lean_dec_ref(v_b_u2082_191_);
lean_dec_ref(v_a_u2082_189_);
return v___x_200_;
}
}
else
{
lean_dec(v_a_198_);
lean_dec_ref(v_b_u2082_191_);
lean_dec_ref(v_b_u2081_190_);
lean_dec_ref(v_a_u2082_189_);
lean_dec_ref(v_a_u2081_188_);
return v___x_197_;
}
}
else
{
lean_dec_ref(v_b_u2082_191_);
lean_dec_ref(v_b_u2081_190_);
lean_dec_ref(v_a_u2082_189_);
lean_dec_ref(v_a_u2081_188_);
return v___x_197_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2));
v___x_215_ = lean_unsigned_to_nat(14u);
v___x_216_ = lean_unsigned_to_nat(22u);
v___x_217_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1));
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0));
v___x_219_ = l_mkPanicMessageWithDecl(v___x_218_, v___x_217_, v___x_216_, v___x_215_, v___x_214_);
return v___x_219_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0(void){
_start:
{
lean_object* v___x_220_; lean_object* v_dummy_221_; 
v___x_220_ = lean_box(0);
v_dummy_221_ = l_Lean_Expr_sort___override(v___x_220_);
return v_dummy_221_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(lean_object* v_upperBound_225_, lean_object* v_a_226_, lean_object* v___x_227_, lean_object* v___x_228_, uint8_t v_mode_229_, lean_object* v_a_230_, lean_object* v_b_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_a_238_; uint8_t v___x_242_; 
v___x_242_ = lean_nat_dec_lt(v_a_230_, v_upperBound_225_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_dec(v_a_230_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v_b_231_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v_isInstance_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_b_231_);
v___x_244_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_245_ = lean_array_get_borrowed(v___x_244_, v_a_226_, v_a_230_);
v_isInstance_246_ = lean_ctor_get_uint8(v___x_245_, sizeof(void*)*1 + 4);
v___x_247_ = lean_box(0);
v___x_248_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_246_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = l_Lean_instInhabitedExpr;
v___x_250_ = lean_array_get_borrowed(v___x_249_, v___x_227_, v_a_230_);
v___x_251_ = lean_array_get_borrowed(v___x_249_, v___x_228_, v_a_230_);
lean_inc(v___x_251_);
lean_inc(v___x_250_);
v___x_252_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_229_, v___x_250_, v___x_251_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_283_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_283_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_283_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_283_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; 
v___x_257_ = lean_unbox(v_a_253_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_del_object(v___x_255_);
lean_inc(v___x_250_);
lean_inc(v___x_251_);
v___x_258_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_229_, v___x_251_, v___x_250_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_269_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_269_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint8_t v___x_263_; 
v___x_263_ = lean_unbox(v_a_259_);
lean_dec(v_a_259_);
if (v___x_263_ == 0)
{
lean_del_object(v___x_261_);
lean_dec(v_a_253_);
v_a_238_ = v___x_248_;
goto v___jp_237_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
lean_dec(v_a_230_);
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v_a_253_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_247_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_265_);
v___x_267_ = v___x_261_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_a_253_);
lean_dec(v_a_230_);
v_a_270_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_258_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_258_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec(v_a_230_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v_a_253_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_247_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_279_);
v___x_281_ = v___x_255_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v_a_230_);
v_a_284_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_252_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_252_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
v_a_238_ = v___x_248_;
goto v___jp_237_;
}
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_a_230_, v___x_239_);
lean_dec(v_a_230_);
lean_inc_ref(v_a_238_);
v_a_230_ = v___x_240_;
v_b_231_ = v_a_238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(lean_object* v_upperBound_292_, lean_object* v___x_293_, lean_object* v___x_294_, uint8_t v_mode_295_, lean_object* v_a_296_, lean_object* v_b_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_lt(v_a_296_, v_upperBound_292_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec(v_a_296_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v_b_297_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref(v_b_297_);
v___x_305_ = l_Lean_instInhabitedExpr;
v___x_306_ = lean_array_get_borrowed(v___x_305_, v___x_293_, v_a_296_);
v___x_307_ = lean_array_get_borrowed(v___x_305_, v___x_294_, v_a_296_);
lean_inc(v___x_307_);
lean_inc(v___x_306_);
v___x_308_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_295_, v___x_306_, v___x_307_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_344_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_344_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_344_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_344_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_box(0);
v___x_314_ = lean_unbox(v_a_309_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
lean_del_object(v___x_311_);
lean_inc(v___x_306_);
lean_inc(v___x_307_);
v___x_315_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_295_, v___x_307_, v___x_306_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_330_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_330_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = lean_unbox(v_a_316_);
lean_dec(v_a_316_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
lean_del_object(v___x_318_);
lean_dec(v_a_309_);
v___x_321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_a_296_, v___x_322_);
lean_dec(v_a_296_);
v_a_296_ = v___x_323_;
v_b_297_ = v___x_321_;
goto _start;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
lean_dec(v_a_296_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v_a_309_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_313_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_326_);
v___x_328_ = v___x_318_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_a_309_);
lean_dec(v_a_296_);
v_a_331_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_315_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_315_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
lean_dec(v_a_296_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_a_309_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_313_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_340_);
v___x_342_ = v___x_311_;
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
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_a_296_);
v_a_345_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_308_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_308_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(uint8_t v_mode_353_, lean_object* v_a_354_, lean_object* v_b_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_aFn_361_; lean_object* v_bFn_362_; lean_object* v___x_363_; 
v_aFn_361_ = l_Lean_Expr_getAppFn(v_a_354_);
v_bFn_362_ = l_Lean_Expr_getAppFn(v_b_355_);
lean_inc_ref(v_bFn_362_);
lean_inc_ref(v_aFn_361_);
v___x_363_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_353_, v_aFn_361_, v_bFn_362_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_462_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_462_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_462_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_462_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
uint8_t v___x_368_; uint8_t v___x_369_; 
v___x_368_ = 1;
v___x_369_ = lean_unbox(v_a_364_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_del_object(v___x_366_);
lean_inc_ref(v_aFn_361_);
v___x_370_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_353_, v_bFn_362_, v_aFn_361_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; uint8_t v___x_372_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
v___x_372_ = lean_unbox(v_a_371_);
if (v___x_372_ == 0)
{
lean_object* v_dummy_373_; lean_object* v_nargs_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_nargs_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
lean_dec(v_a_364_);
v_dummy_373_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_374_ = l_Lean_Expr_getAppNumArgs(v_a_354_);
lean_inc(v_nargs_374_);
v___x_375_ = lean_mk_array(v_nargs_374_, v_dummy_373_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_sub(v_nargs_374_, v___x_376_);
lean_dec(v_nargs_374_);
v___x_378_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_354_, v___x_375_, v___x_377_);
v_nargs_379_ = l_Lean_Expr_getAppNumArgs(v_b_355_);
lean_inc(v_nargs_379_);
v___x_380_ = lean_mk_array(v_nargs_379_, v_dummy_373_);
v___x_381_ = lean_nat_sub(v_nargs_379_, v___x_376_);
lean_dec(v_nargs_379_);
v___x_382_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_b_355_, v___x_380_, v___x_381_);
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
lean_dec_ref(v___x_370_);
v___x_387_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_361_, v___x_383_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref(v___x_387_);
v___x_389_ = lean_array_get_size(v_a_388_);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_389_, v_a_388_, v___x_378_, v___x_382_, v_mode_353_, v___x_390_, v___x_391_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_388_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_424_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_424_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_424_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_424_;
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
v___x_398_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_383_, v___x_378_, v___x_382_, v_mode_353_, v___x_389_, v___x_391_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_411_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_411_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_411_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_411_;
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
lean_object* v___x_405_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_a_371_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_371_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
else
{
lean_object* v_val_407_; lean_object* v___x_409_; 
lean_dec(v_a_371_);
v_val_407_ = lean_ctor_get(v_fst_403_, 0);
lean_inc(v_val_407_);
lean_dec_ref(v_fst_403_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_val_407_);
v___x_409_ = v___x_401_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_val_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_a_371_);
v_a_412_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_398_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_398_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_val_420_; lean_object* v___x_422_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
lean_dec(v_a_371_);
v_val_420_ = lean_ctor_get(v_fst_397_, 0);
lean_inc(v_val_420_);
lean_dec_ref(v_fst_397_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v_val_420_);
v___x_422_ = v___x_395_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_val_420_);
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
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
lean_dec(v_a_371_);
v_a_425_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_392_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_392_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
lean_dec(v_a_371_);
v_a_433_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_387_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_387_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
lean_dec(v_a_371_);
lean_dec_ref(v_aFn_361_);
return v___x_370_;
}
}
else
{
lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_378_);
lean_dec(v_a_371_);
lean_dec_ref(v_aFn_361_);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_449_);
v___x_442_ = v___x_370_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_dec(v___x_370_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_box(v___x_368_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_a_371_);
lean_dec_ref(v_aFn_361_);
lean_dec_ref(v_b_355_);
lean_dec_ref(v_a_354_);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_457_);
v___x_451_ = v___x_370_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_dec(v___x_370_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_a_364_);
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_364_);
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
else
{
lean_dec(v_a_364_);
lean_dec_ref(v_aFn_361_);
lean_dec_ref(v_b_355_);
lean_dec_ref(v_a_354_);
return v___x_370_;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_460_; 
lean_dec(v_a_364_);
lean_dec_ref(v_bFn_362_);
lean_dec_ref(v_aFn_361_);
lean_dec_ref(v_b_355_);
lean_dec_ref(v_a_354_);
v___x_458_ = lean_box(v___x_368_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_458_);
v___x_460_ = v___x_366_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_dec_ref(v_bFn_362_);
lean_dec_ref(v_aFn_361_);
lean_dec_ref(v_b_355_);
lean_dec_ref(v_a_354_);
return v___x_363_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6));
v___x_467_ = lean_unsigned_to_nat(27u);
v___x_468_ = lean_unsigned_to_nat(152u);
v___x_469_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5));
v___x_470_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4));
v___x_471_ = l_mkPanicMessageWithDecl(v___x_470_, v___x_469_, v___x_468_, v___x_467_, v___x_466_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(uint8_t v_mode_472_, lean_object* v_a_473_, lean_object* v_b_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_d_481_; lean_object* v_e_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; 
switch(lean_obj_tag(v_a_473_))
{
case 0:
{
lean_object* v_deBruijnIndex_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_deBruijnIndex_490_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_deBruijnIndex_490_);
lean_dec_ref(v_a_473_);
v___x_491_ = l_Lean_Expr_bvarIdx_x21(v_b_474_);
lean_dec_ref(v_b_474_);
v___x_492_ = lean_nat_dec_lt(v_deBruijnIndex_490_, v___x_491_);
lean_dec(v___x_491_);
lean_dec(v_deBruijnIndex_490_);
v___x_493_ = lean_box(v___x_492_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
case 1:
{
lean_object* v_fvarId_495_; lean_object* v___x_496_; 
v_fvarId_495_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_fvarId_495_);
lean_dec_ref(v_a_473_);
v___x_496_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_495_, v_a_475_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref(v___x_496_);
v___x_498_ = l_Lean_Expr_fvarId_x21(v_b_474_);
lean_dec_ref(v_b_474_);
v___x_499_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_498_, v_a_475_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_522_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_522_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_522_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_522_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_514_; 
if (lean_obj_tag(v_a_497_) == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_520_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_519_);
v___y_514_ = v___x_520_;
goto v___jp_513_;
}
else
{
lean_object* v_val_521_; 
v_val_521_ = lean_ctor_get(v_a_497_, 0);
lean_inc(v_val_521_);
lean_dec_ref(v_a_497_);
v___y_514_ = v_val_521_;
goto v___jp_513_;
}
v___jp_504_:
{
lean_object* v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_507_ = l_Lean_LocalDecl_index(v___y_506_);
lean_dec_ref(v___y_506_);
v___x_508_ = lean_nat_dec_lt(v___y_505_, v___x_507_);
lean_dec(v___x_507_);
lean_dec(v___y_505_);
v___x_509_ = lean_box(v___x_508_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_509_);
v___x_511_ = v___x_502_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
v___jp_513_:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_LocalDecl_index(v___y_514_);
lean_dec_ref(v___y_514_);
if (lean_obj_tag(v_a_500_) == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_517_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_516_);
v___y_505_ = v___x_515_;
v___y_506_ = v___x_517_;
goto v___jp_504_;
}
else
{
lean_object* v_val_518_; 
v_val_518_ = lean_ctor_get(v_a_500_, 0);
lean_inc(v_val_518_);
lean_dec_ref(v_a_500_);
v___y_505_ = v___x_515_;
v___y_506_ = v_val_518_;
goto v___jp_504_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_a_497_);
v_a_523_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_499_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_499_);
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
lean_dec_ref(v_b_474_);
v_a_531_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_496_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_496_);
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
case 2:
{
lean_object* v_mvarId_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_mvarId_539_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_mvarId_539_);
lean_dec_ref(v_a_473_);
v___x_540_ = l_Lean_Expr_mvarId_x21(v_b_474_);
lean_dec_ref(v_b_474_);
v___x_541_ = l_Lean_Name_lt(v_mvarId_539_, v___x_540_);
lean_dec(v___x_540_);
lean_dec(v_mvarId_539_);
v___x_542_ = lean_box(v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
case 3:
{
lean_object* v_u_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_u_544_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_u_544_);
lean_dec_ref(v_a_473_);
v___x_545_ = l_Lean_Expr_sortLevel_x21(v_b_474_);
lean_dec_ref(v_b_474_);
v___x_546_ = l_Lean_Level_normLt(v_u_544_, v___x_545_);
lean_dec(v___x_545_);
lean_dec(v_u_544_);
v___x_547_ = lean_box(v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
case 4:
{
lean_object* v_declName_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_declName_549_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_declName_549_);
lean_dec_ref(v_a_473_);
v___x_550_ = l_Lean_Expr_constName_x21(v_b_474_);
lean_dec_ref(v_b_474_);
v___x_551_ = l_Lean_Name_lt(v_declName_549_, v___x_550_);
lean_dec(v___x_550_);
lean_dec(v_declName_549_);
v___x_552_ = lean_box(v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
case 5:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_472_, v_a_473_, v_b_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_554_;
}
case 8:
{
lean_object* v_value_555_; lean_object* v_body_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_value_555_ = lean_ctor_get(v_a_473_, 2);
lean_inc_ref(v_value_555_);
v_body_556_ = lean_ctor_get(v_a_473_, 3);
lean_inc_ref(v_body_556_);
lean_dec_ref(v_a_473_);
v___x_557_ = l_Lean_Expr_letValue_x21(v_b_474_);
v___x_558_ = l_Lean_Expr_letBody_x21(v_b_474_);
lean_dec_ref(v_b_474_);
v___x_559_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_472_, v_value_555_, v_body_556_, v___x_557_, v___x_558_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_559_;
}
case 9:
{
lean_object* v_a_560_; lean_object* v___x_561_; uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_a_560_ = lean_ctor_get(v_a_473_, 0);
lean_inc_ref(v_a_560_);
lean_dec_ref(v_a_473_);
v___x_561_ = l_Lean_Expr_litValue_x21(v_b_474_);
lean_dec_ref(v_b_474_);
v___x_562_ = l_Lean_Literal_lt(v_a_560_, v___x_561_);
lean_dec_ref(v___x_561_);
lean_dec_ref(v_a_560_);
v___x_563_ = lean_box(v___x_562_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
case 10:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v_a_473_);
lean_dec_ref(v_b_474_);
v___x_565_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
v___x_566_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_565_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_566_;
}
case 11:
{
lean_object* v_idx_567_; lean_object* v_struct_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_idx_567_ = lean_ctor_get(v_a_473_, 1);
lean_inc(v_idx_567_);
v_struct_568_ = lean_ctor_get(v_a_473_, 2);
lean_inc_ref(v_struct_568_);
lean_dec_ref(v_a_473_);
v___x_569_ = l_Lean_Expr_projIdx_x21(v_b_474_);
v___x_570_ = lean_nat_dec_eq(v_idx_567_, v___x_569_);
if (v___x_570_ == 0)
{
uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec_ref(v_struct_568_);
lean_dec_ref(v_b_474_);
v___x_571_ = lean_nat_dec_lt(v_idx_567_, v___x_569_);
lean_dec(v___x_569_);
lean_dec(v_idx_567_);
v___x_572_ = lean_box(v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v___x_569_);
lean_dec(v_idx_567_);
v___x_574_ = l_Lean_Expr_projExpr_x21(v_b_474_);
lean_dec_ref(v_b_474_);
v___x_575_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_472_, v_struct_568_, v___x_574_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_575_;
}
}
default: 
{
lean_object* v_binderType_576_; lean_object* v_body_577_; 
v_binderType_576_ = lean_ctor_get(v_a_473_, 1);
lean_inc_ref(v_binderType_576_);
v_body_577_ = lean_ctor_get(v_a_473_, 2);
lean_inc_ref(v_body_577_);
lean_dec_ref(v_a_473_);
v_d_481_ = v_binderType_576_;
v_e_482_ = v_body_577_;
v___y_483_ = v_a_475_;
v___y_484_ = v_a_476_;
v___y_485_ = v_a_477_;
v___y_486_ = v_a_478_;
goto v___jp_480_;
}
}
v___jp_480_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = l_Lean_Expr_bindingDomain_x21(v_b_474_);
v___x_488_ = l_Lean_Expr_bindingBody_x21(v_b_474_);
lean_dec_ref(v_b_474_);
v___x_489_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_472_, v_d_481_, v_e_482_, v___x_487_, v___x_488_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(uint8_t v_mode_578_, lean_object* v_a_579_, lean_object* v_b_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0));
v___x_587_ = l_Lean_Core_checkSystem(v___x_586_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_588_; 
lean_dec_ref(v___x_587_);
lean_inc_ref(v_a_579_);
lean_inc_ref(v_b_580_);
v___x_588_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_578_, v_b_580_, v_a_579_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; uint8_t v___x_590_; uint8_t v___x_591_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
v___x_590_ = 1;
v___x_591_ = lean_unbox(v_a_589_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; uint8_t v___x_593_; uint8_t v___x_594_; 
v___x_592_ = l_Lean_Expr_ctorWeight(v_b_580_);
v___x_593_ = l_Lean_Expr_ctorWeight(v_a_579_);
v___x_594_ = lean_uint8_dec_lt(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
lean_dec_ref(v___x_588_);
lean_inc_ref(v_b_580_);
lean_inc_ref(v_a_579_);
v___x_595_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_578_, v_a_579_, v_b_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_610_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_610_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v___x_600_; 
v___x_600_ = lean_unbox(v_a_596_);
lean_dec(v_a_596_);
if (v___x_600_ == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v_b_580_);
lean_dec_ref(v_a_579_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_a_589_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_589_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
else
{
uint8_t v___x_604_; 
lean_dec(v_a_589_);
v___x_604_ = lean_uint8_dec_lt(v___x_593_, v___x_592_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_del_object(v___x_598_);
v___x_605_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_578_, v_a_579_, v_b_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec_ref(v_b_580_);
lean_dec_ref(v_a_579_);
v___x_606_ = lean_box(v___x_590_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_606_);
v___x_608_ = v___x_598_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
else
{
lean_dec(v_a_589_);
lean_dec_ref(v_b_580_);
lean_dec_ref(v_a_579_);
return v___x_595_;
}
}
else
{
lean_dec(v_a_589_);
lean_dec_ref(v_b_580_);
lean_dec_ref(v_a_579_);
return v___x_588_;
}
}
else
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_a_589_);
lean_dec_ref(v_b_580_);
lean_dec_ref(v_a_579_);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v___x_588_, 0);
lean_dec(v_unused_619_);
v___x_612_ = v___x_588_;
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
else
{
lean_dec(v___x_588_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = lean_box(v___x_590_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
else
{
lean_dec_ref(v_b_580_);
lean_dec_ref(v_a_579_);
return v___x_588_;
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_b_580_);
lean_dec_ref(v_a_579_);
v_a_620_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_587_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_587_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(uint8_t v_mode_628_, lean_object* v_a_629_, lean_object* v_b_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
uint8_t v___x_636_; 
v___x_636_ = lean_expr_eqv(v_a_629_, v_b_630_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; 
v___x_637_ = l_Lean_Expr_isMData(v_a_629_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; 
v___x_638_ = l_Lean_Expr_isMData(v_b_630_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
v___x_639_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_628_, v_a_629_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_628_, v_b_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref(v___x_641_);
v___x_643_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_628_, v_a_640_, v_a_642_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_643_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_a_640_);
v_a_644_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_641_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v_b_630_);
v_a_652_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_639_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_639_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Expr_mdataExpr_x21(v_b_630_);
lean_dec_ref(v_b_630_);
v_b_630_ = v___x_660_;
goto _start;
}
}
else
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Expr_mdataExpr_x21(v_a_629_);
lean_dec_ref(v_a_629_);
v_a_629_ = v___x_662_;
goto _start;
}
}
else
{
uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec_ref(v_b_630_);
lean_dec_ref(v_a_629_);
v___x_664_ = 0;
v___x_665_ = lean_box(v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(lean_object* v_upperBound_667_, lean_object* v_a_668_, lean_object* v_args_669_, uint8_t v_mode_670_, lean_object* v_b_671_, lean_object* v_a_672_, lean_object* v_b_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_a_680_; uint8_t v___x_684_; 
v___x_684_ = lean_nat_dec_lt(v_a_672_, v_upperBound_667_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
lean_dec(v_a_672_);
lean_dec_ref(v_b_671_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_673_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v_isInstance_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec_ref(v_b_673_);
v___x_686_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_687_ = lean_array_get_borrowed(v___x_686_, v_a_668_, v_a_672_);
v_isInstance_688_ = lean_ctor_get_uint8(v___x_687_, sizeof(void*)*1 + 4);
v___x_689_ = lean_box(0);
v___x_690_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_688_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = l_Lean_instInhabitedExpr;
v___x_692_ = lean_array_get_borrowed(v___x_691_, v_args_669_, v_a_672_);
lean_inc_ref(v_b_671_);
lean_inc(v___x_692_);
v___x_693_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_670_, v___x_692_, v_b_671_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_704_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_704_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_704_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_704_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
uint8_t v___x_698_; 
v___x_698_ = lean_unbox(v_a_694_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec(v_a_672_);
lean_dec_ref(v_b_671_);
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v_a_694_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_689_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_700_);
v___x_702_ = v___x_696_;
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
else
{
lean_del_object(v___x_696_);
lean_dec(v_a_694_);
v_a_680_ = v___x_690_;
goto v___jp_679_;
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_a_672_);
lean_dec_ref(v_b_671_);
v_a_705_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_693_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_693_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
v_a_680_ = v___x_690_;
goto v___jp_679_;
}
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_a_672_, v___x_681_);
lean_dec(v_a_672_);
lean_inc_ref(v_a_680_);
v_a_672_ = v___x_682_;
v_b_673_ = v_a_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(lean_object* v_upperBound_713_, lean_object* v_args_714_, uint8_t v_mode_715_, lean_object* v_b_716_, lean_object* v_a_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = lean_nat_dec_lt(v_a_717_, v_upperBound_713_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec(v_a_717_);
lean_dec_ref(v_b_716_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_b_718_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v_b_718_);
v___x_726_ = lean_array_fget_borrowed(v_args_714_, v_a_717_);
lean_inc_ref(v_b_716_);
lean_inc(v___x_726_);
v___x_727_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_715_, v___x_726_, v_b_716_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_743_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_743_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_743_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_743_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_box(0);
v___x_733_ = lean_unbox(v_a_728_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec(v_a_717_);
lean_dec_ref(v_b_716_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v_a_728_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v___x_732_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_735_);
v___x_737_ = v___x_730_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_del_object(v___x_730_);
lean_dec(v_a_728_);
v___x_739_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_a_717_, v___x_740_);
lean_dec(v_a_717_);
v_a_717_ = v___x_741_;
v_b_718_ = v___x_739_;
goto _start;
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_717_);
lean_dec_ref(v_b_716_);
v_a_744_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_727_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_727_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(uint8_t v_mode_752_, lean_object* v_b_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
if (lean_obj_tag(v_x_754_) == 5)
{
lean_object* v_fn_762_; lean_object* v_arg_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_fn_762_ = lean_ctor_get(v_x_754_, 0);
lean_inc_ref(v_fn_762_);
v_arg_763_ = lean_ctor_get(v_x_754_, 1);
lean_inc_ref(v_arg_763_);
lean_dec_ref(v_x_754_);
v___x_764_ = lean_array_set(v_x_755_, v_x_756_, v_arg_763_);
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_sub(v_x_756_, v___x_765_);
lean_dec(v_x_756_);
v_x_754_ = v_fn_762_;
v_x_755_ = v___x_764_;
v_x_756_ = v___x_766_;
goto _start;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v_x_756_);
v___x_768_ = lean_array_get_size(v_x_755_);
v___x_769_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_x_754_, v___x_768_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
v___x_771_ = lean_array_get_size(v_a_770_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
lean_inc_ref(v_b_753_);
v___x_774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_771_, v_a_770_, v_x_755_, v_mode_752_, v_b_753_, v___x_772_, v___x_773_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v_a_770_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_808_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_808_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_808_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_808_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_fst_779_; 
v_fst_779_ = lean_ctor_get(v_a_775_, 0);
lean_inc(v_fst_779_);
lean_dec(v_a_775_);
if (lean_obj_tag(v_fst_779_) == 0)
{
lean_object* v___x_780_; 
lean_del_object(v___x_777_);
v___x_780_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_768_, v_x_755_, v_mode_752_, v_b_753_, v___x_771_, v___x_773_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec_ref(v_x_755_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_795_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_795_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_fst_785_; 
v_fst_785_ = lean_ctor_get(v_a_781_, 0);
lean_inc(v_fst_785_);
lean_dec(v_a_781_);
if (lean_obj_tag(v_fst_785_) == 0)
{
uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_786_ = 1;
v___x_787_ = lean_box(v___x_786_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_787_);
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
else
{
lean_object* v_val_791_; lean_object* v___x_793_; 
v_val_791_ = lean_ctor_get(v_fst_785_, 0);
lean_inc(v_val_791_);
lean_dec_ref(v_fst_785_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_val_791_);
v___x_793_ = v___x_783_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_val_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_780_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_780_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
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
lean_object* v_val_804_; lean_object* v___x_806_; 
lean_dec_ref(v_x_755_);
lean_dec_ref(v_b_753_);
v_val_804_ = lean_ctor_get(v_fst_779_, 0);
lean_inc(v_val_804_);
lean_dec_ref(v_fst_779_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v_val_804_);
v___x_806_ = v___x_777_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_val_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_x_755_);
lean_dec_ref(v_b_753_);
v_a_809_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_774_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_774_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_x_755_);
lean_dec_ref(v_b_753_);
v_a_817_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_769_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_769_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(uint8_t v_mode_825_, lean_object* v_a_826_, lean_object* v_b_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_d_834_; lean_object* v_e_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; 
switch(lean_obj_tag(v_a_826_))
{
case 11:
{
lean_object* v_struct_844_; lean_object* v___x_845_; 
v_struct_844_ = lean_ctor_get(v_a_826_, 2);
lean_inc_ref(v_struct_844_);
lean_dec_ref(v_a_826_);
v___x_845_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_825_, v_struct_844_, v_b_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
return v___x_845_;
}
case 5:
{
lean_object* v_dummy_846_; lean_object* v_nargs_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_dummy_846_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_847_ = l_Lean_Expr_getAppNumArgs(v_a_826_);
lean_inc(v_nargs_847_);
v___x_848_ = lean_mk_array(v_nargs_847_, v_dummy_846_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_sub(v_nargs_847_, v___x_849_);
lean_dec(v_nargs_847_);
v___x_851_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_825_, v_b_827_, v_a_826_, v___x_848_, v___x_850_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
return v___x_851_;
}
case 6:
{
lean_object* v_binderType_852_; lean_object* v_body_853_; 
v_binderType_852_ = lean_ctor_get(v_a_826_, 1);
lean_inc_ref(v_binderType_852_);
v_body_853_ = lean_ctor_get(v_a_826_, 2);
lean_inc_ref(v_body_853_);
lean_dec_ref(v_a_826_);
v_d_834_ = v_binderType_852_;
v_e_835_ = v_body_853_;
v___y_836_ = v_a_828_;
v___y_837_ = v_a_829_;
v___y_838_ = v_a_830_;
v___y_839_ = v_a_831_;
goto v___jp_833_;
}
case 7:
{
lean_object* v_binderType_854_; lean_object* v_body_855_; 
v_binderType_854_ = lean_ctor_get(v_a_826_, 1);
lean_inc_ref(v_binderType_854_);
v_body_855_ = lean_ctor_get(v_a_826_, 2);
lean_inc_ref(v_body_855_);
lean_dec_ref(v_a_826_);
v_d_834_ = v_binderType_854_;
v_e_835_ = v_body_855_;
v___y_836_ = v_a_828_;
v___y_837_ = v_a_829_;
v___y_838_ = v_a_830_;
v___y_839_ = v_a_831_;
goto v___jp_833_;
}
case 8:
{
lean_object* v_value_856_; lean_object* v_body_857_; lean_object* v___x_858_; 
v_value_856_ = lean_ctor_get(v_a_826_, 2);
lean_inc_ref(v_value_856_);
v_body_857_ = lean_ctor_get(v_a_826_, 3);
lean_inc_ref(v_body_857_);
lean_dec_ref(v_a_826_);
lean_inc_ref(v_b_827_);
v___x_858_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_825_, v_value_856_, v_b_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; uint8_t v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
v___x_860_ = lean_unbox(v_a_859_);
lean_dec(v_a_859_);
if (v___x_860_ == 0)
{
lean_dec_ref(v_body_857_);
lean_dec_ref(v_b_827_);
return v___x_858_;
}
else
{
lean_object* v___x_861_; 
lean_dec_ref(v___x_858_);
v___x_861_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_825_, v_body_857_, v_b_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
return v___x_861_;
}
}
else
{
lean_dec_ref(v_body_857_);
lean_dec_ref(v_b_827_);
return v___x_858_;
}
}
default: 
{
uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec_ref(v_b_827_);
lean_dec_ref(v_a_826_);
v___x_862_ = 1;
v___x_863_ = lean_box(v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
v___jp_833_:
{
lean_object* v___x_840_; 
lean_inc_ref(v_b_827_);
v___x_840_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_825_, v_d_834_, v_b_827_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
v___x_842_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_842_ == 0)
{
lean_dec_ref(v_e_835_);
lean_dec_ref(v_b_827_);
return v___x_840_;
}
else
{
lean_object* v___x_843_; 
lean_dec_ref(v___x_840_);
v___x_843_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_825_, v_e_835_, v_b_827_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
return v___x_843_;
}
}
else
{
lean_dec_ref(v_e_835_);
lean_dec_ref(v_b_827_);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(uint8_t v_mode_865_, lean_object* v_a_866_, lean_object* v_b_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_865_, v_a_866_, v_b_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_889_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_889_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_889_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_889_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint8_t v___x_878_; 
v___x_878_ = lean_unbox(v_a_874_);
lean_dec(v_a_874_);
if (v___x_878_ == 0)
{
uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_879_ = 1;
v___x_880_ = lean_box(v___x_879_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_880_);
v___x_882_ = v___x_876_;
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
else
{
uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = 0;
v___x_885_ = lean_box(v___x_884_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_885_);
v___x_887_ = v___x_876_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(lean_object* v_mode_890_, lean_object* v_a_891_, lean_object* v_b_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
uint8_t v_mode_boxed_898_; lean_object* v_res_899_; 
v_mode_boxed_898_ = lean_unbox(v_mode_890_);
v_res_899_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_boxed_898_, v_a_891_, v_b_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(lean_object* v_mode_900_, lean_object* v_a_u2081_901_, lean_object* v_a_u2082_902_, lean_object* v_b_u2081_903_, lean_object* v_b_u2082_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
uint8_t v_mode_boxed_910_; lean_object* v_res_911_; 
v_mode_boxed_910_ = lean_unbox(v_mode_900_);
v_res_911_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_boxed_910_, v_a_u2081_901_, v_a_u2082_902_, v_b_u2081_903_, v_b_u2082_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(lean_object* v_upperBound_912_, lean_object* v_args_913_, lean_object* v_mode_914_, lean_object* v_b_915_, lean_object* v_a_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
uint8_t v_mode_boxed_923_; lean_object* v_res_924_; 
v_mode_boxed_923_ = lean_unbox(v_mode_914_);
v_res_924_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_912_, v_args_913_, v_mode_boxed_923_, v_b_915_, v_a_916_, v_b_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec_ref(v_args_913_);
lean_dec(v_upperBound_912_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object* v_mode_925_, lean_object* v_a_926_, lean_object* v_b_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
uint8_t v_mode_boxed_933_; lean_object* v_res_934_; 
v_mode_boxed_933_ = lean_unbox(v_mode_925_);
v_res_934_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_boxed_933_, v_a_926_, v_b_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object* v_upperBound_935_, lean_object* v_a_936_, lean_object* v_args_937_, lean_object* v_mode_938_, lean_object* v_b_939_, lean_object* v_a_940_, lean_object* v_b_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v_mode_boxed_947_; lean_object* v_res_948_; 
v_mode_boxed_947_ = lean_unbox(v_mode_938_);
v_res_948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_935_, v_a_936_, v_args_937_, v_mode_boxed_947_, v_b_939_, v_a_940_, v_b_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec_ref(v_args_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_upperBound_935_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object* v_mode_949_, lean_object* v_a_950_, lean_object* v_b_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
uint8_t v_mode_boxed_957_; lean_object* v_res_958_; 
v_mode_boxed_957_ = lean_unbox(v_mode_949_);
v_res_958_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_boxed_957_, v_a_950_, v_b_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object* v_mode_959_, lean_object* v_a_960_, lean_object* v_b_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
uint8_t v_mode_boxed_967_; lean_object* v_res_968_; 
v_mode_boxed_967_ = lean_unbox(v_mode_959_);
v_res_968_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_boxed_967_, v_a_960_, v_b_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(lean_object* v_upperBound_969_, lean_object* v___x_970_, lean_object* v___x_971_, lean_object* v_mode_972_, lean_object* v_a_973_, lean_object* v_b_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
uint8_t v_mode_boxed_980_; lean_object* v_res_981_; 
v_mode_boxed_980_ = lean_unbox(v_mode_972_);
v_res_981_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_969_, v___x_970_, v___x_971_, v_mode_boxed_980_, v_a_973_, v_b_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_970_);
lean_dec(v_upperBound_969_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(lean_object* v_mode_982_, lean_object* v_b_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v_mode_boxed_992_; lean_object* v_res_993_; 
v_mode_boxed_992_ = lean_unbox(v_mode_982_);
v_res_993_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_992_, v_b_983_, v_x_984_, v_x_985_, v_x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(lean_object* v_upperBound_994_, lean_object* v_a_995_, lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v_mode_998_, lean_object* v_a_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v_mode_boxed_1006_; lean_object* v_res_1007_; 
v_mode_boxed_1006_ = lean_unbox(v_mode_998_);
v_res_1007_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_994_, v_a_995_, v___x_996_, v___x_997_, v_mode_boxed_1006_, v_a_999_, v_b_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v___x_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_upperBound_994_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(lean_object* v_mode_1008_, lean_object* v_a_1009_, lean_object* v_b_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
uint8_t v_mode_boxed_1016_; lean_object* v_res_1017_; 
v_mode_boxed_1016_ = lean_unbox(v_mode_1008_);
v_res_1017_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_boxed_1016_, v_a_1009_, v_b_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(lean_object* v_mode_1018_, lean_object* v_a_1019_, lean_object* v_b_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
uint8_t v_mode_boxed_1026_; lean_object* v_res_1027_; 
v_mode_boxed_1026_ = lean_unbox(v_mode_1018_);
v_res_1027_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_boxed_1026_, v_a_1019_, v_b_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(lean_object* v_upperBound_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, uint8_t v_mode_1031_, lean_object* v_inst_1032_, lean_object* v_R_1033_, lean_object* v_a_1034_, lean_object* v_b_1035_, lean_object* v_c_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_1028_, v___x_1029_, v___x_1030_, v_mode_1031_, v_a_1034_, v_b_1035_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(lean_object* v_upperBound_1043_, lean_object* v___x_1044_, lean_object* v___x_1045_, lean_object* v_mode_1046_, lean_object* v_inst_1047_, lean_object* v_R_1048_, lean_object* v_a_1049_, lean_object* v_b_1050_, lean_object* v_c_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
uint8_t v_mode_boxed_1057_; lean_object* v_res_1058_; 
v_mode_boxed_1057_ = lean_unbox(v_mode_1046_);
v_res_1058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_1043_, v___x_1044_, v___x_1045_, v_mode_boxed_1057_, v_inst_1047_, v_R_1048_, v_a_1049_, v_b_1050_, v_c_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v___x_1044_);
lean_dec(v_upperBound_1043_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(lean_object* v_upperBound_1059_, lean_object* v_a_1060_, lean_object* v___x_1061_, lean_object* v___x_1062_, uint8_t v_mode_1063_, lean_object* v_inst_1064_, lean_object* v_R_1065_, lean_object* v_a_1066_, lean_object* v_b_1067_, lean_object* v_c_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_1059_, v_a_1060_, v___x_1061_, v___x_1062_, v_mode_1063_, v_a_1066_, v_b_1067_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(lean_object* v_upperBound_1075_, lean_object* v_a_1076_, lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v_mode_1079_, lean_object* v_inst_1080_, lean_object* v_R_1081_, lean_object* v_a_1082_, lean_object* v_b_1083_, lean_object* v_c_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
uint8_t v_mode_boxed_1090_; lean_object* v_res_1091_; 
v_mode_boxed_1090_ = lean_unbox(v_mode_1079_);
v_res_1091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_1075_, v_a_1076_, v___x_1077_, v___x_1078_, v_mode_boxed_1090_, v_inst_1080_, v_R_1081_, v_a_1082_, v_b_1083_, v_c_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v___x_1078_);
lean_dec_ref(v___x_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_upperBound_1075_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(lean_object* v_upperBound_1092_, lean_object* v_args_1093_, uint8_t v_mode_1094_, lean_object* v_b_1095_, lean_object* v_inst_1096_, lean_object* v_R_1097_, lean_object* v_a_1098_, lean_object* v_b_1099_, lean_object* v_c_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_1092_, v_args_1093_, v_mode_1094_, v_b_1095_, v_a_1098_, v_b_1099_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(lean_object* v_upperBound_1107_, lean_object* v_args_1108_, lean_object* v_mode_1109_, lean_object* v_b_1110_, lean_object* v_inst_1111_, lean_object* v_R_1112_, lean_object* v_a_1113_, lean_object* v_b_1114_, lean_object* v_c_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
uint8_t v_mode_boxed_1121_; lean_object* v_res_1122_; 
v_mode_boxed_1121_ = lean_unbox(v_mode_1109_);
v_res_1122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_1107_, v_args_1108_, v_mode_boxed_1121_, v_b_1110_, v_inst_1111_, v_R_1112_, v_a_1113_, v_b_1114_, v_c_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec_ref(v_args_1108_);
lean_dec(v_upperBound_1107_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(lean_object* v_upperBound_1123_, lean_object* v_a_1124_, lean_object* v_args_1125_, uint8_t v_mode_1126_, lean_object* v_b_1127_, lean_object* v_inst_1128_, lean_object* v_R_1129_, lean_object* v_a_1130_, lean_object* v_b_1131_, lean_object* v_c_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_1123_, v_a_1124_, v_args_1125_, v_mode_1126_, v_b_1127_, v_a_1130_, v_b_1131_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(lean_object* v_upperBound_1139_, lean_object* v_a_1140_, lean_object* v_args_1141_, lean_object* v_mode_1142_, lean_object* v_b_1143_, lean_object* v_inst_1144_, lean_object* v_R_1145_, lean_object* v_a_1146_, lean_object* v_b_1147_, lean_object* v_c_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v_mode_boxed_1154_; lean_object* v_res_1155_; 
v_mode_boxed_1154_ = lean_unbox(v_mode_1142_);
v_res_1155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_1139_, v_a_1140_, v_args_1141_, v_mode_boxed_1154_, v_b_1143_, v_inst_1144_, v_R_1145_, v_a_1146_, v_b_1147_, v_c_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v_args_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_upperBound_1139_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main(lean_object* v_a_1156_, lean_object* v_b_1157_, uint8_t v_mode_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1158_, v_a_1156_, v_b_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main___boxed(lean_object* v_a_1165_, lean_object* v_b_1166_, lean_object* v_mode_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
uint8_t v_mode_boxed_1173_; lean_object* v_res_1174_; 
v_mode_boxed_1173_ = lean_unbox(v_mode_1167_);
v_res_1174_ = l_Lean_Meta_ACLt_main(v_a_1165_, v_b_1166_, v_mode_boxed_1173_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt(lean_object* v_a_1175_, lean_object* v_b_1176_, uint8_t v_mode_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1177_, v_a_1175_, v_b_1176_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt___boxed(lean_object* v_a_1184_, lean_object* v_b_1185_, lean_object* v_mode_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v_mode_boxed_1192_; lean_object* v_res_1193_; 
v_mode_boxed_1192_ = lean_unbox(v_mode_1186_);
v_res_1193_ = l_Lean_Meta_acLt(v_a_1184_, v_b_1185_, v_mode_boxed_1192_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1193_;
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
