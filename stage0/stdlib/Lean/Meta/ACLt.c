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
uint8_t lean_bool_not(uint8_t);
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_115_, 7);
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
lean_object* v___f_173_; lean_object* v___x_15931__overap_174_; lean_object* v___x_175_; 
v___f_173_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0));
v___x_15931__overap_174_ = lean_panic_fn_borrowed(v___f_173_, v_msg_167_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
v___x_175_ = lean_apply_5(v___x_15931__overap_174_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, lean_box(0));
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
lean_dec_ref_known(v___x_197_, 1);
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
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v_isInstance_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
lean_dec_ref(v_b_231_);
v___x_244_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_245_ = lean_array_get_borrowed(v___x_244_, v_a_226_, v_a_230_);
v_isInstance_246_ = lean_ctor_get_uint8(v___x_245_, sizeof(void*)*1 + 4);
v___x_247_ = lean_box(0);
v___x_248_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_249_ = lean_bool_not(v_isInstance_246_);
if (v___x_249_ == 0)
{
v_a_238_ = v___x_248_;
goto v___jp_237_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = l_Lean_instInhabitedExpr;
v___x_251_ = lean_array_get_borrowed(v___x_250_, v___x_227_, v_a_230_);
v___x_252_ = lean_array_get_borrowed(v___x_250_, v___x_228_, v_a_230_);
lean_inc(v___x_252_);
lean_inc(v___x_251_);
v___x_253_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_229_, v___x_251_, v___x_252_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_284_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_284_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_284_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_284_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
uint8_t v___x_258_; 
v___x_258_ = lean_unbox(v_a_254_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_del_object(v___x_256_);
lean_inc(v___x_251_);
lean_inc(v___x_252_);
v___x_259_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_229_, v___x_252_, v___x_251_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_270_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_270_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_270_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_270_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
uint8_t v___x_264_; 
v___x_264_ = lean_unbox(v_a_260_);
lean_dec(v_a_260_);
if (v___x_264_ == 0)
{
lean_del_object(v___x_262_);
lean_dec(v_a_254_);
v_a_238_ = v___x_248_;
goto v___jp_237_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
lean_dec(v_a_230_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_a_254_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_247_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_266_);
v___x_268_ = v___x_262_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec(v_a_254_);
lean_dec(v_a_230_);
v_a_271_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_259_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_259_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
lean_dec(v_a_230_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_a_254_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_247_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_280_);
v___x_282_ = v___x_256_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec(v_a_230_);
v_a_285_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_253_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_253_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(lean_object* v_upperBound_293_, lean_object* v___x_294_, lean_object* v___x_295_, uint8_t v_mode_296_, lean_object* v_a_297_, lean_object* v_b_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = lean_nat_dec_lt(v_a_297_, v_upperBound_293_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_dec(v_a_297_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v_b_298_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec_ref(v_b_298_);
v___x_306_ = l_Lean_instInhabitedExpr;
v___x_307_ = lean_array_get_borrowed(v___x_306_, v___x_294_, v_a_297_);
v___x_308_ = lean_array_get_borrowed(v___x_306_, v___x_295_, v_a_297_);
lean_inc(v___x_308_);
lean_inc(v___x_307_);
v___x_309_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_296_, v___x_307_, v___x_308_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_345_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_345_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_345_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_345_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_box(0);
v___x_315_ = lean_unbox(v_a_310_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_del_object(v___x_312_);
lean_inc(v___x_307_);
lean_inc(v___x_308_);
v___x_316_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_296_, v___x_308_, v___x_307_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_331_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_331_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_331_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_331_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint8_t v___x_321_; 
v___x_321_ = lean_unbox(v_a_317_);
lean_dec(v_a_317_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
lean_del_object(v___x_319_);
lean_dec(v_a_310_);
v___x_322_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_add(v_a_297_, v___x_323_);
lean_dec(v_a_297_);
v_a_297_ = v___x_324_;
v_b_298_ = v___x_322_;
goto _start;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
lean_dec(v_a_297_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_a_310_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_314_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_327_);
v___x_329_ = v___x_319_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec(v_a_310_);
lean_dec(v_a_297_);
v_a_332_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_316_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_316_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec(v_a_297_);
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v_a_310_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_314_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_341_);
v___x_343_ = v___x_312_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_a_297_);
v_a_346_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_309_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_309_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(uint8_t v_mode_354_, lean_object* v_a_355_, lean_object* v_b_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_aFn_362_; lean_object* v_bFn_363_; lean_object* v___x_364_; 
v_aFn_362_ = l_Lean_Expr_getAppFn(v_a_355_);
v_bFn_363_ = l_Lean_Expr_getAppFn(v_b_356_);
lean_inc_ref(v_bFn_363_);
lean_inc_ref(v_aFn_362_);
v___x_364_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_354_, v_aFn_362_, v_bFn_363_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_463_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_463_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_463_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_463_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint8_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 1;
v___x_370_ = lean_unbox(v_a_365_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_del_object(v___x_367_);
lean_inc_ref(v_aFn_362_);
v___x_371_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_354_, v_bFn_363_, v_aFn_362_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; uint8_t v___x_373_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
v___x_373_ = lean_unbox(v_a_372_);
if (v___x_373_ == 0)
{
lean_object* v_dummy_374_; lean_object* v_nargs_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_nargs_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
lean_dec(v_a_365_);
v_dummy_374_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_375_ = l_Lean_Expr_getAppNumArgs(v_a_355_);
lean_inc(v_nargs_375_);
v___x_376_ = lean_mk_array(v_nargs_375_, v_dummy_374_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_sub(v_nargs_375_, v___x_377_);
lean_dec(v_nargs_375_);
v___x_379_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_355_, v___x_376_, v___x_378_);
v_nargs_380_ = l_Lean_Expr_getAppNumArgs(v_b_356_);
lean_inc(v_nargs_380_);
v___x_381_ = lean_mk_array(v_nargs_380_, v_dummy_374_);
v___x_382_ = lean_nat_sub(v_nargs_380_, v___x_377_);
lean_dec(v_nargs_380_);
v___x_383_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_b_356_, v___x_381_, v___x_382_);
v___x_384_ = lean_array_get_size(v___x_379_);
v___x_385_ = lean_array_get_size(v___x_383_);
v___x_386_ = lean_nat_dec_lt(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; 
v___x_387_ = lean_nat_dec_lt(v___x_385_, v___x_384_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec_ref_known(v___x_371_, 1);
v___x_388_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_362_, v___x_384_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = lean_array_get_size(v_a_389_);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_393_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_390_, v_a_389_, v___x_379_, v___x_383_, v_mode_354_, v___x_391_, v___x_392_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_389_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_425_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_425_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_425_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_425_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_fst_398_; 
v_fst_398_ = lean_ctor_get(v_a_394_, 0);
lean_inc(v_fst_398_);
lean_dec(v_a_394_);
if (lean_obj_tag(v_fst_398_) == 0)
{
lean_object* v___x_399_; 
lean_del_object(v___x_396_);
v___x_399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_384_, v___x_379_, v___x_383_, v_mode_354_, v___x_390_, v___x_392_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_379_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_412_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_412_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_412_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_412_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_fst_404_; 
v_fst_404_ = lean_ctor_get(v_a_400_, 0);
lean_inc(v_fst_404_);
lean_dec(v_a_400_);
if (lean_obj_tag(v_fst_404_) == 0)
{
lean_object* v___x_406_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v_a_372_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_372_);
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
lean_dec(v_a_372_);
v_val_408_ = lean_ctor_get(v_fst_404_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v_fst_404_, 1);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v_val_408_);
v___x_410_ = v___x_402_;
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
lean_dec(v_a_372_);
v_a_413_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_399_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_399_);
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
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_379_);
lean_dec(v_a_372_);
v_val_421_ = lean_ctor_get(v_fst_398_, 0);
lean_inc(v_val_421_);
lean_dec_ref_known(v_fst_398_, 1);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v_val_421_);
v___x_423_ = v___x_396_;
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
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_379_);
lean_dec(v_a_372_);
v_a_426_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_393_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_393_);
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
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_379_);
lean_dec(v_a_372_);
v_a_434_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_388_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_388_);
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
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_379_);
lean_dec(v_a_372_);
lean_dec_ref(v_aFn_362_);
return v___x_371_;
}
}
else
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_379_);
lean_dec(v_a_372_);
lean_dec_ref(v_aFn_362_);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_371_, 0);
lean_dec(v_unused_450_);
v___x_443_ = v___x_371_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_dec(v___x_371_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_box(v___x_369_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_a_372_);
lean_dec_ref(v_aFn_362_);
lean_dec_ref(v_b_356_);
lean_dec_ref(v_a_355_);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v___x_371_, 0);
lean_dec(v_unused_458_);
v___x_452_ = v___x_371_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_dec(v___x_371_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_a_365_);
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_365_);
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
else
{
lean_dec(v_a_365_);
lean_dec_ref(v_aFn_362_);
lean_dec_ref(v_b_356_);
lean_dec_ref(v_a_355_);
return v___x_371_;
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec(v_a_365_);
lean_dec_ref(v_bFn_363_);
lean_dec_ref(v_aFn_362_);
lean_dec_ref(v_b_356_);
lean_dec_ref(v_a_355_);
v___x_459_ = lean_box(v___x_369_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_459_);
v___x_461_ = v___x_367_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_dec_ref(v_bFn_363_);
lean_dec_ref(v_aFn_362_);
lean_dec_ref(v_b_356_);
lean_dec_ref(v_a_355_);
return v___x_364_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_467_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6));
v___x_468_ = lean_unsigned_to_nat(27u);
v___x_469_ = lean_unsigned_to_nat(152u);
v___x_470_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5));
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4));
v___x_472_ = l_mkPanicMessageWithDecl(v___x_471_, v___x_470_, v___x_469_, v___x_468_, v___x_467_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(uint8_t v_mode_473_, lean_object* v_a_474_, lean_object* v_b_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_d_482_; lean_object* v_e_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; 
switch(lean_obj_tag(v_a_474_))
{
case 0:
{
lean_object* v_deBruijnIndex_491_; lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_deBruijnIndex_491_ = lean_ctor_get(v_a_474_, 0);
lean_inc(v_deBruijnIndex_491_);
lean_dec_ref_known(v_a_474_, 1);
v___x_492_ = l_Lean_Expr_bvarIdx_x21(v_b_475_);
lean_dec_ref(v_b_475_);
v___x_493_ = lean_nat_dec_lt(v_deBruijnIndex_491_, v___x_492_);
lean_dec(v___x_492_);
lean_dec(v_deBruijnIndex_491_);
v___x_494_ = lean_box(v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
case 1:
{
lean_object* v_fvarId_496_; lean_object* v___x_497_; 
v_fvarId_496_ = lean_ctor_get(v_a_474_, 0);
lean_inc(v_fvarId_496_);
lean_dec_ref_known(v_a_474_, 1);
v___x_497_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_496_, v_a_476_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = l_Lean_Expr_fvarId_x21(v_b_475_);
lean_dec_ref(v_b_475_);
v___x_500_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_499_, v_a_476_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_523_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_523_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_523_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_523_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_515_; 
if (lean_obj_tag(v_a_498_) == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_521_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_520_);
v___y_515_ = v___x_521_;
goto v___jp_514_;
}
else
{
lean_object* v_val_522_; 
v_val_522_ = lean_ctor_get(v_a_498_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v_a_498_, 1);
v___y_515_ = v_val_522_;
goto v___jp_514_;
}
v___jp_505_:
{
lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_508_ = l_Lean_LocalDecl_index(v___y_507_);
lean_dec_ref(v___y_507_);
v___x_509_ = lean_nat_dec_lt(v___y_506_, v___x_508_);
lean_dec(v___x_508_);
lean_dec(v___y_506_);
v___x_510_ = lean_box(v___x_509_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_510_);
v___x_512_ = v___x_503_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
v___jp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_LocalDecl_index(v___y_515_);
lean_dec_ref(v___y_515_);
if (lean_obj_tag(v_a_501_) == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_518_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_517_);
v___y_506_ = v___x_516_;
v___y_507_ = v___x_518_;
goto v___jp_505_;
}
else
{
lean_object* v_val_519_; 
v_val_519_ = lean_ctor_get(v_a_501_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v_a_501_, 1);
v___y_506_ = v___x_516_;
v___y_507_ = v_val_519_;
goto v___jp_505_;
}
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_a_498_);
v_a_524_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_500_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_500_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v_b_475_);
v_a_532_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_497_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_497_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_mvarId_540_ = lean_ctor_get(v_a_474_, 0);
lean_inc(v_mvarId_540_);
lean_dec_ref_known(v_a_474_, 1);
v___x_541_ = l_Lean_Expr_mvarId_x21(v_b_475_);
lean_dec_ref(v_b_475_);
v___x_542_ = l_Lean_Name_lt(v_mvarId_540_, v___x_541_);
lean_dec(v___x_541_);
lean_dec(v_mvarId_540_);
v___x_543_ = lean_box(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
case 3:
{
lean_object* v_u_545_; lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_u_545_ = lean_ctor_get(v_a_474_, 0);
lean_inc(v_u_545_);
lean_dec_ref_known(v_a_474_, 1);
v___x_546_ = l_Lean_Expr_sortLevel_x21(v_b_475_);
lean_dec_ref(v_b_475_);
v___x_547_ = l_Lean_Level_normLt(v_u_545_, v___x_546_);
lean_dec(v___x_546_);
lean_dec(v_u_545_);
v___x_548_ = lean_box(v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
case 4:
{
lean_object* v_declName_550_; lean_object* v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_declName_550_ = lean_ctor_get(v_a_474_, 0);
lean_inc(v_declName_550_);
lean_dec_ref_known(v_a_474_, 2);
v___x_551_ = l_Lean_Expr_constName_x21(v_b_475_);
lean_dec_ref(v_b_475_);
v___x_552_ = l_Lean_Name_lt(v_declName_550_, v___x_551_);
lean_dec(v___x_551_);
lean_dec(v_declName_550_);
v___x_553_ = lean_box(v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
case 5:
{
lean_object* v___x_555_; 
v___x_555_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_473_, v_a_474_, v_b_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
return v___x_555_;
}
case 8:
{
lean_object* v_value_556_; lean_object* v_body_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_value_556_ = lean_ctor_get(v_a_474_, 2);
lean_inc_ref(v_value_556_);
v_body_557_ = lean_ctor_get(v_a_474_, 3);
lean_inc_ref(v_body_557_);
lean_dec_ref_known(v_a_474_, 4);
v___x_558_ = l_Lean_Expr_letValue_x21(v_b_475_);
v___x_559_ = l_Lean_Expr_letBody_x21(v_b_475_);
lean_dec_ref(v_b_475_);
v___x_560_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_473_, v_value_556_, v_body_557_, v___x_558_, v___x_559_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
return v___x_560_;
}
case 9:
{
lean_object* v_a_561_; lean_object* v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_a_561_ = lean_ctor_get(v_a_474_, 0);
lean_inc_ref(v_a_561_);
lean_dec_ref_known(v_a_474_, 1);
v___x_562_ = l_Lean_Expr_litValue_x21(v_b_475_);
lean_dec_ref(v_b_475_);
v___x_563_ = l_Lean_Literal_lt(v_a_561_, v___x_562_);
lean_dec_ref(v___x_562_);
lean_dec_ref(v_a_561_);
v___x_564_ = lean_box(v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
case 10:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref_known(v_a_474_, 2);
lean_dec_ref(v_b_475_);
v___x_566_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
v___x_567_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_566_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
return v___x_567_;
}
case 11:
{
lean_object* v_idx_568_; lean_object* v_struct_569_; lean_object* v___x_570_; uint8_t v___x_571_; uint8_t v___x_572_; 
v_idx_568_ = lean_ctor_get(v_a_474_, 1);
lean_inc(v_idx_568_);
v_struct_569_ = lean_ctor_get(v_a_474_, 2);
lean_inc_ref(v_struct_569_);
lean_dec_ref_known(v_a_474_, 3);
v___x_570_ = l_Lean_Expr_projIdx_x21(v_b_475_);
v___x_571_ = lean_nat_dec_eq(v_idx_568_, v___x_570_);
v___x_572_ = lean_bool_not(v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_570_);
lean_dec(v_idx_568_);
v___x_573_ = l_Lean_Expr_projExpr_x21(v_b_475_);
lean_dec_ref(v_b_475_);
v___x_574_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_473_, v_struct_569_, v___x_573_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
return v___x_574_;
}
else
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref(v_struct_569_);
lean_dec_ref(v_b_475_);
v___x_575_ = lean_nat_dec_lt(v_idx_568_, v___x_570_);
lean_dec(v___x_570_);
lean_dec(v_idx_568_);
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
default: 
{
lean_object* v_binderType_578_; lean_object* v_body_579_; 
v_binderType_578_ = lean_ctor_get(v_a_474_, 1);
lean_inc_ref(v_binderType_578_);
v_body_579_ = lean_ctor_get(v_a_474_, 2);
lean_inc_ref(v_body_579_);
lean_dec_ref(v_a_474_);
v_d_482_ = v_binderType_578_;
v_e_483_ = v_body_579_;
v___y_484_ = v_a_476_;
v___y_485_ = v_a_477_;
v___y_486_ = v_a_478_;
v___y_487_ = v_a_479_;
goto v___jp_481_;
}
}
v___jp_481_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = l_Lean_Expr_bindingDomain_x21(v_b_475_);
v___x_489_ = l_Lean_Expr_bindingBody_x21(v_b_475_);
lean_dec_ref(v_b_475_);
v___x_490_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_473_, v_d_482_, v_e_483_, v___x_488_, v___x_489_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(uint8_t v_mode_580_, lean_object* v_a_581_, lean_object* v_b_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0));
v___x_589_ = l_Lean_Core_checkSystem(v___x_588_, v_a_585_, v_a_586_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; 
lean_dec_ref_known(v___x_589_, 1);
lean_inc_ref(v_a_581_);
lean_inc_ref(v_b_582_);
v___x_590_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_580_, v_b_582_, v_a_581_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; uint8_t v___x_592_; uint8_t v___x_593_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
v___x_592_ = 1;
v___x_593_ = lean_unbox(v_a_591_);
if (v___x_593_ == 0)
{
uint8_t v___x_594_; uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_594_ = l_Lean_Expr_ctorWeight(v_b_582_);
v___x_595_ = l_Lean_Expr_ctorWeight(v_a_581_);
v___x_596_ = lean_uint8_dec_lt(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
lean_dec_ref_known(v___x_590_, 1);
lean_inc_ref(v_b_582_);
lean_inc_ref(v_a_581_);
v___x_597_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_580_, v_a_581_, v_b_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_613_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_613_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_613_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_613_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint8_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_unbox(v_a_598_);
lean_dec(v_a_598_);
v___x_603_ = lean_bool_not(v___x_602_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; 
lean_dec(v_a_591_);
v___x_604_ = lean_uint8_dec_lt(v___x_595_, v___x_594_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_del_object(v___x_600_);
v___x_605_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_580_, v_a_581_, v_b_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec_ref(v_b_582_);
lean_dec_ref(v_a_581_);
v___x_606_ = lean_box(v___x_592_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_606_);
v___x_608_ = v___x_600_;
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
else
{
lean_object* v___x_611_; 
lean_dec_ref(v_b_582_);
lean_dec_ref(v_a_581_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v_a_591_);
v___x_611_ = v___x_600_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_591_);
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
else
{
lean_dec(v_a_591_);
lean_dec_ref(v_b_582_);
lean_dec_ref(v_a_581_);
return v___x_597_;
}
}
else
{
lean_dec(v_a_591_);
lean_dec_ref(v_b_582_);
lean_dec_ref(v_a_581_);
return v___x_590_;
}
}
else
{
lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_a_591_);
lean_dec_ref(v_b_582_);
lean_dec_ref(v_a_581_);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_590_, 0);
lean_dec(v_unused_622_);
v___x_615_ = v___x_590_;
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
else
{
lean_dec(v___x_590_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_621_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_box(v___x_592_);
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
lean_dec_ref(v_b_582_);
lean_dec_ref(v_a_581_);
return v___x_590_;
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_b_582_);
lean_dec_ref(v_a_581_);
v_a_623_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_589_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_589_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(uint8_t v_mode_631_, lean_object* v_a_632_, lean_object* v_b_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_expr_eqv(v_a_632_, v_b_633_);
if (v___x_639_ == 0)
{
uint8_t v___x_640_; 
v___x_640_ = l_Lean_Expr_isMData(v_a_632_);
if (v___x_640_ == 0)
{
uint8_t v___x_641_; 
v___x_641_ = l_Lean_Expr_isMData(v_b_633_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_631_, v_a_632_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_631_, v_b_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_646_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_631_, v_a_643_, v_a_645_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v___x_646_;
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_a_643_);
v_a_647_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_644_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_644_);
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
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_b_633_);
v_a_655_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_642_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_642_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_Expr_mdataExpr_x21(v_b_633_);
lean_dec_ref(v_b_633_);
v_b_633_ = v___x_663_;
goto _start;
}
}
else
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Expr_mdataExpr_x21(v_a_632_);
lean_dec_ref(v_a_632_);
v_a_632_ = v___x_665_;
goto _start;
}
}
else
{
uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec_ref(v_b_633_);
lean_dec_ref(v_a_632_);
v___x_667_ = 0;
v___x_668_ = lean_box(v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(lean_object* v_upperBound_676_, lean_object* v_a_677_, lean_object* v_args_678_, uint8_t v_mode_679_, lean_object* v_b_680_, lean_object* v_a_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_a_689_; uint8_t v___x_693_; 
v___x_693_ = lean_nat_dec_lt(v_a_681_, v_upperBound_676_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
lean_dec(v_a_681_);
lean_dec_ref(v_b_680_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v_b_682_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v_isInstance_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
lean_dec_ref(v_b_682_);
v___x_695_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_696_ = lean_array_get_borrowed(v___x_695_, v_a_677_, v_a_681_);
v_isInstance_697_ = lean_ctor_get_uint8(v___x_696_, sizeof(void*)*1 + 4);
v___x_698_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_699_ = lean_bool_not(v_isInstance_697_);
if (v___x_699_ == 0)
{
v_a_689_ = v___x_698_;
goto v___jp_688_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_instInhabitedExpr;
v___x_701_ = lean_array_get_borrowed(v___x_700_, v_args_678_, v_a_681_);
lean_inc_ref(v_b_680_);
lean_inc(v___x_701_);
v___x_702_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_679_, v___x_701_, v_b_680_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_713_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_713_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
uint8_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_unbox(v_a_703_);
lean_dec(v_a_703_);
v___x_708_ = lean_bool_not(v___x_707_);
if (v___x_708_ == 0)
{
lean_del_object(v___x_705_);
v_a_689_ = v___x_698_;
goto v___jp_688_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec(v_a_681_);
lean_dec_ref(v_b_680_);
v___x_709_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__2));
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_709_);
v___x_711_ = v___x_705_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_a_681_);
lean_dec_ref(v_b_680_);
v_a_714_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_702_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_702_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
v___jp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_add(v_a_681_, v___x_690_);
lean_dec(v_a_681_);
lean_inc_ref(v_a_689_);
v_a_681_ = v___x_691_;
v_b_682_ = v_a_689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(lean_object* v_upperBound_722_, lean_object* v_args_723_, uint8_t v_mode_724_, lean_object* v_b_725_, lean_object* v_a_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = lean_nat_dec_lt(v_a_726_, v_upperBound_722_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_dec(v_a_726_);
lean_dec_ref(v_b_725_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v_b_727_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec_ref(v_b_727_);
v___x_735_ = lean_array_fget_borrowed(v_args_723_, v_a_726_);
lean_inc_ref(v_b_725_);
lean_inc(v___x_735_);
v___x_736_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_724_, v___x_735_, v_b_725_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_751_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_751_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_751_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_751_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
uint8_t v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_unbox(v_a_737_);
lean_dec(v_a_737_);
v___x_742_ = lean_bool_not(v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_del_object(v___x_739_);
v___x_743_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_a_726_, v___x_744_);
lean_dec(v_a_726_);
v_a_726_ = v___x_745_;
v_b_727_ = v___x_743_;
goto _start;
}
else
{
lean_object* v___x_747_; lean_object* v___x_749_; 
lean_dec(v_a_726_);
lean_dec_ref(v_b_725_);
v___x_747_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__2));
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_747_);
v___x_749_ = v___x_739_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
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
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_726_);
lean_dec_ref(v_b_725_);
v_a_752_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_736_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_736_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(uint8_t v_mode_760_, lean_object* v_b_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
if (lean_obj_tag(v_x_762_) == 5)
{
lean_object* v_fn_770_; lean_object* v_arg_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_fn_770_ = lean_ctor_get(v_x_762_, 0);
lean_inc_ref(v_fn_770_);
v_arg_771_ = lean_ctor_get(v_x_762_, 1);
lean_inc_ref(v_arg_771_);
lean_dec_ref_known(v_x_762_, 2);
v___x_772_ = lean_array_set(v_x_763_, v_x_764_, v_arg_771_);
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_sub(v_x_764_, v___x_773_);
lean_dec(v_x_764_);
v_x_762_ = v_fn_770_;
v_x_763_ = v___x_772_;
v_x_764_ = v___x_774_;
goto _start;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec(v_x_764_);
v___x_776_ = lean_array_get_size(v_x_763_);
v___x_777_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_x_762_, v___x_776_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = lean_array_get_size(v_a_778_);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
lean_inc_ref(v_b_761_);
v___x_782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_779_, v_a_778_, v_x_763_, v_mode_760_, v_b_761_, v___x_780_, v___x_781_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v_a_778_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_816_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_816_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_816_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_816_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_fst_787_; 
v_fst_787_ = lean_ctor_get(v_a_783_, 0);
lean_inc(v_fst_787_);
lean_dec(v_a_783_);
if (lean_obj_tag(v_fst_787_) == 0)
{
lean_object* v___x_788_; 
lean_del_object(v___x_785_);
v___x_788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_776_, v_x_763_, v_mode_760_, v_b_761_, v___x_779_, v___x_781_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec_ref(v_x_763_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_803_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_803_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_803_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_803_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_fst_793_; 
v_fst_793_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_fst_793_);
lean_dec(v_a_789_);
if (lean_obj_tag(v_fst_793_) == 0)
{
uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_794_ = 1;
v___x_795_ = lean_box(v___x_794_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_795_);
v___x_797_ = v___x_791_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
else
{
lean_object* v_val_799_; lean_object* v___x_801_; 
v_val_799_ = lean_ctor_get(v_fst_793_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v_fst_793_, 1);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_val_799_);
v___x_801_ = v___x_791_;
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
v_a_804_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_788_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_788_);
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
lean_object* v_val_812_; lean_object* v___x_814_; 
lean_dec_ref(v_x_763_);
lean_dec_ref(v_b_761_);
v_val_812_ = lean_ctor_get(v_fst_787_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v_fst_787_, 1);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_val_812_);
v___x_814_ = v___x_785_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_val_812_);
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
lean_dec_ref(v_x_763_);
lean_dec_ref(v_b_761_);
v_a_817_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_782_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_782_);
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
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v_x_763_);
lean_dec_ref(v_b_761_);
v_a_825_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_777_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_777_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(uint8_t v_mode_833_, lean_object* v_a_834_, lean_object* v_b_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_d_842_; lean_object* v_e_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; 
switch(lean_obj_tag(v_a_834_))
{
case 11:
{
lean_object* v_struct_852_; lean_object* v___x_853_; 
v_struct_852_ = lean_ctor_get(v_a_834_, 2);
lean_inc_ref(v_struct_852_);
lean_dec_ref_known(v_a_834_, 3);
v___x_853_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_833_, v_struct_852_, v_b_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v___x_853_;
}
case 5:
{
lean_object* v_dummy_854_; lean_object* v_nargs_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_dummy_854_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_855_ = l_Lean_Expr_getAppNumArgs(v_a_834_);
lean_inc(v_nargs_855_);
v___x_856_ = lean_mk_array(v_nargs_855_, v_dummy_854_);
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_nat_sub(v_nargs_855_, v___x_857_);
lean_dec(v_nargs_855_);
v___x_859_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_833_, v_b_835_, v_a_834_, v___x_856_, v___x_858_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v___x_859_;
}
case 6:
{
lean_object* v_binderType_860_; lean_object* v_body_861_; 
v_binderType_860_ = lean_ctor_get(v_a_834_, 1);
lean_inc_ref(v_binderType_860_);
v_body_861_ = lean_ctor_get(v_a_834_, 2);
lean_inc_ref(v_body_861_);
lean_dec_ref_known(v_a_834_, 3);
v_d_842_ = v_binderType_860_;
v_e_843_ = v_body_861_;
v___y_844_ = v_a_836_;
v___y_845_ = v_a_837_;
v___y_846_ = v_a_838_;
v___y_847_ = v_a_839_;
goto v___jp_841_;
}
case 7:
{
lean_object* v_binderType_862_; lean_object* v_body_863_; 
v_binderType_862_ = lean_ctor_get(v_a_834_, 1);
lean_inc_ref(v_binderType_862_);
v_body_863_ = lean_ctor_get(v_a_834_, 2);
lean_inc_ref(v_body_863_);
lean_dec_ref_known(v_a_834_, 3);
v_d_842_ = v_binderType_862_;
v_e_843_ = v_body_863_;
v___y_844_ = v_a_836_;
v___y_845_ = v_a_837_;
v___y_846_ = v_a_838_;
v___y_847_ = v_a_839_;
goto v___jp_841_;
}
case 8:
{
lean_object* v_value_864_; lean_object* v_body_865_; lean_object* v___x_866_; 
v_value_864_ = lean_ctor_get(v_a_834_, 2);
lean_inc_ref(v_value_864_);
v_body_865_ = lean_ctor_get(v_a_834_, 3);
lean_inc_ref(v_body_865_);
lean_dec_ref_known(v_a_834_, 4);
lean_inc_ref(v_b_835_);
v___x_866_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_833_, v_value_864_, v_b_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; uint8_t v___x_868_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
v___x_868_ = lean_unbox(v_a_867_);
lean_dec(v_a_867_);
if (v___x_868_ == 0)
{
lean_dec_ref(v_body_865_);
lean_dec_ref(v_b_835_);
return v___x_866_;
}
else
{
lean_object* v___x_869_; 
lean_dec_ref_known(v___x_866_, 1);
v___x_869_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_833_, v_body_865_, v_b_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v___x_869_;
}
}
else
{
lean_dec_ref(v_body_865_);
lean_dec_ref(v_b_835_);
return v___x_866_;
}
}
default: 
{
uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v_b_835_);
lean_dec_ref(v_a_834_);
v___x_870_ = 1;
v___x_871_ = lean_box(v___x_870_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
v___jp_841_:
{
lean_object* v___x_848_; 
lean_inc_ref(v_b_835_);
v___x_848_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_833_, v_d_842_, v_b_835_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; uint8_t v___x_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
v___x_850_ = lean_unbox(v_a_849_);
lean_dec(v_a_849_);
if (v___x_850_ == 0)
{
lean_dec_ref(v_e_843_);
lean_dec_ref(v_b_835_);
return v___x_848_;
}
else
{
lean_object* v___x_851_; 
lean_dec_ref_known(v___x_848_, 1);
v___x_851_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_833_, v_e_843_, v_b_835_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
return v___x_851_;
}
}
else
{
lean_dec_ref(v_e_843_);
lean_dec_ref(v_b_835_);
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(uint8_t v_mode_873_, lean_object* v_a_874_, lean_object* v_b_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_873_, v_a_874_, v_b_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_892_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_892_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
uint8_t v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_886_ = lean_unbox(v_a_882_);
lean_dec(v_a_882_);
v___x_887_ = lean_bool_not(v___x_886_);
v___x_888_ = lean_box(v___x_887_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_888_);
v___x_890_ = v___x_884_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(lean_object* v_mode_893_, lean_object* v_a_894_, lean_object* v_b_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
uint8_t v_mode_boxed_901_; lean_object* v_res_902_; 
v_mode_boxed_901_ = lean_unbox(v_mode_893_);
v_res_902_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_boxed_901_, v_a_894_, v_b_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(lean_object* v_mode_903_, lean_object* v_a_u2081_904_, lean_object* v_a_u2082_905_, lean_object* v_b_u2081_906_, lean_object* v_b_u2082_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
uint8_t v_mode_boxed_913_; lean_object* v_res_914_; 
v_mode_boxed_913_ = lean_unbox(v_mode_903_);
v_res_914_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_boxed_913_, v_a_u2081_904_, v_a_u2082_905_, v_b_u2081_906_, v_b_u2082_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(lean_object* v_upperBound_915_, lean_object* v_args_916_, lean_object* v_mode_917_, lean_object* v_b_918_, lean_object* v_a_919_, lean_object* v_b_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v_mode_boxed_926_; lean_object* v_res_927_; 
v_mode_boxed_926_ = lean_unbox(v_mode_917_);
v_res_927_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_915_, v_args_916_, v_mode_boxed_926_, v_b_918_, v_a_919_, v_b_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec_ref(v_args_916_);
lean_dec(v_upperBound_915_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object* v_mode_928_, lean_object* v_a_929_, lean_object* v_b_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
uint8_t v_mode_boxed_936_; lean_object* v_res_937_; 
v_mode_boxed_936_ = lean_unbox(v_mode_928_);
v_res_937_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_boxed_936_, v_a_929_, v_b_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object* v_mode_938_, lean_object* v_a_939_, lean_object* v_b_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
uint8_t v_mode_boxed_946_; lean_object* v_res_947_; 
v_mode_boxed_946_ = lean_unbox(v_mode_938_);
v_res_947_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_boxed_946_, v_a_939_, v_b_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object* v_upperBound_948_, lean_object* v_a_949_, lean_object* v_args_950_, lean_object* v_mode_951_, lean_object* v_b_952_, lean_object* v_a_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v_mode_boxed_960_; lean_object* v_res_961_; 
v_mode_boxed_960_ = lean_unbox(v_mode_951_);
v_res_961_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_948_, v_a_949_, v_args_950_, v_mode_boxed_960_, v_b_952_, v_a_953_, v_b_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_args_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_upperBound_948_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(lean_object* v_upperBound_962_, lean_object* v___x_963_, lean_object* v___x_964_, lean_object* v_mode_965_, lean_object* v_a_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v_mode_boxed_973_; lean_object* v_res_974_; 
v_mode_boxed_973_ = lean_unbox(v_mode_965_);
v_res_974_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_962_, v___x_963_, v___x_964_, v_mode_boxed_973_, v_a_966_, v_b_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v___x_964_);
lean_dec_ref(v___x_963_);
lean_dec(v_upperBound_962_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object* v_mode_975_, lean_object* v_a_976_, lean_object* v_b_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
uint8_t v_mode_boxed_983_; lean_object* v_res_984_; 
v_mode_boxed_983_ = lean_unbox(v_mode_975_);
v_res_984_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_boxed_983_, v_a_976_, v_b_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(lean_object* v_mode_985_, lean_object* v_b_986_, lean_object* v_x_987_, lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_mode_boxed_995_; lean_object* v_res_996_; 
v_mode_boxed_995_ = lean_unbox(v_mode_985_);
v_res_996_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_995_, v_b_986_, v_x_987_, v_x_988_, v_x_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(lean_object* v_upperBound_997_, lean_object* v_a_998_, lean_object* v___x_999_, lean_object* v___x_1000_, lean_object* v_mode_1001_, lean_object* v_a_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v_mode_boxed_1009_; lean_object* v_res_1010_; 
v_mode_boxed_1009_ = lean_unbox(v_mode_1001_);
v_res_1010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_997_, v_a_998_, v___x_999_, v___x_1000_, v_mode_boxed_1009_, v_a_1002_, v_b_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v___x_1000_);
lean_dec_ref(v___x_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_upperBound_997_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(lean_object* v_mode_1011_, lean_object* v_a_1012_, lean_object* v_b_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_mode_boxed_1019_; lean_object* v_res_1020_; 
v_mode_boxed_1019_ = lean_unbox(v_mode_1011_);
v_res_1020_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_boxed_1019_, v_a_1012_, v_b_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(lean_object* v_mode_1021_, lean_object* v_a_1022_, lean_object* v_b_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
uint8_t v_mode_boxed_1029_; lean_object* v_res_1030_; 
v_mode_boxed_1029_ = lean_unbox(v_mode_1021_);
v_res_1030_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_boxed_1029_, v_a_1022_, v_b_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(lean_object* v_upperBound_1031_, lean_object* v___x_1032_, lean_object* v___x_1033_, uint8_t v_mode_1034_, lean_object* v_inst_1035_, lean_object* v_R_1036_, lean_object* v_a_1037_, lean_object* v_b_1038_, lean_object* v_c_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_1031_, v___x_1032_, v___x_1033_, v_mode_1034_, v_a_1037_, v_b_1038_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(lean_object* v_upperBound_1046_, lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v_mode_1049_, lean_object* v_inst_1050_, lean_object* v_R_1051_, lean_object* v_a_1052_, lean_object* v_b_1053_, lean_object* v_c_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v_mode_boxed_1060_; lean_object* v_res_1061_; 
v_mode_boxed_1060_ = lean_unbox(v_mode_1049_);
v_res_1061_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_1046_, v___x_1047_, v___x_1048_, v_mode_boxed_1060_, v_inst_1050_, v_R_1051_, v_a_1052_, v_b_1053_, v_c_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v___x_1047_);
lean_dec(v_upperBound_1046_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(lean_object* v_upperBound_1062_, lean_object* v_a_1063_, lean_object* v___x_1064_, lean_object* v___x_1065_, uint8_t v_mode_1066_, lean_object* v_inst_1067_, lean_object* v_R_1068_, lean_object* v_a_1069_, lean_object* v_b_1070_, lean_object* v_c_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_1062_, v_a_1063_, v___x_1064_, v___x_1065_, v_mode_1066_, v_a_1069_, v_b_1070_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(lean_object* v_upperBound_1078_, lean_object* v_a_1079_, lean_object* v___x_1080_, lean_object* v___x_1081_, lean_object* v_mode_1082_, lean_object* v_inst_1083_, lean_object* v_R_1084_, lean_object* v_a_1085_, lean_object* v_b_1086_, lean_object* v_c_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v_mode_boxed_1093_; lean_object* v_res_1094_; 
v_mode_boxed_1093_ = lean_unbox(v_mode_1082_);
v_res_1094_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_1078_, v_a_1079_, v___x_1080_, v___x_1081_, v_mode_boxed_1093_, v_inst_1083_, v_R_1084_, v_a_1085_, v_b_1086_, v_c_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec_ref(v___x_1081_);
lean_dec_ref(v___x_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_upperBound_1078_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(lean_object* v_upperBound_1095_, lean_object* v_args_1096_, uint8_t v_mode_1097_, lean_object* v_b_1098_, lean_object* v_inst_1099_, lean_object* v_R_1100_, lean_object* v_a_1101_, lean_object* v_b_1102_, lean_object* v_c_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_1095_, v_args_1096_, v_mode_1097_, v_b_1098_, v_a_1101_, v_b_1102_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(lean_object* v_upperBound_1110_, lean_object* v_args_1111_, lean_object* v_mode_1112_, lean_object* v_b_1113_, lean_object* v_inst_1114_, lean_object* v_R_1115_, lean_object* v_a_1116_, lean_object* v_b_1117_, lean_object* v_c_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v_mode_boxed_1124_; lean_object* v_res_1125_; 
v_mode_boxed_1124_ = lean_unbox(v_mode_1112_);
v_res_1125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_1110_, v_args_1111_, v_mode_boxed_1124_, v_b_1113_, v_inst_1114_, v_R_1115_, v_a_1116_, v_b_1117_, v_c_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec_ref(v_args_1111_);
lean_dec(v_upperBound_1110_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(lean_object* v_upperBound_1126_, lean_object* v_a_1127_, lean_object* v_args_1128_, uint8_t v_mode_1129_, lean_object* v_b_1130_, lean_object* v_inst_1131_, lean_object* v_R_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_, lean_object* v_c_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_1126_, v_a_1127_, v_args_1128_, v_mode_1129_, v_b_1130_, v_a_1133_, v_b_1134_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(lean_object* v_upperBound_1142_, lean_object* v_a_1143_, lean_object* v_args_1144_, lean_object* v_mode_1145_, lean_object* v_b_1146_, lean_object* v_inst_1147_, lean_object* v_R_1148_, lean_object* v_a_1149_, lean_object* v_b_1150_, lean_object* v_c_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v_mode_boxed_1157_; lean_object* v_res_1158_; 
v_mode_boxed_1157_ = lean_unbox(v_mode_1145_);
v_res_1158_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_1142_, v_a_1143_, v_args_1144_, v_mode_boxed_1157_, v_b_1146_, v_inst_1147_, v_R_1148_, v_a_1149_, v_b_1150_, v_c_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec_ref(v_args_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_upperBound_1142_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main(lean_object* v_a_1159_, lean_object* v_b_1160_, uint8_t v_mode_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1161_, v_a_1159_, v_b_1160_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main___boxed(lean_object* v_a_1168_, lean_object* v_b_1169_, lean_object* v_mode_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
uint8_t v_mode_boxed_1176_; lean_object* v_res_1177_; 
v_mode_boxed_1176_ = lean_unbox(v_mode_1170_);
v_res_1177_ = l_Lean_Meta_ACLt_main(v_a_1168_, v_b_1169_, v_mode_boxed_1176_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt(lean_object* v_a_1178_, lean_object* v_b_1179_, uint8_t v_mode_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1180_, v_a_1178_, v_b_1179_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt___boxed(lean_object* v_a_1187_, lean_object* v_b_1188_, lean_object* v_mode_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
uint8_t v_mode_boxed_1195_; lean_object* v_res_1196_; 
v_mode_boxed_1195_ = lean_unbox(v_mode_1189_);
v_res_1196_ = l_Lean_Meta_acLt(v_a_1187_, v_b_1188_, v_mode_boxed_1195_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
return v_res_1196_;
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
