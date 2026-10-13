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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_ctorWeight(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorWeight___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl(uint8_t v_x_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_box(v_x_17_);
v___x_19_ = lean_obj_tag_nat(v___x_18_);
lean_dec(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl___boxed(lean_object* v_x_20_){
_start:
{
uint8_t v_x_4__boxed_21_; lean_object* v_res_22_; 
v_x_4__boxed_21_ = lean_unbox(v_x_20_);
v_res_22_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl(v_x_4__boxed_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(lean_object* v_k_23_){
_start:
{
lean_inc(v_k_23_);
return v_k_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg___boxed(lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(v_k_24_);
lean_dec(v_k_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim(lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_inc(v_k_30_);
return v_k_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___boxed(lean_object* v_motive_31_, lean_object* v_ctorIdx_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_k_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim(v_motive_31_, v_ctorIdx_32_, v_t_boxed_36_, v_h_34_, v_k_35_);
lean_dec(v_k_35_);
lean_dec(v_ctorIdx_32_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(lean_object* v_reduce_38_){
_start:
{
lean_inc(v_reduce_38_);
return v_reduce_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg___boxed(lean_object* v_reduce_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(v_reduce_39_);
lean_dec(v_reduce_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_reduce_44_){
_start:
{
lean_inc(v_reduce_44_);
return v_reduce_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___boxed(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_reduce_48_){
_start:
{
uint8_t v_t_boxed_49_; lean_object* v_res_50_; 
v_t_boxed_49_ = lean_unbox(v_t_46_);
v_res_50_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim(v_motive_45_, v_t_boxed_49_, v_h_47_, v_reduce_48_);
lean_dec(v_reduce_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(lean_object* v_reduceSimpleOnly_51_){
_start:
{
lean_inc(v_reduceSimpleOnly_51_);
return v_reduceSimpleOnly_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg___boxed(lean_object* v_reduceSimpleOnly_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(v_reduceSimpleOnly_52_);
lean_dec(v_reduceSimpleOnly_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(lean_object* v_motive_54_, uint8_t v_t_55_, lean_object* v_h_56_, lean_object* v_reduceSimpleOnly_57_){
_start:
{
lean_inc(v_reduceSimpleOnly_57_);
return v_reduceSimpleOnly_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___boxed(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_reduceSimpleOnly_61_){
_start:
{
uint8_t v_t_boxed_62_; lean_object* v_res_63_; 
v_t_boxed_62_ = lean_unbox(v_t_59_);
v_res_63_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(v_motive_58_, v_t_boxed_62_, v_h_60_, v_reduceSimpleOnly_61_);
lean_dec(v_reduceSimpleOnly_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(lean_object* v_none_64_){
_start:
{
lean_inc(v_none_64_);
return v_none_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg___boxed(lean_object* v_none_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(v_none_65_);
lean_dec(v_none_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim(lean_object* v_motive_67_, uint8_t v_t_68_, lean_object* v_h_69_, lean_object* v_none_70_){
_start:
{
lean_inc(v_none_70_);
return v_none_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___boxed(lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_none_74_){
_start:
{
uint8_t v_t_boxed_75_; lean_object* v_res_76_; 
v_t_boxed_75_ = lean_unbox(v_t_72_);
v_res_76_ = l_Lean_Meta_ACLt_ReduceMode_none_elim(v_motive_71_, v_t_boxed_75_, v_h_73_, v_none_74_);
lean_dec(v_none_74_);
return v_res_76_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__0));
v___x_84_ = l_Lean_Meta_Config_toConfigWithKey(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config___closed__1);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(uint8_t v_mode_86_, lean_object* v_e_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = l_Lean_Expr_hasLooseBVars(v_e_87_);
if (v___x_93_ == 0)
{
switch(v_mode_86_)
{
case 0:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_Meta_DiscrTree_reduce(v_e_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
return v___x_94_;
}
case 1:
{
lean_object* v___x_95_; lean_object* v_config_96_; uint8_t v_trackZetaDelta_97_; lean_object* v_zetaDeltaSet_98_; lean_object* v_lctx_99_; lean_object* v_localInstances_100_; lean_object* v_defEqCtx_x3f_101_; lean_object* v_synthPendingDepth_102_; lean_object* v_customCanUnfoldPredicate_x3f_103_; uint8_t v_univApprox_104_; uint8_t v_inTypeClassResolution_105_; uint8_t v_cacheInferType_106_; uint64_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_95_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config;
v_config_96_ = lean_ctor_get(v___x_95_, 0);
v_trackZetaDelta_97_ = lean_ctor_get_uint8(v_a_88_, sizeof(void*)*7);
v_zetaDeltaSet_98_ = lean_ctor_get(v_a_88_, 1);
v_lctx_99_ = lean_ctor_get(v_a_88_, 2);
v_localInstances_100_ = lean_ctor_get(v_a_88_, 3);
v_defEqCtx_x3f_101_ = lean_ctor_get(v_a_88_, 4);
v_synthPendingDepth_102_ = lean_ctor_get(v_a_88_, 5);
v_customCanUnfoldPredicate_x3f_103_ = lean_ctor_get(v_a_88_, 6);
v_univApprox_104_ = lean_ctor_get_uint8(v_a_88_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_105_ = lean_ctor_get_uint8(v_a_88_, sizeof(void*)*7 + 2);
v_cacheInferType_106_ = lean_ctor_get_uint8(v_a_88_, sizeof(void*)*7 + 3);
v___x_107_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_96_);
lean_inc_ref(v_config_96_);
v___x_108_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_108_, 0, v_config_96_);
lean_ctor_set_uint64(v___x_108_, sizeof(void*)*1, v___x_107_);
lean_inc(v_customCanUnfoldPredicate_x3f_103_);
lean_inc(v_synthPendingDepth_102_);
lean_inc(v_defEqCtx_x3f_101_);
lean_inc_ref(v_localInstances_100_);
lean_inc_ref(v_lctx_99_);
lean_inc(v_zetaDeltaSet_98_);
v___x_109_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_zetaDeltaSet_98_);
lean_ctor_set(v___x_109_, 2, v_lctx_99_);
lean_ctor_set(v___x_109_, 3, v_localInstances_100_);
lean_ctor_set(v___x_109_, 4, v_defEqCtx_x3f_101_);
lean_ctor_set(v___x_109_, 5, v_synthPendingDepth_102_);
lean_ctor_set(v___x_109_, 6, v_customCanUnfoldPredicate_x3f_103_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*7, v_trackZetaDelta_97_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*7 + 1, v_univApprox_104_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*7 + 2, v_inTypeClassResolution_105_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*7 + 3, v_cacheInferType_106_);
v___x_110_ = l_Lean_Meta_DiscrTree_reduce(v_e_87_, v___x_109_, v_a_89_, v_a_90_, v_a_91_);
lean_dec_ref_known(v___x_109_, 7);
return v___x_110_;
}
default: 
{
lean_object* v___x_111_; 
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v_e_87_);
return v___x_111_;
}
}
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v_e_87_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce___boxed(lean_object* v_mode_113_, lean_object* v_e_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
uint8_t v_mode_boxed_120_; lean_object* v_res_121_; 
v_mode_boxed_120_ = lean_unbox(v_mode_113_);
v_res_121_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_boxed_120_, v_e_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(lean_object* v_f_124_, lean_object* v_numArgs_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_Expr_hasLooseBVars(v_f_124_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Meta_getFunInfoNArgs(v_f_124_, v_numArgs_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_141_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_paramInfo_137_; lean_object* v___x_139_; 
v_paramInfo_137_ = lean_ctor_get(v_a_133_, 0);
lean_inc_ref(v_paramInfo_137_);
lean_dec(v_a_133_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v_paramInfo_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_paramInfo_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_132_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_132_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v_numArgs_125_);
lean_dec_ref(v_f_124_);
v___x_150_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0));
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___boxed(lean_object* v_f_152_, lean_object* v_numArgs_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_f_152_, v_numArgs_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(lean_object* v_msg_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___f_167_; lean_object* v___x_12973__overap_168_; lean_object* v___x_169_; 
v___f_167_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0));
v___x_12973__overap_168_ = lean_panic_fn_borrowed(v___f_167_, v_msg_161_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
v___x_169_ = lean_apply_5(v___x_12973__overap_168_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, lean_box(0));
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(lean_object* v_msg_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = l_Lean_instInhabitedLocalDecl_default;
v___x_179_ = lean_panic_fn_borrowed(v___x_178_, v_msg_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(uint8_t v_mode_181_, lean_object* v_a_u2081_182_, lean_object* v_a_u2082_183_, lean_object* v_b_u2081_184_, lean_object* v_b_u2082_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_191_; 
lean_inc_ref(v_b_u2081_184_);
lean_inc_ref(v_a_u2081_182_);
v___x_191_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_181_, v_a_u2081_182_, v_b_u2081_184_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; uint8_t v___x_193_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v___x_193_ = lean_unbox(v_a_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_inc(v_a_192_);
lean_dec_ref_known(v___x_191_, 1);
v___x_194_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_181_, v_b_u2081_184_, v_a_u2081_182_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_204_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_204_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
uint8_t v___x_199_; 
v___x_199_ = lean_unbox(v_a_195_);
lean_dec(v_a_195_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
lean_del_object(v___x_197_);
lean_dec(v_a_192_);
v___x_200_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_181_, v_a_u2082_183_, v_b_u2082_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
return v___x_200_;
}
else
{
lean_object* v___x_202_; 
lean_dec_ref(v_b_u2082_185_);
lean_dec_ref(v_a_u2082_183_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v_a_192_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_192_);
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
lean_dec(v_a_192_);
lean_dec_ref(v_b_u2082_185_);
lean_dec_ref(v_a_u2082_183_);
return v___x_194_;
}
}
else
{
lean_dec_ref(v_b_u2082_185_);
lean_dec_ref(v_b_u2081_184_);
lean_dec_ref(v_a_u2082_183_);
lean_dec_ref(v_a_u2081_182_);
return v___x_191_;
}
}
else
{
lean_dec_ref(v_b_u2082_185_);
lean_dec_ref(v_b_u2081_184_);
lean_dec_ref(v_a_u2082_183_);
lean_dec_ref(v_a_u2081_182_);
return v___x_191_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2));
v___x_209_ = lean_unsigned_to_nat(14u);
v___x_210_ = lean_unsigned_to_nat(22u);
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1));
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0));
v___x_213_ = l_mkPanicMessageWithDecl(v___x_212_, v___x_211_, v___x_210_, v___x_209_, v___x_208_);
return v___x_213_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0(void){
_start:
{
lean_object* v___x_214_; lean_object* v_dummy_215_; 
v___x_214_ = lean_box(0);
v_dummy_215_ = l_Lean_Expr_sort___override(v___x_214_);
return v_dummy_215_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(lean_object* v_upperBound_219_, lean_object* v_a_220_, lean_object* v___x_221_, lean_object* v___x_222_, uint8_t v_mode_223_, lean_object* v_a_224_, lean_object* v_b_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_a_232_; uint8_t v___x_236_; 
v___x_236_ = lean_nat_dec_lt(v_a_224_, v_upperBound_219_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v_a_224_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v_b_225_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v_isInstance_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec_ref(v_b_225_);
v___x_238_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_239_ = lean_array_get_borrowed(v___x_238_, v_a_220_, v_a_224_);
v_isInstance_240_ = lean_ctor_get_uint8(v___x_239_, sizeof(void*)*1 + 4);
v___x_241_ = lean_box(0);
v___x_242_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_240_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = l_Lean_instInhabitedExpr;
v___x_244_ = lean_array_get_borrowed(v___x_243_, v___x_221_, v_a_224_);
v___x_245_ = lean_array_get_borrowed(v___x_243_, v___x_222_, v_a_224_);
lean_inc(v___x_245_);
lean_inc(v___x_244_);
v___x_246_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_223_, v___x_244_, v___x_245_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_278_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_278_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_278_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_278_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
uint8_t v___x_251_; 
v___x_251_ = lean_unbox(v_a_247_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_del_object(v___x_249_);
lean_inc(v___x_244_);
lean_inc(v___x_245_);
v___x_252_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_223_, v___x_245_, v___x_244_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_263_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_263_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_263_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_263_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; 
v___x_257_ = lean_unbox(v_a_253_);
lean_dec(v_a_253_);
if (v___x_257_ == 0)
{
lean_del_object(v___x_255_);
lean_dec(v_a_247_);
v_a_232_ = v___x_242_;
goto v___jp_231_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
lean_dec(v_a_224_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_a_247_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_241_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_259_);
v___x_261_ = v___x_255_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_a_247_);
lean_dec(v_a_224_);
v_a_264_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_252_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_252_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec(v_a_247_);
lean_dec(v_a_224_);
v___x_272_ = lean_box(v___x_236_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_241_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_274_);
v___x_276_ = v___x_249_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
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
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec(v_a_224_);
v_a_279_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_246_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_246_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
v_a_232_ = v___x_242_;
goto v___jp_231_;
}
}
v___jp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_a_224_, v___x_233_);
lean_dec(v_a_224_);
lean_inc_ref(v_a_232_);
v_a_224_ = v___x_234_;
v_b_225_ = v_a_232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(lean_object* v_upperBound_287_, lean_object* v___x_288_, lean_object* v___x_289_, uint8_t v_mode_290_, lean_object* v_a_291_, lean_object* v_b_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = lean_nat_dec_lt(v_a_291_, v_upperBound_287_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec(v_a_291_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v_b_292_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_b_292_);
v___x_300_ = l_Lean_instInhabitedExpr;
v___x_301_ = lean_box(0);
v___x_302_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_303_ = lean_array_get_borrowed(v___x_300_, v___x_288_, v_a_291_);
v___x_304_ = lean_array_get_borrowed(v___x_300_, v___x_289_, v_a_291_);
lean_inc(v___x_304_);
lean_inc(v___x_303_);
v___x_305_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_290_, v___x_303_, v___x_304_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_340_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_340_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_340_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_340_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
uint8_t v___x_310_; 
v___x_310_ = lean_unbox(v_a_306_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_del_object(v___x_308_);
lean_inc(v___x_303_);
lean_inc(v___x_304_);
v___x_311_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_290_, v___x_304_, v___x_303_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_325_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_325_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_325_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_325_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint8_t v___x_316_; 
v___x_316_ = lean_unbox(v_a_312_);
lean_dec(v_a_312_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_del_object(v___x_314_);
lean_dec(v_a_306_);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_a_291_, v___x_317_);
lean_dec(v_a_291_);
v_a_291_ = v___x_318_;
v_b_292_ = v___x_302_;
goto _start;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
lean_dec(v_a_291_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v_a_306_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_301_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_321_);
v___x_323_ = v___x_314_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_a_306_);
lean_dec(v_a_291_);
v_a_326_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_311_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_311_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_dec(v_a_306_);
lean_dec(v_a_291_);
v___x_334_ = lean_box(v___x_298_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_301_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_336_);
v___x_338_ = v___x_308_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_a_291_);
v_a_341_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_305_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_305_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(uint8_t v_mode_349_, lean_object* v_a_350_, lean_object* v_b_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_aFn_357_; lean_object* v_bFn_358_; lean_object* v___x_359_; 
v_aFn_357_ = l_Lean_Expr_getAppFn(v_a_350_);
v_bFn_358_ = l_Lean_Expr_getAppFn(v_b_351_);
lean_inc_ref(v_bFn_358_);
lean_inc_ref(v_aFn_357_);
v___x_359_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_349_, v_aFn_357_, v_bFn_358_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_457_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_457_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_457_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_457_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
uint8_t v___x_364_; uint8_t v___x_365_; 
v___x_364_ = 1;
v___x_365_ = lean_unbox(v_a_360_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_del_object(v___x_362_);
lean_inc_ref(v_aFn_357_);
v___x_366_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_349_, v_bFn_358_, v_aFn_357_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_452_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_452_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_452_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_452_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
uint8_t v___x_371_; 
v___x_371_ = lean_unbox(v_a_367_);
lean_dec(v_a_367_);
if (v___x_371_ == 0)
{
lean_object* v_dummy_372_; lean_object* v_nargs_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_nargs_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
lean_dec(v_a_360_);
v_dummy_372_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_373_ = l_Lean_Expr_getAppNumArgs(v_a_350_);
lean_inc(v_nargs_373_);
v___x_374_ = lean_mk_array(v_nargs_373_, v_dummy_372_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_sub(v_nargs_373_, v___x_375_);
lean_dec(v_nargs_373_);
v___x_377_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_350_, v___x_374_, v___x_376_);
v_nargs_378_ = l_Lean_Expr_getAppNumArgs(v_b_351_);
lean_inc(v_nargs_378_);
v___x_379_ = lean_mk_array(v_nargs_378_, v_dummy_372_);
v___x_380_ = lean_nat_sub(v_nargs_378_, v___x_375_);
lean_dec(v_nargs_378_);
v___x_381_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_b_351_, v___x_379_, v___x_380_);
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
lean_del_object(v___x_369_);
v___x_386_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_357_, v___x_382_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v___x_388_ = lean_array_get_size(v_a_387_);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_391_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_388_, v_a_387_, v___x_377_, v___x_381_, v_mode_349_, v___x_389_, v___x_390_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_387_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_424_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_424_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_424_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_424_;
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
v___x_397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_382_, v___x_377_, v___x_381_, v_mode_349_, v___x_388_, v___x_390_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_411_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_411_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_411_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_411_;
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
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_box(v___x_385_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_403_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
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
v_val_407_ = lean_ctor_get(v_fst_402_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v_fst_402_, 1);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_val_407_);
v___x_409_ = v___x_400_;
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
v_a_412_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_397_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_397_);
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
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
v_val_420_ = lean_ctor_get(v_fst_396_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_fst_396_, 1);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_val_420_);
v___x_422_ = v___x_394_;
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
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
v_a_425_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_391_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_391_);
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
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
v_a_433_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_386_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_386_);
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
lean_object* v___x_441_; lean_object* v___x_443_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
lean_dec_ref(v_aFn_357_);
v___x_441_ = lean_box(v___x_384_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_441_);
v___x_443_ = v___x_369_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_447_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v___x_377_);
lean_dec_ref(v_aFn_357_);
v___x_445_ = lean_box(v___x_364_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_445_);
v___x_447_ = v___x_369_;
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
else
{
lean_object* v___x_450_; 
lean_dec_ref(v_aFn_357_);
lean_dec_ref(v_b_351_);
lean_dec_ref(v_a_350_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v_a_360_);
v___x_450_ = v___x_369_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_360_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_dec(v_a_360_);
lean_dec_ref(v_aFn_357_);
lean_dec_ref(v_b_351_);
lean_dec_ref(v_a_350_);
return v___x_366_;
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec(v_a_360_);
lean_dec_ref(v_bFn_358_);
lean_dec_ref(v_aFn_357_);
lean_dec_ref(v_b_351_);
lean_dec_ref(v_a_350_);
v___x_453_ = lean_box(v___x_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_453_);
v___x_455_ = v___x_362_;
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
else
{
lean_dec_ref(v_bFn_358_);
lean_dec_ref(v_aFn_357_);
lean_dec_ref(v_b_351_);
lean_dec_ref(v_a_350_);
return v___x_359_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6));
v___x_462_ = lean_unsigned_to_nat(27u);
v___x_463_ = lean_unsigned_to_nat(152u);
v___x_464_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5));
v___x_465_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4));
v___x_466_ = l_mkPanicMessageWithDecl(v___x_465_, v___x_464_, v___x_463_, v___x_462_, v___x_461_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(uint8_t v_mode_467_, lean_object* v_a_468_, lean_object* v_b_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_d_476_; lean_object* v_e_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; 
switch(lean_obj_tag(v_a_468_))
{
case 0:
{
lean_object* v_deBruijnIndex_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_deBruijnIndex_485_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_deBruijnIndex_485_);
lean_dec_ref_known(v_a_468_, 1);
v___x_486_ = l_Lean_Expr_bvarIdx_x21(v_b_469_);
lean_dec_ref(v_b_469_);
v___x_487_ = lean_nat_dec_lt(v_deBruijnIndex_485_, v___x_486_);
lean_dec(v___x_486_);
lean_dec(v_deBruijnIndex_485_);
v___x_488_ = lean_box(v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
case 1:
{
lean_object* v_fvarId_490_; lean_object* v___x_491_; 
v_fvarId_490_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_fvarId_490_);
lean_dec_ref_known(v_a_468_, 1);
v___x_491_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_490_, v_a_470_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = l_Lean_Expr_fvarId_x21(v_b_469_);
lean_dec_ref(v_b_469_);
v___x_494_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_493_, v_a_470_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_517_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_517_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_517_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_517_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_509_; 
if (lean_obj_tag(v_a_492_) == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_515_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_514_);
v___y_509_ = v___x_515_;
goto v___jp_508_;
}
else
{
lean_object* v_val_516_; 
v_val_516_ = lean_ctor_get(v_a_492_, 0);
lean_inc(v_val_516_);
lean_dec_ref_known(v_a_492_, 1);
v___y_509_ = v_val_516_;
goto v___jp_508_;
}
v___jp_499_:
{
lean_object* v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_502_ = l_Lean_LocalDecl_index(v___y_501_);
lean_dec_ref(v___y_501_);
v___x_503_ = lean_nat_dec_lt(v___y_500_, v___x_502_);
lean_dec(v___x_502_);
lean_dec(v___y_500_);
v___x_504_ = lean_box(v___x_503_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_504_);
v___x_506_ = v___x_497_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
v___jp_508_:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_LocalDecl_index(v___y_509_);
lean_dec_ref(v___y_509_);
if (lean_obj_tag(v_a_495_) == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_512_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_511_);
v___y_500_ = v___x_510_;
v___y_501_ = v___x_512_;
goto v___jp_499_;
}
else
{
lean_object* v_val_513_; 
v_val_513_ = lean_ctor_get(v_a_495_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v_a_495_, 1);
v___y_500_ = v___x_510_;
v___y_501_ = v_val_513_;
goto v___jp_499_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_a_492_);
v_a_518_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_494_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_494_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v_b_469_);
v_a_526_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_491_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_491_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_534_; lean_object* v___x_535_; uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_mvarId_534_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_mvarId_534_);
lean_dec_ref_known(v_a_468_, 1);
v___x_535_ = l_Lean_Expr_mvarId_x21(v_b_469_);
lean_dec_ref(v_b_469_);
v___x_536_ = l_Lean_Name_lt(v_mvarId_534_, v___x_535_);
lean_dec(v___x_535_);
lean_dec(v_mvarId_534_);
v___x_537_ = lean_box(v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
case 3:
{
lean_object* v_u_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_u_539_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_u_539_);
lean_dec_ref_known(v_a_468_, 1);
v___x_540_ = l_Lean_Expr_sortLevel_x21(v_b_469_);
lean_dec_ref(v_b_469_);
v___x_541_ = l_Lean_Level_normLt(v_u_539_, v___x_540_);
lean_dec(v___x_540_);
lean_dec(v_u_539_);
v___x_542_ = lean_box(v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
case 4:
{
lean_object* v_declName_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_declName_544_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_declName_544_);
lean_dec_ref_known(v_a_468_, 2);
v___x_545_ = l_Lean_Expr_constName_x21(v_b_469_);
lean_dec_ref(v_b_469_);
v___x_546_ = l_Lean_Name_lt(v_declName_544_, v___x_545_);
lean_dec(v___x_545_);
lean_dec(v_declName_544_);
v___x_547_ = lean_box(v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
case 5:
{
lean_object* v___x_549_; 
v___x_549_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_467_, v_a_468_, v_b_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v___x_549_;
}
case 8:
{
lean_object* v_value_550_; lean_object* v_body_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_value_550_ = lean_ctor_get(v_a_468_, 2);
lean_inc_ref(v_value_550_);
v_body_551_ = lean_ctor_get(v_a_468_, 3);
lean_inc_ref(v_body_551_);
lean_dec_ref_known(v_a_468_, 4);
v___x_552_ = l_Lean_Expr_letValue_x21(v_b_469_);
v___x_553_ = l_Lean_Expr_letBody_x21(v_b_469_);
lean_dec_ref(v_b_469_);
v___x_554_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_467_, v_value_550_, v_body_551_, v___x_552_, v___x_553_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v___x_554_;
}
case 9:
{
lean_object* v_a_555_; lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_a_555_ = lean_ctor_get(v_a_468_, 0);
lean_inc_ref(v_a_555_);
lean_dec_ref_known(v_a_468_, 1);
v___x_556_ = l_Lean_Expr_litValue_x21(v_b_469_);
lean_dec_ref(v_b_469_);
v___x_557_ = l_Lean_Literal_lt(v_a_555_, v___x_556_);
lean_dec_ref(v___x_556_);
lean_dec_ref(v_a_555_);
v___x_558_ = lean_box(v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
case 10:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref_known(v_a_468_, 2);
lean_dec_ref(v_b_469_);
v___x_560_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
v___x_561_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_560_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v___x_561_;
}
case 11:
{
lean_object* v_idx_562_; lean_object* v_struct_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_idx_562_ = lean_ctor_get(v_a_468_, 1);
lean_inc(v_idx_562_);
v_struct_563_ = lean_ctor_get(v_a_468_, 2);
lean_inc_ref(v_struct_563_);
lean_dec_ref_known(v_a_468_, 3);
v___x_564_ = l_Lean_Expr_projIdx_x21(v_b_469_);
v___x_565_ = lean_nat_dec_eq(v_idx_562_, v___x_564_);
if (v___x_565_ == 0)
{
uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v_struct_563_);
lean_dec_ref(v_b_469_);
v___x_566_ = lean_nat_dec_lt(v_idx_562_, v___x_564_);
lean_dec(v___x_564_);
lean_dec(v_idx_562_);
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v___x_564_);
lean_dec(v_idx_562_);
v___x_569_ = l_Lean_Expr_projExpr_x21(v_b_469_);
lean_dec_ref(v_b_469_);
v___x_570_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_467_, v_struct_563_, v___x_569_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v___x_570_;
}
}
default: 
{
lean_object* v_binderType_571_; lean_object* v_body_572_; 
v_binderType_571_ = lean_ctor_get(v_a_468_, 1);
lean_inc_ref(v_binderType_571_);
v_body_572_ = lean_ctor_get(v_a_468_, 2);
lean_inc_ref(v_body_572_);
lean_dec_ref(v_a_468_);
v_d_476_ = v_binderType_571_;
v_e_477_ = v_body_572_;
v___y_478_ = v_a_470_;
v___y_479_ = v_a_471_;
v___y_480_ = v_a_472_;
v___y_481_ = v_a_473_;
goto v___jp_475_;
}
}
v___jp_475_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = l_Lean_Expr_bindingDomain_x21(v_b_469_);
v___x_483_ = l_Lean_Expr_bindingBody_x21(v_b_469_);
lean_dec_ref(v_b_469_);
v___x_484_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_467_, v_d_476_, v_e_477_, v___x_482_, v___x_483_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(uint8_t v_mode_573_, lean_object* v_a_574_, lean_object* v_b_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0));
v___x_582_ = l_Lean_Core_checkSystem(v___x_581_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v___x_583_; 
lean_dec_ref_known(v___x_582_, 1);
lean_inc_ref(v_a_574_);
lean_inc_ref(v_b_575_);
v___x_583_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_573_, v_b_575_, v_a_574_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; uint8_t v___x_585_; uint8_t v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v___x_585_ = 1;
v___x_586_ = lean_unbox(v_a_584_);
if (v___x_586_ == 0)
{
uint8_t v___x_587_; uint8_t v___x_588_; uint8_t v___x_589_; 
v___x_587_ = l_Lean_Expr_ctorWeight(v_b_575_);
v___x_588_ = l_Lean_Expr_ctorWeight(v_a_574_);
v___x_589_ = lean_uint8_dec_lt(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_dec_ref_known(v___x_583_, 1);
lean_inc_ref(v_b_575_);
lean_inc_ref(v_a_574_);
v___x_590_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_573_, v_a_574_, v_b_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_606_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_606_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; 
v___x_595_ = lean_unbox(v_a_591_);
lean_dec(v_a_591_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_598_; 
lean_dec_ref(v_b_575_);
lean_dec_ref(v_a_574_);
v___x_596_ = lean_box(v___x_589_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
uint8_t v___x_600_; 
v___x_600_ = lean_uint8_dec_lt(v___x_588_, v___x_587_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
lean_del_object(v___x_593_);
v___x_601_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_573_, v_a_574_, v_b_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec_ref(v_b_575_);
lean_dec_ref(v_a_574_);
v___x_602_ = lean_box(v___x_585_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_602_);
v___x_604_ = v___x_593_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
else
{
lean_dec_ref(v_b_575_);
lean_dec_ref(v_a_574_);
return v___x_590_;
}
}
else
{
lean_dec_ref(v_b_575_);
lean_dec_ref(v_a_574_);
return v___x_583_;
}
}
else
{
lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_b_575_);
lean_dec_ref(v_a_574_);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_583_, 0);
lean_dec(v_unused_615_);
v___x_608_ = v___x_583_;
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
else
{
lean_dec(v___x_583_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_box(v___x_585_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_dec_ref(v_b_575_);
lean_dec_ref(v_a_574_);
return v___x_583_;
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_b_575_);
lean_dec_ref(v_a_574_);
v_a_616_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_582_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_582_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(uint8_t v_mode_624_, lean_object* v_a_625_, lean_object* v_b_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = lean_expr_eqv(v_a_625_, v_b_626_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; 
v___x_633_ = l_Lean_Expr_isMData(v_a_625_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
v___x_634_ = l_Lean_Expr_isMData(v_b_626_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_624_, v_a_625_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_624_, v_b_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_624_, v_a_636_, v_a_638_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_639_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_636_);
v_a_640_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_637_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_637_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v_b_626_);
v_a_648_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_635_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_635_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Expr_mdataExpr_x21(v_b_626_);
lean_dec_ref(v_b_626_);
v_b_626_ = v___x_656_;
goto _start;
}
}
else
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Expr_mdataExpr_x21(v_a_625_);
lean_dec_ref(v_a_625_);
v_a_625_ = v___x_658_;
goto _start;
}
}
else
{
uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec_ref(v_b_626_);
lean_dec_ref(v_a_625_);
v___x_660_ = 0;
v___x_661_ = lean_box(v___x_660_);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(lean_object* v_upperBound_663_, lean_object* v_a_664_, lean_object* v_args_665_, uint8_t v_mode_666_, lean_object* v_b_667_, lean_object* v_a_668_, lean_object* v_b_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_a_676_; uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_lt(v_a_668_, v_upperBound_663_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
lean_dec(v_a_668_);
lean_dec_ref(v_b_667_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v_b_669_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v_isInstance_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec_ref(v_b_669_);
v___x_682_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_683_ = lean_array_get_borrowed(v___x_682_, v_a_664_, v_a_668_);
v_isInstance_684_ = lean_ctor_get_uint8(v___x_683_, sizeof(void*)*1 + 4);
v___x_685_ = lean_box(0);
v___x_686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_684_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = l_Lean_instInhabitedExpr;
v___x_688_ = lean_array_get_borrowed(v___x_687_, v_args_665_, v_a_668_);
lean_inc_ref(v_b_667_);
lean_inc(v___x_688_);
v___x_689_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_666_, v___x_688_, v_b_667_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_700_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_700_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_700_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_700_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
uint8_t v___x_694_; 
v___x_694_ = lean_unbox(v_a_690_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec(v_a_668_);
lean_dec_ref(v_b_667_);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v_a_690_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_685_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_696_);
v___x_698_ = v___x_692_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_del_object(v___x_692_);
lean_dec(v_a_690_);
v_a_676_ = v___x_686_;
goto v___jp_675_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_a_668_);
lean_dec_ref(v_b_667_);
v_a_701_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_689_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_689_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
v_a_676_ = v___x_686_;
goto v___jp_675_;
}
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_add(v_a_668_, v___x_677_);
lean_dec(v_a_668_);
lean_inc_ref(v_a_676_);
v_a_668_ = v___x_678_;
v_b_669_ = v_a_676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(lean_object* v_upperBound_709_, lean_object* v_args_710_, uint8_t v_mode_711_, lean_object* v_b_712_, lean_object* v_a_713_, lean_object* v_b_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_lt(v_a_713_, v_upperBound_709_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec(v_a_713_);
lean_dec_ref(v_b_712_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_b_714_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec_ref(v_b_714_);
v___x_722_ = lean_box(0);
v___x_723_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_724_ = lean_array_fget_borrowed(v_args_710_, v_a_713_);
lean_inc_ref(v_b_712_);
lean_inc(v___x_724_);
v___x_725_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_711_, v___x_724_, v_b_712_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_739_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_739_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
uint8_t v___x_730_; 
v___x_730_ = lean_unbox(v_a_726_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
lean_dec(v_a_713_);
lean_dec_ref(v_b_712_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v_a_726_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v___x_722_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_732_);
v___x_734_ = v___x_728_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_del_object(v___x_728_);
lean_dec(v_a_726_);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_add(v_a_713_, v___x_736_);
lean_dec(v_a_713_);
v_a_713_ = v___x_737_;
v_b_714_ = v___x_723_;
goto _start;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_a_713_);
lean_dec_ref(v_b_712_);
v_a_740_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_725_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_725_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(uint8_t v_mode_748_, lean_object* v_b_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
if (lean_obj_tag(v_x_750_) == 5)
{
lean_object* v_fn_758_; lean_object* v_arg_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_fn_758_ = lean_ctor_get(v_x_750_, 0);
lean_inc_ref(v_fn_758_);
v_arg_759_ = lean_ctor_get(v_x_750_, 1);
lean_inc_ref(v_arg_759_);
lean_dec_ref_known(v_x_750_, 2);
v___x_760_ = lean_array_set(v_x_751_, v_x_752_, v_arg_759_);
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_sub(v_x_752_, v___x_761_);
lean_dec(v_x_752_);
v_x_750_ = v_fn_758_;
v_x_751_ = v___x_760_;
v_x_752_ = v___x_762_;
goto _start;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec(v_x_752_);
v___x_764_ = lean_array_get_size(v_x_751_);
v___x_765_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_x_750_, v___x_764_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = lean_array_get_size(v_a_766_);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
lean_inc_ref(v_b_749_);
v___x_770_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_767_, v_a_766_, v_x_751_, v_mode_748_, v_b_749_, v___x_768_, v___x_769_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v_a_766_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_804_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_804_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_804_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_804_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_fst_775_; 
v_fst_775_ = lean_ctor_get(v_a_771_, 0);
lean_inc(v_fst_775_);
lean_dec(v_a_771_);
if (lean_obj_tag(v_fst_775_) == 0)
{
lean_object* v___x_776_; 
lean_del_object(v___x_773_);
v___x_776_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_764_, v_x_751_, v_mode_748_, v_b_749_, v___x_767_, v___x_769_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec_ref(v_x_751_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_791_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_791_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_791_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_791_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_fst_781_; 
v_fst_781_ = lean_ctor_get(v_a_777_, 0);
lean_inc(v_fst_781_);
lean_dec(v_a_777_);
if (lean_obj_tag(v_fst_781_) == 0)
{
uint8_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = 1;
v___x_783_ = lean_box(v___x_782_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_783_);
v___x_785_ = v___x_779_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
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
lean_object* v_val_787_; lean_object* v___x_789_; 
v_val_787_ = lean_ctor_get(v_fst_781_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v_fst_781_, 1);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_val_787_);
v___x_789_ = v___x_779_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_val_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v_a_792_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_776_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_776_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_val_800_; lean_object* v___x_802_; 
lean_dec_ref(v_x_751_);
lean_dec_ref(v_b_749_);
v_val_800_ = lean_ctor_get(v_fst_775_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v_fst_775_, 1);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_val_800_);
v___x_802_ = v___x_773_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_val_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v_x_751_);
lean_dec_ref(v_b_749_);
v_a_805_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_770_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_770_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v_x_751_);
lean_dec_ref(v_b_749_);
v_a_813_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_765_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_765_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(uint8_t v_mode_821_, lean_object* v_a_822_, lean_object* v_b_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_d_830_; lean_object* v_e_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; 
switch(lean_obj_tag(v_a_822_))
{
case 11:
{
lean_object* v_struct_840_; lean_object* v___x_841_; 
v_struct_840_ = lean_ctor_get(v_a_822_, 2);
lean_inc_ref(v_struct_840_);
lean_dec_ref_known(v_a_822_, 3);
v___x_841_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_821_, v_struct_840_, v_b_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
return v___x_841_;
}
case 5:
{
lean_object* v_dummy_842_; lean_object* v_nargs_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_dummy_842_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_843_ = l_Lean_Expr_getAppNumArgs(v_a_822_);
lean_inc(v_nargs_843_);
v___x_844_ = lean_mk_array(v_nargs_843_, v_dummy_842_);
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = lean_nat_sub(v_nargs_843_, v___x_845_);
lean_dec(v_nargs_843_);
v___x_847_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_821_, v_b_823_, v_a_822_, v___x_844_, v___x_846_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
return v___x_847_;
}
case 6:
{
lean_object* v_binderType_848_; lean_object* v_body_849_; 
v_binderType_848_ = lean_ctor_get(v_a_822_, 1);
lean_inc_ref(v_binderType_848_);
v_body_849_ = lean_ctor_get(v_a_822_, 2);
lean_inc_ref(v_body_849_);
lean_dec_ref_known(v_a_822_, 3);
v_d_830_ = v_binderType_848_;
v_e_831_ = v_body_849_;
v___y_832_ = v_a_824_;
v___y_833_ = v_a_825_;
v___y_834_ = v_a_826_;
v___y_835_ = v_a_827_;
goto v___jp_829_;
}
case 7:
{
lean_object* v_binderType_850_; lean_object* v_body_851_; 
v_binderType_850_ = lean_ctor_get(v_a_822_, 1);
lean_inc_ref(v_binderType_850_);
v_body_851_ = lean_ctor_get(v_a_822_, 2);
lean_inc_ref(v_body_851_);
lean_dec_ref_known(v_a_822_, 3);
v_d_830_ = v_binderType_850_;
v_e_831_ = v_body_851_;
v___y_832_ = v_a_824_;
v___y_833_ = v_a_825_;
v___y_834_ = v_a_826_;
v___y_835_ = v_a_827_;
goto v___jp_829_;
}
case 8:
{
lean_object* v_value_852_; lean_object* v_body_853_; lean_object* v___x_854_; 
v_value_852_ = lean_ctor_get(v_a_822_, 2);
lean_inc_ref(v_value_852_);
v_body_853_ = lean_ctor_get(v_a_822_, 3);
lean_inc_ref(v_body_853_);
lean_dec_ref_known(v_a_822_, 4);
lean_inc_ref(v_b_823_);
v___x_854_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_821_, v_value_852_, v_b_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; uint8_t v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v___x_856_ = lean_unbox(v_a_855_);
if (v___x_856_ == 0)
{
lean_dec_ref(v_body_853_);
lean_dec_ref(v_b_823_);
return v___x_854_;
}
else
{
lean_object* v___x_857_; 
lean_dec_ref_known(v___x_854_, 1);
v___x_857_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_821_, v_body_853_, v_b_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
return v___x_857_;
}
}
else
{
lean_dec_ref(v_body_853_);
lean_dec_ref(v_b_823_);
return v___x_854_;
}
}
default: 
{
uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec_ref(v_b_823_);
lean_dec_ref(v_a_822_);
v___x_858_ = 1;
v___x_859_ = lean_box(v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
v___jp_829_:
{
lean_object* v___x_836_; 
lean_inc_ref(v_b_823_);
v___x_836_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_821_, v_d_830_, v_b_823_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; uint8_t v___x_838_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v___x_838_ = lean_unbox(v_a_837_);
if (v___x_838_ == 0)
{
lean_dec_ref(v_e_831_);
lean_dec_ref(v_b_823_);
return v___x_836_;
}
else
{
lean_object* v___x_839_; 
lean_dec_ref_known(v___x_836_, 1);
v___x_839_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_821_, v_e_831_, v_b_823_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
return v___x_839_;
}
}
else
{
lean_dec_ref(v_e_831_);
lean_dec_ref(v_b_823_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(uint8_t v_mode_861_, lean_object* v_a_862_, lean_object* v_b_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_861_, v_a_862_, v_b_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_885_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_885_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_885_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_885_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___x_874_; 
v___x_874_ = lean_unbox(v_a_870_);
lean_dec(v_a_870_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = 1;
v___x_876_ = lean_box(v___x_875_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_876_);
v___x_878_ = v___x_872_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = 0;
v___x_881_ = lean_box(v___x_880_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_881_);
v___x_883_ = v___x_872_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(lean_object* v_mode_886_, lean_object* v_a_887_, lean_object* v_b_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
uint8_t v_mode_boxed_894_; lean_object* v_res_895_; 
v_mode_boxed_894_ = lean_unbox(v_mode_886_);
v_res_895_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_boxed_894_, v_a_887_, v_b_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(lean_object* v_mode_896_, lean_object* v_a_u2081_897_, lean_object* v_a_u2082_898_, lean_object* v_b_u2081_899_, lean_object* v_b_u2082_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
uint8_t v_mode_boxed_906_; lean_object* v_res_907_; 
v_mode_boxed_906_ = lean_unbox(v_mode_896_);
v_res_907_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_boxed_906_, v_a_u2081_897_, v_a_u2082_898_, v_b_u2081_899_, v_b_u2082_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(lean_object* v_upperBound_908_, lean_object* v_args_909_, lean_object* v_mode_910_, lean_object* v_b_911_, lean_object* v_a_912_, lean_object* v_b_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
uint8_t v_mode_boxed_919_; lean_object* v_res_920_; 
v_mode_boxed_919_ = lean_unbox(v_mode_910_);
v_res_920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_908_, v_args_909_, v_mode_boxed_919_, v_b_911_, v_a_912_, v_b_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_args_909_);
lean_dec(v_upperBound_908_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object* v_mode_921_, lean_object* v_a_922_, lean_object* v_b_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
uint8_t v_mode_boxed_929_; lean_object* v_res_930_; 
v_mode_boxed_929_ = lean_unbox(v_mode_921_);
v_res_930_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_boxed_929_, v_a_922_, v_b_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object* v_upperBound_931_, lean_object* v_a_932_, lean_object* v_args_933_, lean_object* v_mode_934_, lean_object* v_b_935_, lean_object* v_a_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
uint8_t v_mode_boxed_943_; lean_object* v_res_944_; 
v_mode_boxed_943_ = lean_unbox(v_mode_934_);
v_res_944_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_931_, v_a_932_, v_args_933_, v_mode_boxed_943_, v_b_935_, v_a_936_, v_b_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec_ref(v_args_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_upperBound_931_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object* v_mode_945_, lean_object* v_a_946_, lean_object* v_b_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
uint8_t v_mode_boxed_953_; lean_object* v_res_954_; 
v_mode_boxed_953_ = lean_unbox(v_mode_945_);
v_res_954_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_boxed_953_, v_a_946_, v_b_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object* v_mode_955_, lean_object* v_a_956_, lean_object* v_b_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
uint8_t v_mode_boxed_963_; lean_object* v_res_964_; 
v_mode_boxed_963_ = lean_unbox(v_mode_955_);
v_res_964_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_boxed_963_, v_a_956_, v_b_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(lean_object* v_upperBound_965_, lean_object* v___x_966_, lean_object* v___x_967_, lean_object* v_mode_968_, lean_object* v_a_969_, lean_object* v_b_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v_mode_boxed_976_; lean_object* v_res_977_; 
v_mode_boxed_976_ = lean_unbox(v_mode_968_);
v_res_977_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_965_, v___x_966_, v___x_967_, v_mode_boxed_976_, v_a_969_, v_b_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec_ref(v___x_967_);
lean_dec_ref(v___x_966_);
lean_dec(v_upperBound_965_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(lean_object* v_mode_978_, lean_object* v_b_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v_mode_boxed_988_; lean_object* v_res_989_; 
v_mode_boxed_988_ = lean_unbox(v_mode_978_);
v_res_989_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_988_, v_b_979_, v_x_980_, v_x_981_, v_x_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(lean_object* v_upperBound_990_, lean_object* v_a_991_, lean_object* v___x_992_, lean_object* v___x_993_, lean_object* v_mode_994_, lean_object* v_a_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v_mode_boxed_1002_; lean_object* v_res_1003_; 
v_mode_boxed_1002_ = lean_unbox(v_mode_994_);
v_res_1003_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_990_, v_a_991_, v___x_992_, v___x_993_, v_mode_boxed_1002_, v_a_995_, v_b_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec_ref(v___x_993_);
lean_dec_ref(v___x_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_upperBound_990_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(lean_object* v_mode_1004_, lean_object* v_a_1005_, lean_object* v_b_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
uint8_t v_mode_boxed_1012_; lean_object* v_res_1013_; 
v_mode_boxed_1012_ = lean_unbox(v_mode_1004_);
v_res_1013_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_boxed_1012_, v_a_1005_, v_b_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(lean_object* v_mode_1014_, lean_object* v_a_1015_, lean_object* v_b_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
uint8_t v_mode_boxed_1022_; lean_object* v_res_1023_; 
v_mode_boxed_1022_ = lean_unbox(v_mode_1014_);
v_res_1023_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_boxed_1022_, v_a_1015_, v_b_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(lean_object* v_upperBound_1024_, lean_object* v___x_1025_, lean_object* v___x_1026_, uint8_t v_mode_1027_, lean_object* v_inst_1028_, lean_object* v_R_1029_, lean_object* v_a_1030_, lean_object* v_b_1031_, lean_object* v_c_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_1024_, v___x_1025_, v___x_1026_, v_mode_1027_, v_a_1030_, v_b_1031_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(lean_object* v_upperBound_1039_, lean_object* v___x_1040_, lean_object* v___x_1041_, lean_object* v_mode_1042_, lean_object* v_inst_1043_, lean_object* v_R_1044_, lean_object* v_a_1045_, lean_object* v_b_1046_, lean_object* v_c_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v_mode_boxed_1053_; lean_object* v_res_1054_; 
v_mode_boxed_1053_ = lean_unbox(v_mode_1042_);
v_res_1054_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_1039_, v___x_1040_, v___x_1041_, v_mode_boxed_1053_, v_inst_1043_, v_R_1044_, v_a_1045_, v_b_1046_, v_c_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v___x_1040_);
lean_dec(v_upperBound_1039_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(lean_object* v_upperBound_1055_, lean_object* v_a_1056_, lean_object* v___x_1057_, lean_object* v___x_1058_, uint8_t v_mode_1059_, lean_object* v_inst_1060_, lean_object* v_R_1061_, lean_object* v_a_1062_, lean_object* v_b_1063_, lean_object* v_c_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_1055_, v_a_1056_, v___x_1057_, v___x_1058_, v_mode_1059_, v_a_1062_, v_b_1063_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(lean_object* v_upperBound_1071_, lean_object* v_a_1072_, lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v_mode_1075_, lean_object* v_inst_1076_, lean_object* v_R_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_, lean_object* v_c_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
uint8_t v_mode_boxed_1086_; lean_object* v_res_1087_; 
v_mode_boxed_1086_ = lean_unbox(v_mode_1075_);
v_res_1087_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_1071_, v_a_1072_, v___x_1073_, v___x_1074_, v_mode_boxed_1086_, v_inst_1076_, v_R_1077_, v_a_1078_, v_b_1079_, v_c_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1074_);
lean_dec_ref(v___x_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_upperBound_1071_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(lean_object* v_upperBound_1088_, lean_object* v_args_1089_, uint8_t v_mode_1090_, lean_object* v_b_1091_, lean_object* v_inst_1092_, lean_object* v_R_1093_, lean_object* v_a_1094_, lean_object* v_b_1095_, lean_object* v_c_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_1088_, v_args_1089_, v_mode_1090_, v_b_1091_, v_a_1094_, v_b_1095_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(lean_object* v_upperBound_1103_, lean_object* v_args_1104_, lean_object* v_mode_1105_, lean_object* v_b_1106_, lean_object* v_inst_1107_, lean_object* v_R_1108_, lean_object* v_a_1109_, lean_object* v_b_1110_, lean_object* v_c_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v_mode_boxed_1117_; lean_object* v_res_1118_; 
v_mode_boxed_1117_ = lean_unbox(v_mode_1105_);
v_res_1118_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_1103_, v_args_1104_, v_mode_boxed_1117_, v_b_1106_, v_inst_1107_, v_R_1108_, v_a_1109_, v_b_1110_, v_c_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v_args_1104_);
lean_dec(v_upperBound_1103_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(lean_object* v_upperBound_1119_, lean_object* v_a_1120_, lean_object* v_args_1121_, uint8_t v_mode_1122_, lean_object* v_b_1123_, lean_object* v_inst_1124_, lean_object* v_R_1125_, lean_object* v_a_1126_, lean_object* v_b_1127_, lean_object* v_c_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_1119_, v_a_1120_, v_args_1121_, v_mode_1122_, v_b_1123_, v_a_1126_, v_b_1127_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(lean_object* v_upperBound_1135_, lean_object* v_a_1136_, lean_object* v_args_1137_, lean_object* v_mode_1138_, lean_object* v_b_1139_, lean_object* v_inst_1140_, lean_object* v_R_1141_, lean_object* v_a_1142_, lean_object* v_b_1143_, lean_object* v_c_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v_mode_boxed_1150_; lean_object* v_res_1151_; 
v_mode_boxed_1150_ = lean_unbox(v_mode_1138_);
v_res_1151_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_1135_, v_a_1136_, v_args_1137_, v_mode_boxed_1150_, v_b_1139_, v_inst_1140_, v_R_1141_, v_a_1142_, v_b_1143_, v_c_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec_ref(v_args_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_upperBound_1135_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main(lean_object* v_a_1152_, lean_object* v_b_1153_, uint8_t v_mode_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1154_, v_a_1152_, v_b_1153_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main___boxed(lean_object* v_a_1161_, lean_object* v_b_1162_, lean_object* v_mode_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
uint8_t v_mode_boxed_1169_; lean_object* v_res_1170_; 
v_mode_boxed_1169_ = lean_unbox(v_mode_1163_);
v_res_1170_ = l_Lean_Meta_ACLt_main(v_a_1161_, v_b_1162_, v_mode_boxed_1169_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt(lean_object* v_a_1171_, lean_object* v_b_1172_, uint8_t v_mode_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1173_, v_a_1171_, v_b_1172_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt___boxed(lean_object* v_a_1180_, lean_object* v_b_1181_, lean_object* v_mode_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
uint8_t v_mode_boxed_1188_; lean_object* v_res_1189_; 
v_mode_boxed_1188_ = lean_unbox(v_mode_1182_);
v_res_1189_ = l_Lean_Meta_acLt(v_a_1180_, v_b_1181_, v_mode_boxed_1188_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
return v_res_1189_;
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
