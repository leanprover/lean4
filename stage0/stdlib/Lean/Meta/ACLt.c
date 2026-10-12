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
uint8_t l_Lean_Expr_ctorWeight(lean_object* v_x_1_){
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
LEAN_EXPORT void l_Lean_Expr_ctorWeight_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint8_t v_res_14_;
v_res_14_ = l_Lean_Expr_ctorWeight(v_x_1_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorWeight___boxed(lean_object* v_x_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Lean_Expr_ctorWeight(v_x_15_);
lean_dec_ref(v_x_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl(uint8_t v_x_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_box(v_x_18_);
v___x_20_ = lean_obj_tag_nat(v___x_19_);
lean_dec(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_18_ = stack[0].m_num;
lean_object* v_res_21_;
v_res_21_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl(v_x_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl___boxed(lean_object* v_x_22_){
_start:
{
uint8_t v_x_4__boxed_23_; lean_object* v_res_24_; 
v_x_4__boxed_23_ = lean_unbox(v_x_22_);
v_res_24_ = l_Lean_Meta_ACLt_ReduceMode_ctorIdx___impl(v_x_4__boxed_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(lean_object* v_k_25_){
_start:
{
lean_inc(v_k_25_);
return v_k_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg___boxed(lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim___redArg(v_k_26_);
lean_dec(v_k_26_);
return v_res_27_;
}
}
lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim(lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, uint8_t v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_inc(v_k_32_);
return v_k_32_;
}
}
LEAN_EXPORT void l_Lean_Meta_ACLt_ReduceMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_29_ = stack[1].m_obj;
uint8_t v_t_30_ = stack[2].m_num;
lean_object* v_k_32_ = stack[4].m_obj;
lean_object* v_res_33_;
v_res_33_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim(lean_box(0), v_ctorIdx_29_, v_t_30_, lean_box(0), v_k_32_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_ctorElim___boxed(lean_object* v_motive_34_, lean_object* v_ctorIdx_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_k_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Meta_ACLt_ReduceMode_ctorElim(v_motive_34_, v_ctorIdx_35_, v_t_boxed_39_, v_h_37_, v_k_38_);
lean_dec(v_k_38_);
lean_dec(v_ctorIdx_35_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(lean_object* v_reduce_41_){
_start:
{
lean_inc(v_reduce_41_);
return v_reduce_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg___boxed(lean_object* v_reduce_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim___redArg(v_reduce_42_);
lean_dec(v_reduce_42_);
return v_res_43_;
}
}
lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_reduce_47_){
_start:
{
lean_inc(v_reduce_47_);
return v_reduce_47_;
}
}
LEAN_EXPORT void l_Lean_Meta_ACLt_ReduceMode_reduce_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_45_ = stack[1].m_num;
lean_object* v_reduce_47_ = stack[3].m_obj;
lean_object* v_res_48_;
v_res_48_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim(lean_box(0), v_t_45_, lean_box(0), v_reduce_47_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduce_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_reduce_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Lean_Meta_ACLt_ReduceMode_reduce_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_reduce_52_);
lean_dec(v_reduce_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(lean_object* v_reduceSimpleOnly_55_){
_start:
{
lean_inc(v_reduceSimpleOnly_55_);
return v_reduceSimpleOnly_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg___boxed(lean_object* v_reduceSimpleOnly_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___redArg(v_reduceSimpleOnly_56_);
lean_dec(v_reduceSimpleOnly_56_);
return v_res_57_;
}
}
lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_reduceSimpleOnly_61_){
_start:
{
lean_inc(v_reduceSimpleOnly_61_);
return v_reduceSimpleOnly_61_;
}
}
LEAN_EXPORT void l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_59_ = stack[1].m_num;
lean_object* v_reduceSimpleOnly_61_ = stack[3].m_obj;
lean_object* v_res_62_;
v_res_62_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(lean_box(0), v_t_59_, lean_box(0), v_reduceSimpleOnly_61_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim___boxed(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_reduceSimpleOnly_66_){
_start:
{
uint8_t v_t_boxed_67_; lean_object* v_res_68_; 
v_t_boxed_67_ = lean_unbox(v_t_64_);
v_res_68_ = l_Lean_Meta_ACLt_ReduceMode_reduceSimpleOnly_elim(v_motive_63_, v_t_boxed_67_, v_h_65_, v_reduceSimpleOnly_66_);
lean_dec(v_reduceSimpleOnly_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(lean_object* v_none_69_){
_start:
{
lean_inc(v_none_69_);
return v_none_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg___boxed(lean_object* v_none_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Meta_ACLt_ReduceMode_none_elim___redArg(v_none_70_);
lean_dec(v_none_70_);
return v_res_71_;
}
}
lean_object* l_Lean_Meta_ACLt_ReduceMode_none_elim(lean_object* v_motive_72_, uint8_t v_t_73_, lean_object* v_h_74_, lean_object* v_none_75_){
_start:
{
lean_inc(v_none_75_);
return v_none_75_;
}
}
LEAN_EXPORT void l_Lean_Meta_ACLt_ReduceMode_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_73_ = stack[1].m_num;
lean_object* v_none_75_ = stack[3].m_obj;
lean_object* v_res_76_;
v_res_76_ = l_Lean_Meta_ACLt_ReduceMode_none_elim(lean_box(0), v_t_73_, lean_box(0), v_none_75_);
stack->m_obj
 = v_res_76_;
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
lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(uint8_t v_mode_92_, lean_object* v_e_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
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
lean_object* v___x_101_; lean_object* v_config_102_; uint8_t v_trackZetaDelta_103_; lean_object* v_zetaDeltaSet_104_; lean_object* v_lctx_105_; lean_object* v_localInstances_106_; lean_object* v_defEqCtx_x3f_107_; lean_object* v_synthPendingDepth_108_; lean_object* v_customCanUnfoldPredicate_x3f_109_; uint8_t v_univApprox_110_; uint8_t v_inTypeClassResolution_111_; uint8_t v_cacheInferType_112_; uint64_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_101_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_config;
v_config_102_ = lean_ctor_get(v___x_101_, 0);
v_trackZetaDelta_103_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7);
v_zetaDeltaSet_104_ = lean_ctor_get(v_a_94_, 1);
v_lctx_105_ = lean_ctor_get(v_a_94_, 2);
v_localInstances_106_ = lean_ctor_get(v_a_94_, 3);
v_defEqCtx_x3f_107_ = lean_ctor_get(v_a_94_, 4);
v_synthPendingDepth_108_ = lean_ctor_get(v_a_94_, 5);
v_customCanUnfoldPredicate_x3f_109_ = lean_ctor_get(v_a_94_, 6);
v_univApprox_110_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_111_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7 + 2);
v_cacheInferType_112_ = lean_ctor_get_uint8(v_a_94_, sizeof(void*)*7 + 3);
v___x_113_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_102_);
lean_inc_ref(v_config_102_);
v___x_114_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_114_, 0, v_config_102_);
lean_ctor_set_uint64(v___x_114_, sizeof(void*)*1, v___x_113_);
lean_inc(v_customCanUnfoldPredicate_x3f_109_);
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
lean_ctor_set(v___x_115_, 6, v_customCanUnfoldPredicate_x3f_109_);
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
LEAN_EXPORT void l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_92_ = stack[0].m_num;
lean_object* v_e_93_ = stack[1].m_obj;
lean_object* v_a_94_ = stack[2].m_obj;
lean_object* v_a_95_ = stack[3].m_obj;
lean_object* v_a_96_ = stack[4].m_obj;
lean_object* v_a_97_ = stack[5].m_obj;
lean_object* v_res_119_;
v_res_119_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_92_, v_e_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
stack->m_obj
 = v_res_119_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce___boxed(lean_object* v_mode_120_, lean_object* v_e_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
uint8_t v_mode_boxed_127_; lean_object* v_res_128_; 
v_mode_boxed_127_ = lean_unbox(v_mode_120_);
v_res_128_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_boxed_127_, v_e_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
return v_res_128_;
}
}
lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(lean_object* v_f_131_, lean_object* v_numArgs_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = l_Lean_Expr_hasLooseBVars(v_f_131_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_getFunInfoNArgs(v_f_131_, v_numArgs_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_148_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_148_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_paramInfo_144_; lean_object* v___x_146_; 
v_paramInfo_144_ = lean_ctor_get(v_a_140_, 0);
lean_inc_ref(v_paramInfo_144_);
lean_dec(v_a_140_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v_paramInfo_144_);
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_paramInfo_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_a_149_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_139_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_139_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
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
else
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_numArgs_132_);
lean_dec_ref(v_f_131_);
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___closed__0));
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_131_ = stack[0].m_obj;
lean_object* v_numArgs_132_ = stack[1].m_obj;
lean_object* v_a_133_ = stack[2].m_obj;
lean_object* v_a_134_ = stack[3].m_obj;
lean_object* v_a_135_ = stack[4].m_obj;
lean_object* v_a_136_ = stack[5].m_obj;
lean_object* v_res_159_;
v_res_159_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_f_131_, v_numArgs_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo___boxed(lean_object* v_f_160_, lean_object* v_numArgs_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_f_160_, v_numArgs_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
return v_res_167_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(lean_object* v_msg_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___f_175_; lean_object* v___x_12973__overap_176_; lean_object* v___x_177_; 
v___f_175_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___closed__0));
v___x_12973__overap_176_ = lean_panic_fn_borrowed(v___f_175_, v_msg_169_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
v___x_177_ = lean_apply_5(v___x_12973__overap_176_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, lean_box(0));
return v___x_177_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_169_ = stack[0].m_obj;
lean_object* v___y_170_ = stack[1].m_obj;
lean_object* v___y_171_ = stack[2].m_obj;
lean_object* v___y_172_ = stack[3].m_obj;
lean_object* v___y_173_ = stack[4].m_obj;
lean_object* v_res_178_;
v_res_178_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v_msg_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
stack->m_obj
 = v_res_178_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3___boxed(lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v_msg_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(lean_object* v_msg_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = l_Lean_instInhabitedLocalDecl_default;
v___x_188_ = lean_panic_fn_borrowed(v___x_187_, v_msg_186_);
return v___x_188_;
}
}
lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(uint8_t v_mode_190_, lean_object* v_a_u2081_191_, lean_object* v_a_u2082_192_, lean_object* v_b_u2081_193_, lean_object* v_b_u2082_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; 
lean_inc_ref(v_b_u2081_193_);
lean_inc_ref(v_a_u2081_191_);
v___x_200_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_190_, v_a_u2081_191_, v_b_u2081_193_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; uint8_t v___x_202_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v___x_202_ = lean_unbox(v_a_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v___x_203_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_190_, v_b_u2081_193_, v_a_u2081_191_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_213_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_213_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_213_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_213_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
uint8_t v___x_208_; 
v___x_208_ = lean_unbox(v_a_204_);
lean_dec(v_a_204_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_del_object(v___x_206_);
lean_dec(v_a_201_);
v___x_209_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_190_, v_a_u2082_192_, v_b_u2082_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
return v___x_209_;
}
else
{
lean_object* v___x_211_; 
lean_dec_ref(v_b_u2082_194_);
lean_dec_ref(v_a_u2082_192_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v_a_201_);
v___x_211_ = v___x_206_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_201_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
else
{
lean_dec(v_a_201_);
lean_dec_ref(v_b_u2082_194_);
lean_dec_ref(v_a_u2082_192_);
return v___x_203_;
}
}
else
{
lean_dec_ref(v_b_u2082_194_);
lean_dec_ref(v_b_u2081_193_);
lean_dec_ref(v_a_u2082_192_);
lean_dec_ref(v_a_u2081_191_);
return v___x_200_;
}
}
else
{
lean_dec_ref(v_b_u2082_194_);
lean_dec_ref(v_b_u2081_193_);
lean_dec_ref(v_a_u2082_192_);
lean_dec_ref(v_a_u2081_191_);
return v___x_200_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_190_ = stack[0].m_num;
lean_object* v_a_u2081_191_ = stack[1].m_obj;
lean_object* v_a_u2082_192_ = stack[2].m_obj;
lean_object* v_b_u2081_193_ = stack[3].m_obj;
lean_object* v_b_u2082_194_ = stack[4].m_obj;
lean_object* v_a_195_ = stack[5].m_obj;
lean_object* v_a_196_ = stack[6].m_obj;
lean_object* v_a_197_ = stack[7].m_obj;
lean_object* v_a_198_ = stack[8].m_obj;
lean_object* v_res_214_;
v_res_214_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_190_, v_a_u2081_191_, v_a_u2082_192_, v_b_u2081_193_, v_b_u2082_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
stack->m_obj
 = v_res_214_;
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__2));
v___x_219_ = lean_unsigned_to_nat(14u);
v___x_220_ = lean_unsigned_to_nat(22u);
v___x_221_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__1));
v___x_222_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__0));
v___x_223_ = l_mkPanicMessageWithDecl(v___x_222_, v___x_221_, v___x_220_, v___x_219_, v___x_218_);
return v___x_223_;
}
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0(void){
_start:
{
lean_object* v___x_224_; lean_object* v_dummy_225_; 
v___x_224_ = lean_box(0);
v_dummy_225_ = l_Lean_Expr_sort___override(v___x_224_);
return v_dummy_225_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(lean_object* v_upperBound_229_, lean_object* v_a_230_, lean_object* v___x_231_, lean_object* v___x_232_, uint8_t v_mode_233_, lean_object* v_a_234_, lean_object* v_b_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_a_242_; uint8_t v___x_246_; 
v___x_246_ = lean_nat_dec_lt(v_a_234_, v_upperBound_229_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
lean_dec(v_a_234_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v_b_235_);
return v___x_247_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v_isInstance_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref(v_b_235_);
v___x_248_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_249_ = lean_array_get_borrowed(v___x_248_, v_a_230_, v_a_234_);
v_isInstance_250_ = lean_ctor_get_uint8(v___x_249_, sizeof(void*)*1 + 4);
v___x_251_ = lean_box(0);
v___x_252_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_250_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_253_ = l_Lean_instInhabitedExpr;
v___x_254_ = lean_array_get_borrowed(v___x_253_, v___x_231_, v_a_234_);
v___x_255_ = lean_array_get_borrowed(v___x_253_, v___x_232_, v_a_234_);
lean_inc(v___x_255_);
lean_inc(v___x_254_);
v___x_256_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_233_, v___x_254_, v___x_255_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_288_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_288_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_288_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_288_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
uint8_t v___x_261_; 
v___x_261_ = lean_unbox(v_a_257_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_del_object(v___x_259_);
lean_inc(v___x_254_);
lean_inc(v___x_255_);
v___x_262_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_233_, v___x_255_, v___x_254_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_273_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_273_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
uint8_t v___x_267_; 
v___x_267_ = lean_unbox(v_a_263_);
lean_dec(v_a_263_);
if (v___x_267_ == 0)
{
lean_del_object(v___x_265_);
lean_dec(v_a_257_);
v_a_242_ = v___x_252_;
goto v___jp_241_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
lean_dec(v_a_234_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v_a_257_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_251_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_269_);
v___x_271_ = v___x_265_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec(v_a_257_);
lean_dec(v_a_234_);
v_a_274_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_262_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_262_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
lean_dec(v_a_257_);
lean_dec(v_a_234_);
v___x_282_ = lean_box(v___x_246_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_251_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_284_);
v___x_286_ = v___x_259_;
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
lean_dec(v_a_234_);
v_a_289_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_256_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_256_);
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
v_a_242_ = v___x_252_;
goto v___jp_241_;
}
}
v___jp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_a_234_, v___x_243_);
lean_dec(v_a_234_);
lean_inc_ref(v_a_242_);
v_a_234_ = v___x_244_;
v_b_235_ = v_a_242_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_229_ = stack[0].m_obj;
lean_object* v_a_230_ = stack[1].m_obj;
lean_object* v___x_231_ = stack[2].m_obj;
lean_object* v___x_232_ = stack[3].m_obj;
uint8_t v_mode_233_ = stack[4].m_num;
lean_object* v_a_234_ = stack[5].m_obj;
lean_object* v_b_235_ = stack[6].m_obj;
lean_object* v___y_236_ = stack[7].m_obj;
lean_object* v___y_237_ = stack[8].m_obj;
lean_object* v___y_238_ = stack[9].m_obj;
lean_object* v___y_239_ = stack[10].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_229_, v_a_230_, v___x_231_, v___x_232_, v_mode_233_, v_a_234_, v_b_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
stack->m_obj
 = v_res_297_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(lean_object* v_upperBound_298_, lean_object* v___x_299_, lean_object* v___x_300_, uint8_t v_mode_301_, lean_object* v_a_302_, lean_object* v_b_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
uint8_t v___x_309_; 
v___x_309_ = lean_nat_dec_lt(v_a_302_, v_upperBound_298_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
lean_dec(v_a_302_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v_b_303_);
return v___x_310_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec_ref(v_b_303_);
v___x_311_ = l_Lean_instInhabitedExpr;
v___x_312_ = lean_box(0);
v___x_313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_314_ = lean_array_get_borrowed(v___x_311_, v___x_299_, v_a_302_);
v___x_315_ = lean_array_get_borrowed(v___x_311_, v___x_300_, v_a_302_);
lean_inc(v___x_315_);
lean_inc(v___x_314_);
v___x_316_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_301_, v___x_314_, v___x_315_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_351_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_351_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_351_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_351_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint8_t v___x_321_; 
v___x_321_ = lean_unbox(v_a_317_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_del_object(v___x_319_);
lean_inc(v___x_314_);
lean_inc(v___x_315_);
v___x_322_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_301_, v___x_315_, v___x_314_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_336_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_336_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_336_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_336_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
uint8_t v___x_327_; 
v___x_327_ = lean_unbox(v_a_323_);
lean_dec(v_a_323_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_del_object(v___x_325_);
lean_dec(v_a_317_);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_a_302_, v___x_328_);
lean_dec(v_a_302_);
v_a_302_ = v___x_329_;
v_b_303_ = v___x_313_;
goto _start;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
lean_dec(v_a_302_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v_a_317_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_312_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_332_);
v___x_334_ = v___x_325_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v_a_317_);
lean_dec(v_a_302_);
v_a_337_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_322_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_322_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
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
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
lean_dec(v_a_317_);
lean_dec(v_a_302_);
v___x_345_ = lean_box(v___x_309_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_312_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_347_);
v___x_349_ = v___x_319_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
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
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_a_302_);
v_a_352_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_316_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_316_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_298_ = stack[0].m_obj;
lean_object* v___x_299_ = stack[1].m_obj;
lean_object* v___x_300_ = stack[2].m_obj;
uint8_t v_mode_301_ = stack[3].m_num;
lean_object* v_a_302_ = stack[4].m_obj;
lean_object* v_b_303_ = stack[5].m_obj;
lean_object* v___y_304_ = stack[6].m_obj;
lean_object* v___y_305_ = stack[7].m_obj;
lean_object* v___y_306_ = stack[8].m_obj;
lean_object* v___y_307_ = stack[9].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_298_, v___x_299_, v___x_300_, v_mode_301_, v_a_302_, v_b_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
stack->m_obj
 = v_res_360_;
}
lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(uint8_t v_mode_361_, lean_object* v_a_362_, lean_object* v_b_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_aFn_369_; lean_object* v_bFn_370_; lean_object* v___x_371_; 
v_aFn_369_ = l_Lean_Expr_getAppFn(v_a_362_);
v_bFn_370_ = l_Lean_Expr_getAppFn(v_b_363_);
lean_inc_ref(v_bFn_370_);
lean_inc_ref(v_aFn_369_);
v___x_371_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_361_, v_aFn_369_, v_bFn_370_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_469_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_469_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_469_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_469_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
uint8_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 1;
v___x_377_ = lean_unbox(v_a_372_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_del_object(v___x_374_);
lean_inc_ref(v_aFn_369_);
v___x_378_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_361_, v_bFn_370_, v_aFn_369_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_464_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_464_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_464_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_464_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint8_t v___x_383_; 
v___x_383_ = lean_unbox(v_a_379_);
lean_dec(v_a_379_);
if (v___x_383_ == 0)
{
lean_object* v_dummy_384_; lean_object* v_nargs_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v_nargs_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
lean_dec(v_a_372_);
v_dummy_384_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_385_ = l_Lean_Expr_getAppNumArgs(v_a_362_);
lean_inc(v_nargs_385_);
v___x_386_ = lean_mk_array(v_nargs_385_, v_dummy_384_);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_sub(v_nargs_385_, v___x_387_);
lean_dec(v_nargs_385_);
v___x_389_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_362_, v___x_386_, v___x_388_);
v_nargs_390_ = l_Lean_Expr_getAppNumArgs(v_b_363_);
lean_inc(v_nargs_390_);
v___x_391_ = lean_mk_array(v_nargs_390_, v_dummy_384_);
v___x_392_ = lean_nat_sub(v_nargs_390_, v___x_387_);
lean_dec(v_nargs_390_);
v___x_393_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_b_363_, v___x_391_, v___x_392_);
v___x_394_ = lean_array_get_size(v___x_389_);
v___x_395_ = lean_array_get_size(v___x_393_);
v___x_396_ = lean_nat_dec_lt(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_394_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_del_object(v___x_381_);
v___x_398_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_aFn_369_, v___x_394_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = lean_array_get_size(v_a_399_);
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_403_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v___x_400_, v_a_399_, v___x_389_, v___x_393_, v_mode_361_, v___x_401_, v___x_402_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v_a_399_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_436_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_436_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_436_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_436_;
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
lean_object* v___x_409_; 
lean_del_object(v___x_406_);
v___x_409_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v___x_394_, v___x_389_, v___x_393_, v_mode_361_, v___x_400_, v___x_402_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
lean_dec_ref(v___x_393_);
lean_dec_ref(v___x_389_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_423_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_423_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_423_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_423_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_fst_414_; 
v_fst_414_ = lean_ctor_get(v_a_410_, 0);
lean_inc(v_fst_414_);
lean_dec(v_a_410_);
if (lean_obj_tag(v_fst_414_) == 0)
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = lean_box(v___x_397_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_415_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
else
{
lean_object* v_val_419_; lean_object* v___x_421_; 
v_val_419_ = lean_ctor_get(v_fst_414_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_fst_414_, 1);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v_val_419_);
v___x_421_ = v___x_412_;
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
v_a_424_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_409_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_409_);
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
lean_object* v_val_432_; lean_object* v___x_434_; 
lean_dec_ref(v___x_393_);
lean_dec_ref(v___x_389_);
v_val_432_ = lean_ctor_get(v_fst_408_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v_fst_408_, 1);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_val_432_);
v___x_434_ = v___x_406_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_val_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec_ref(v___x_393_);
lean_dec_ref(v___x_389_);
v_a_437_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_403_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_403_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v___x_393_);
lean_dec_ref(v___x_389_);
v_a_445_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_398_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_398_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
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
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec_ref(v___x_393_);
lean_dec_ref(v___x_389_);
lean_dec_ref(v_aFn_369_);
v___x_453_ = lean_box(v___x_396_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_453_);
v___x_455_ = v___x_381_;
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
else
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec_ref(v___x_393_);
lean_dec_ref(v___x_389_);
lean_dec_ref(v_aFn_369_);
v___x_457_ = lean_box(v___x_376_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_457_);
v___x_459_ = v___x_381_;
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
else
{
lean_object* v___x_462_; 
lean_dec_ref(v_aFn_369_);
lean_dec_ref(v_b_363_);
lean_dec_ref(v_a_362_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v_a_372_);
v___x_462_ = v___x_381_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_372_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_dec(v_a_372_);
lean_dec_ref(v_aFn_369_);
lean_dec_ref(v_b_363_);
lean_dec_ref(v_a_362_);
return v___x_378_;
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_467_; 
lean_dec(v_a_372_);
lean_dec_ref(v_bFn_370_);
lean_dec_ref(v_aFn_369_);
lean_dec_ref(v_b_363_);
lean_dec_ref(v_a_362_);
v___x_465_ = lean_box(v___x_376_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_465_);
v___x_467_ = v___x_374_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_dec_ref(v_bFn_370_);
lean_dec_ref(v_aFn_369_);
lean_dec_ref(v_b_363_);
lean_dec_ref(v_a_362_);
return v___x_371_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_361_ = stack[0].m_num;
lean_object* v_a_362_ = stack[1].m_obj;
lean_object* v_b_363_ = stack[2].m_obj;
lean_object* v_a_364_ = stack[3].m_obj;
lean_object* v_a_365_ = stack[4].m_obj;
lean_object* v_a_366_ = stack[5].m_obj;
lean_object* v_a_367_ = stack[6].m_obj;
lean_object* v_res_470_;
v_res_470_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_361_, v_a_362_, v_b_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
stack->m_obj
 = v_res_470_;
}
static lean_object* _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_474_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__6));
v___x_475_ = lean_unsigned_to_nat(27u);
v___x_476_ = lean_unsigned_to_nat(152u);
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__5));
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__4));
v___x_479_ = l_mkPanicMessageWithDecl(v___x_478_, v___x_477_, v___x_476_, v___x_475_, v___x_474_);
return v___x_479_;
}
}
lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(uint8_t v_mode_480_, lean_object* v_a_481_, lean_object* v_b_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_d_489_; lean_object* v_e_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; 
switch(lean_obj_tag(v_a_481_))
{
case 0:
{
lean_object* v_deBruijnIndex_498_; lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_deBruijnIndex_498_ = lean_ctor_get(v_a_481_, 0);
lean_inc(v_deBruijnIndex_498_);
lean_dec_ref_known(v_a_481_, 1);
v___x_499_ = l_Lean_Expr_bvarIdx_x21(v_b_482_);
lean_dec_ref(v_b_482_);
v___x_500_ = lean_nat_dec_lt(v_deBruijnIndex_498_, v___x_499_);
lean_dec(v___x_499_);
lean_dec(v_deBruijnIndex_498_);
v___x_501_ = lean_box(v___x_500_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
case 1:
{
lean_object* v_fvarId_503_; lean_object* v___x_504_; 
v_fvarId_503_ = lean_ctor_get(v_a_481_, 0);
lean_inc(v_fvarId_503_);
lean_dec_ref_known(v_a_481_, 1);
v___x_504_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_503_, v_a_483_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = l_Lean_Expr_fvarId_x21(v_b_482_);
lean_dec_ref(v_b_482_);
v___x_507_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_506_, v_a_483_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_530_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_530_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_530_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_530_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_522_; 
if (lean_obj_tag(v_a_505_) == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_528_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_527_);
v___y_522_ = v___x_528_;
goto v___jp_521_;
}
else
{
lean_object* v_val_529_; 
v_val_529_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v_a_505_, 1);
v___y_522_ = v_val_529_;
goto v___jp_521_;
}
v___jp_512_:
{
lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_515_ = l_Lean_LocalDecl_index(v___y_514_);
lean_dec_ref(v___y_514_);
v___x_516_ = lean_nat_dec_lt(v___y_513_, v___x_515_);
lean_dec(v___x_515_);
lean_dec(v___y_513_);
v___x_517_ = lean_box(v___x_516_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_517_);
v___x_519_ = v___x_510_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
v___jp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_LocalDecl_index(v___y_522_);
lean_dec_ref(v___y_522_);
if (lean_obj_tag(v_a_508_) == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__3);
v___x_525_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__2(v___x_524_);
v___y_513_ = v___x_523_;
v___y_514_ = v___x_525_;
goto v___jp_512_;
}
else
{
lean_object* v_val_526_; 
v_val_526_ = lean_ctor_get(v_a_508_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v_a_508_, 1);
v___y_513_ = v___x_523_;
v___y_514_ = v_val_526_;
goto v___jp_512_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_505_);
v_a_531_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_507_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_507_);
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
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref(v_b_482_);
v_a_539_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_504_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_504_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_mvarId_547_ = lean_ctor_get(v_a_481_, 0);
lean_inc(v_mvarId_547_);
lean_dec_ref_known(v_a_481_, 1);
v___x_548_ = l_Lean_Expr_mvarId_x21(v_b_482_);
lean_dec_ref(v_b_482_);
v___x_549_ = l_Lean_Name_lt(v_mvarId_547_, v___x_548_);
lean_dec(v___x_548_);
lean_dec(v_mvarId_547_);
v___x_550_ = lean_box(v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
case 3:
{
lean_object* v_u_552_; lean_object* v___x_553_; uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_u_552_ = lean_ctor_get(v_a_481_, 0);
lean_inc(v_u_552_);
lean_dec_ref_known(v_a_481_, 1);
v___x_553_ = l_Lean_Expr_sortLevel_x21(v_b_482_);
lean_dec_ref(v_b_482_);
v___x_554_ = l_Lean_Level_normLt(v_u_552_, v___x_553_);
lean_dec(v___x_553_);
lean_dec(v_u_552_);
v___x_555_ = lean_box(v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
case 4:
{
lean_object* v_declName_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_declName_557_ = lean_ctor_get(v_a_481_, 0);
lean_inc(v_declName_557_);
lean_dec_ref_known(v_a_481_, 2);
v___x_558_ = l_Lean_Expr_constName_x21(v_b_482_);
lean_dec_ref(v_b_482_);
v___x_559_ = l_Lean_Name_lt(v_declName_557_, v___x_558_);
lean_dec(v___x_558_);
lean_dec(v_declName_557_);
v___x_560_ = lean_box(v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
case 5:
{
lean_object* v___x_562_; 
v___x_562_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_480_, v_a_481_, v_b_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_562_;
}
case 8:
{
lean_object* v_value_563_; lean_object* v_body_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_value_563_ = lean_ctor_get(v_a_481_, 2);
lean_inc_ref(v_value_563_);
v_body_564_ = lean_ctor_get(v_a_481_, 3);
lean_inc_ref(v_body_564_);
lean_dec_ref_known(v_a_481_, 4);
v___x_565_ = l_Lean_Expr_letValue_x21(v_b_482_);
v___x_566_ = l_Lean_Expr_letBody_x21(v_b_482_);
lean_dec_ref(v_b_482_);
v___x_567_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_480_, v_value_563_, v_body_564_, v___x_565_, v___x_566_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_567_;
}
case 9:
{
lean_object* v_a_568_; lean_object* v___x_569_; uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_a_568_ = lean_ctor_get(v_a_481_, 0);
lean_inc_ref(v_a_568_);
lean_dec_ref_known(v_a_481_, 1);
v___x_569_ = l_Lean_Expr_litValue_x21(v_b_482_);
lean_dec_ref(v_b_482_);
v___x_570_ = l_Lean_Literal_lt(v_a_568_, v___x_569_);
lean_dec_ref(v___x_569_);
lean_dec_ref(v_a_568_);
v___x_571_ = lean_box(v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
case 10:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref_known(v_a_481_, 2);
lean_dec_ref(v_b_482_);
v___x_573_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___closed__7);
v___x_574_ = l_panic___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_spec__3(v___x_573_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_574_;
}
case 11:
{
lean_object* v_idx_575_; lean_object* v_struct_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_idx_575_ = lean_ctor_get(v_a_481_, 1);
lean_inc(v_idx_575_);
v_struct_576_ = lean_ctor_get(v_a_481_, 2);
lean_inc_ref(v_struct_576_);
lean_dec_ref_known(v_a_481_, 3);
v___x_577_ = l_Lean_Expr_projIdx_x21(v_b_482_);
v___x_578_ = lean_nat_dec_eq(v_idx_575_, v___x_577_);
if (v___x_578_ == 0)
{
uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec_ref(v_struct_576_);
lean_dec_ref(v_b_482_);
v___x_579_ = lean_nat_dec_lt(v_idx_575_, v___x_577_);
lean_dec(v___x_577_);
lean_dec(v_idx_575_);
v___x_580_ = lean_box(v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v___x_577_);
lean_dec(v_idx_575_);
v___x_582_ = l_Lean_Expr_projExpr_x21(v_b_482_);
lean_dec_ref(v_b_482_);
v___x_583_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_480_, v_struct_576_, v___x_582_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_583_;
}
}
default: 
{
lean_object* v_binderType_584_; lean_object* v_body_585_; 
v_binderType_584_ = lean_ctor_get(v_a_481_, 1);
lean_inc_ref(v_binderType_584_);
v_body_585_ = lean_ctor_get(v_a_481_, 2);
lean_inc_ref(v_body_585_);
lean_dec_ref(v_a_481_);
v_d_489_ = v_binderType_584_;
v_e_490_ = v_body_585_;
v___y_491_ = v_a_483_;
v___y_492_ = v_a_484_;
v___y_493_ = v_a_485_;
v___y_494_ = v_a_486_;
goto v___jp_488_;
}
}
v___jp_488_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = l_Lean_Expr_bindingDomain_x21(v_b_482_);
v___x_496_ = l_Lean_Expr_bindingBody_x21(v_b_482_);
lean_dec_ref(v_b_482_);
v___x_497_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_480_, v_d_489_, v_e_490_, v___x_495_, v___x_496_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
return v___x_497_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_480_ = stack[0].m_num;
lean_object* v_a_481_ = stack[1].m_obj;
lean_object* v_b_482_ = stack[2].m_obj;
lean_object* v_a_483_ = stack[3].m_obj;
lean_object* v_a_484_ = stack[4].m_obj;
lean_object* v_a_485_ = stack[5].m_obj;
lean_object* v_a_486_ = stack[6].m_obj;
lean_object* v_res_586_;
v_res_586_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_480_, v_a_481_, v_b_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
stack->m_obj
 = v_res_586_;
}
lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(uint8_t v_mode_587_, lean_object* v_a_588_, lean_object* v_b_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___closed__0));
v___x_596_ = l_Lean_Core_checkSystem(v___x_595_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v___x_597_; 
lean_dec_ref_known(v___x_596_, 1);
lean_inc_ref(v_a_588_);
lean_inc_ref(v_b_589_);
v___x_597_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_587_, v_b_589_, v_a_588_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; uint8_t v___x_599_; uint8_t v___x_600_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v___x_599_ = 1;
v___x_600_ = lean_unbox(v_a_598_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; uint8_t v___x_602_; uint8_t v___x_603_; 
v___x_601_ = l_Lean_Expr_ctorWeight(v_b_589_);
v___x_602_ = l_Lean_Expr_ctorWeight(v_a_588_);
v___x_603_ = lean_uint8_dec_lt(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
lean_dec_ref_known(v___x_597_, 1);
lean_inc_ref(v_b_589_);
lean_inc_ref(v_a_588_);
v___x_604_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_587_, v_a_588_, v_b_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_620_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_620_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = lean_unbox(v_a_605_);
lean_dec(v_a_605_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_612_; 
lean_dec_ref(v_b_589_);
lean_dec_ref(v_a_588_);
v___x_610_ = lean_box(v___x_603_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_610_);
v___x_612_ = v___x_607_;
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
else
{
uint8_t v___x_614_; 
v___x_614_ = lean_uint8_dec_lt(v___x_602_, v___x_601_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_del_object(v___x_607_);
v___x_615_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_587_, v_a_588_, v_b_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_618_; 
lean_dec_ref(v_b_589_);
lean_dec_ref(v_a_588_);
v___x_616_ = lean_box(v___x_599_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_616_);
v___x_618_ = v___x_607_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
else
{
lean_dec_ref(v_b_589_);
lean_dec_ref(v_a_588_);
return v___x_604_;
}
}
else
{
lean_dec_ref(v_b_589_);
lean_dec_ref(v_a_588_);
return v___x_597_;
}
}
else
{
lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_b_589_);
lean_dec_ref(v_a_588_);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v___x_597_, 0);
lean_dec(v_unused_629_);
v___x_622_ = v___x_597_;
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
else
{
lean_dec(v___x_597_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_624_ = lean_box(v___x_599_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_624_);
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_dec_ref(v_b_589_);
lean_dec_ref(v_a_588_);
return v___x_597_;
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_b_589_);
lean_dec_ref(v_a_588_);
v_a_630_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_596_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_596_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_587_ = stack[0].m_num;
lean_object* v_a_588_ = stack[1].m_obj;
lean_object* v_b_589_ = stack[2].m_obj;
lean_object* v_a_590_ = stack[3].m_obj;
lean_object* v_a_591_ = stack[4].m_obj;
lean_object* v_a_592_ = stack[5].m_obj;
lean_object* v_a_593_ = stack[6].m_obj;
lean_object* v_res_638_;
v_res_638_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_587_, v_a_588_, v_b_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
stack->m_obj
 = v_res_638_;
}
lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(uint8_t v_mode_639_, lean_object* v_a_640_, lean_object* v_b_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = lean_expr_eqv(v_a_640_, v_b_641_);
if (v___x_647_ == 0)
{
uint8_t v___x_648_; 
v___x_648_ = l_Lean_Expr_isMData(v_a_640_);
if (v___x_648_ == 0)
{
uint8_t v___x_649_; 
v___x_649_ = l_Lean_Expr_isMData(v_b_641_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_639_, v_a_640_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_reduce(v_mode_639_, v_b_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_639_, v_a_651_, v_a_653_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
return v___x_654_;
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec(v_a_651_);
v_a_655_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_652_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_652_);
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
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v_b_641_);
v_a_663_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_650_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_650_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Expr_mdataExpr_x21(v_b_641_);
lean_dec_ref(v_b_641_);
v_b_641_ = v___x_671_;
goto _start;
}
}
else
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Expr_mdataExpr_x21(v_a_640_);
lean_dec_ref(v_a_640_);
v_a_640_ = v___x_673_;
goto _start;
}
}
else
{
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec_ref(v_b_641_);
lean_dec_ref(v_a_640_);
v___x_675_ = 0;
v___x_676_ = lean_box(v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_639_ = stack[0].m_num;
lean_object* v_a_640_ = stack[1].m_obj;
lean_object* v_b_641_ = stack[2].m_obj;
lean_object* v_a_642_ = stack[3].m_obj;
lean_object* v_a_643_ = stack[4].m_obj;
lean_object* v_a_644_ = stack[5].m_obj;
lean_object* v_a_645_ = stack[6].m_obj;
lean_object* v_res_678_;
v_res_678_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_639_, v_a_640_, v_b_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
stack->m_obj
 = v_res_678_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(lean_object* v_upperBound_679_, lean_object* v_a_680_, lean_object* v_args_681_, uint8_t v_mode_682_, lean_object* v_b_683_, lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_a_692_; uint8_t v___x_696_; 
v___x_696_ = lean_nat_dec_lt(v_a_684_, v_upperBound_679_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
lean_dec(v_a_684_);
lean_dec_ref(v_b_683_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v_b_685_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v_isInstance_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec_ref(v_b_685_);
v___x_698_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_699_ = lean_array_get_borrowed(v___x_698_, v_a_680_, v_a_684_);
v_isInstance_700_ = lean_ctor_get_uint8(v___x_699_, sizeof(void*)*1 + 4);
v___x_701_ = lean_box(0);
v___x_702_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
if (v_isInstance_700_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = l_Lean_instInhabitedExpr;
v___x_704_ = lean_array_get_borrowed(v___x_703_, v_args_681_, v_a_684_);
lean_inc_ref(v_b_683_);
lean_inc(v___x_704_);
v___x_705_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_682_, v___x_704_, v_b_683_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_716_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_716_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_716_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_716_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
uint8_t v___x_710_; 
v___x_710_ = lean_unbox(v_a_706_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
lean_dec(v_a_684_);
lean_dec_ref(v_b_683_);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v_a_706_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_701_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_712_);
v___x_714_ = v___x_708_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
else
{
lean_del_object(v___x_708_);
lean_dec(v_a_706_);
v_a_692_ = v___x_702_;
goto v___jp_691_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_a_684_);
lean_dec_ref(v_b_683_);
v_a_717_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_705_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_705_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
v_a_692_ = v___x_702_;
goto v___jp_691_;
}
}
v___jp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_add(v_a_684_, v___x_693_);
lean_dec(v_a_684_);
lean_inc_ref(v_a_692_);
v_a_684_ = v___x_694_;
v_b_685_ = v_a_692_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_679_ = stack[0].m_obj;
lean_object* v_a_680_ = stack[1].m_obj;
lean_object* v_args_681_ = stack[2].m_obj;
uint8_t v_mode_682_ = stack[3].m_num;
lean_object* v_b_683_ = stack[4].m_obj;
lean_object* v_a_684_ = stack[5].m_obj;
lean_object* v_b_685_ = stack[6].m_obj;
lean_object* v___y_686_ = stack[7].m_obj;
lean_object* v___y_687_ = stack[8].m_obj;
lean_object* v___y_688_ = stack[9].m_obj;
lean_object* v___y_689_ = stack[10].m_obj;
lean_object* v_res_725_;
v_res_725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_679_, v_a_680_, v_args_681_, v_mode_682_, v_b_683_, v_a_684_, v_b_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
stack->m_obj
 = v_res_725_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(lean_object* v_upperBound_726_, lean_object* v_args_727_, uint8_t v_mode_728_, lean_object* v_b_729_, lean_object* v_a_730_, lean_object* v_b_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = lean_nat_dec_lt(v_a_730_, v_upperBound_726_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v_a_730_);
lean_dec_ref(v_b_729_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v_b_731_);
return v___x_738_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec_ref(v_b_731_);
v___x_739_ = lean_box(0);
v___x_740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
v___x_741_ = lean_array_fget_borrowed(v_args_727_, v_a_730_);
lean_inc_ref(v_b_729_);
lean_inc(v___x_741_);
v___x_742_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_728_, v___x_741_, v_b_729_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_756_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_756_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_756_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_756_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v___x_747_; 
v___x_747_ = lean_unbox(v_a_743_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
lean_dec(v_a_730_);
lean_dec_ref(v_b_729_);
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v_a_743_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_739_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_749_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_del_object(v___x_745_);
lean_dec(v_a_743_);
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_a_730_, v___x_753_);
lean_dec(v_a_730_);
v_a_730_ = v___x_754_;
v_b_731_ = v___x_740_;
goto _start;
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_a_730_);
lean_dec_ref(v_b_729_);
v_a_757_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_742_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_742_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_726_ = stack[0].m_obj;
lean_object* v_args_727_ = stack[1].m_obj;
uint8_t v_mode_728_ = stack[2].m_num;
lean_object* v_b_729_ = stack[3].m_obj;
lean_object* v_a_730_ = stack[4].m_obj;
lean_object* v_b_731_ = stack[5].m_obj;
lean_object* v___y_732_ = stack[6].m_obj;
lean_object* v___y_733_ = stack[7].m_obj;
lean_object* v___y_734_ = stack[8].m_obj;
lean_object* v___y_735_ = stack[9].m_obj;
lean_object* v_res_765_;
v_res_765_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_726_, v_args_727_, v_mode_728_, v_b_729_, v_a_730_, v_b_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
stack->m_obj
 = v_res_765_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(uint8_t v_mode_766_, lean_object* v_b_767_, lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
if (lean_obj_tag(v_x_768_) == 5)
{
lean_object* v_fn_776_; lean_object* v_arg_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_fn_776_ = lean_ctor_get(v_x_768_, 0);
lean_inc_ref(v_fn_776_);
v_arg_777_ = lean_ctor_get(v_x_768_, 1);
lean_inc_ref(v_arg_777_);
lean_dec_ref_known(v_x_768_, 2);
v___x_778_ = lean_array_set(v_x_769_, v_x_770_, v_arg_777_);
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_sub(v_x_770_, v___x_779_);
lean_dec(v_x_770_);
v_x_768_ = v_fn_776_;
v_x_769_ = v___x_778_;
v_x_770_ = v___x_780_;
goto _start;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v_x_770_);
v___x_782_ = lean_array_get_size(v_x_769_);
v___x_783_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_getParamsInfo(v_x_768_, v___x_782_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_785_ = lean_array_get_size(v_a_784_);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___closed__0));
lean_inc_ref(v_b_767_);
v___x_788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v___x_785_, v_a_784_, v_x_769_, v_mode_766_, v_b_767_, v___x_786_, v___x_787_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v_a_784_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_822_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_822_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_822_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_822_;
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
lean_object* v___x_794_; 
lean_del_object(v___x_791_);
v___x_794_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v___x_782_, v_x_769_, v_mode_766_, v_b_767_, v___x_785_, v___x_787_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec_ref(v_x_769_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_809_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_809_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_fst_799_; 
v_fst_799_ = lean_ctor_get(v_a_795_, 0);
lean_inc(v_fst_799_);
lean_dec(v_a_795_);
if (lean_obj_tag(v_fst_799_) == 0)
{
uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_800_ = 1;
v___x_801_ = lean_box(v___x_800_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_801_);
v___x_803_ = v___x_797_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
else
{
lean_object* v_val_805_; lean_object* v___x_807_; 
v_val_805_ = lean_ctor_get(v_fst_799_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v_fst_799_, 1);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v_val_805_);
v___x_807_ = v___x_797_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_val_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_a_810_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_794_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_794_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_val_818_; lean_object* v___x_820_; 
lean_dec_ref(v_x_769_);
lean_dec_ref(v_b_767_);
v_val_818_ = lean_ctor_get(v_fst_793_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v_fst_793_, 1);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_val_818_);
v___x_820_ = v___x_791_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_val_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v_x_769_);
lean_dec_ref(v_b_767_);
v_a_823_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_788_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_788_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_x_769_);
lean_dec_ref(v_b_767_);
v_a_831_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_783_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_783_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
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
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_766_ = stack[0].m_num;
lean_object* v_b_767_ = stack[1].m_obj;
lean_object* v_x_768_ = stack[2].m_obj;
lean_object* v_x_769_ = stack[3].m_obj;
lean_object* v_x_770_ = stack[4].m_obj;
lean_object* v___y_771_ = stack[5].m_obj;
lean_object* v___y_772_ = stack[6].m_obj;
lean_object* v___y_773_ = stack[7].m_obj;
lean_object* v___y_774_ = stack[8].m_obj;
lean_object* v_res_839_;
v_res_839_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_766_, v_b_767_, v_x_768_, v_x_769_, v_x_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
stack->m_obj
 = v_res_839_;
}
lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(uint8_t v_mode_840_, lean_object* v_a_841_, lean_object* v_b_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_d_849_; lean_object* v_e_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; 
switch(lean_obj_tag(v_a_841_))
{
case 11:
{
lean_object* v_struct_859_; lean_object* v___x_860_; 
v_struct_859_ = lean_ctor_get(v_a_841_, 2);
lean_inc_ref(v_struct_859_);
lean_dec_ref_known(v_a_841_, 3);
v___x_860_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_840_, v_struct_859_, v_b_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_860_;
}
case 5:
{
lean_object* v_dummy_861_; lean_object* v_nargs_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_dummy_861_ = lean_obj_once(&l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0, &l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0_once, _init_l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___closed__0);
v_nargs_862_ = l_Lean_Expr_getAppNumArgs(v_a_841_);
lean_inc(v_nargs_862_);
v___x_863_ = lean_mk_array(v_nargs_862_, v_dummy_861_);
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_nat_sub(v_nargs_862_, v___x_864_);
lean_dec(v_nargs_862_);
v___x_866_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_840_, v_b_842_, v_a_841_, v___x_863_, v___x_865_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_866_;
}
case 6:
{
lean_object* v_binderType_867_; lean_object* v_body_868_; 
v_binderType_867_ = lean_ctor_get(v_a_841_, 1);
lean_inc_ref(v_binderType_867_);
v_body_868_ = lean_ctor_get(v_a_841_, 2);
lean_inc_ref(v_body_868_);
lean_dec_ref_known(v_a_841_, 3);
v_d_849_ = v_binderType_867_;
v_e_850_ = v_body_868_;
v___y_851_ = v_a_843_;
v___y_852_ = v_a_844_;
v___y_853_ = v_a_845_;
v___y_854_ = v_a_846_;
goto v___jp_848_;
}
case 7:
{
lean_object* v_binderType_869_; lean_object* v_body_870_; 
v_binderType_869_ = lean_ctor_get(v_a_841_, 1);
lean_inc_ref(v_binderType_869_);
v_body_870_ = lean_ctor_get(v_a_841_, 2);
lean_inc_ref(v_body_870_);
lean_dec_ref_known(v_a_841_, 3);
v_d_849_ = v_binderType_869_;
v_e_850_ = v_body_870_;
v___y_851_ = v_a_843_;
v___y_852_ = v_a_844_;
v___y_853_ = v_a_845_;
v___y_854_ = v_a_846_;
goto v___jp_848_;
}
case 8:
{
lean_object* v_value_871_; lean_object* v_body_872_; lean_object* v___x_873_; 
v_value_871_ = lean_ctor_get(v_a_841_, 2);
lean_inc_ref(v_value_871_);
v_body_872_ = lean_ctor_get(v_a_841_, 3);
lean_inc_ref(v_body_872_);
lean_dec_ref_known(v_a_841_, 4);
lean_inc_ref(v_b_842_);
v___x_873_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_840_, v_value_871_, v_b_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; uint8_t v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v___x_875_ = lean_unbox(v_a_874_);
if (v___x_875_ == 0)
{
lean_dec_ref(v_body_872_);
lean_dec_ref(v_b_842_);
return v___x_873_;
}
else
{
lean_object* v___x_876_; 
lean_dec_ref_known(v___x_873_, 1);
v___x_876_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_840_, v_body_872_, v_b_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_876_;
}
}
else
{
lean_dec_ref(v_body_872_);
lean_dec_ref(v_b_842_);
return v___x_873_;
}
}
default: 
{
uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec_ref(v_b_842_);
lean_dec_ref(v_a_841_);
v___x_877_ = 1;
v___x_878_ = lean_box(v___x_877_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
v___jp_848_:
{
lean_object* v___x_855_; 
lean_inc_ref(v_b_842_);
v___x_855_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_840_, v_d_849_, v_b_842_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; uint8_t v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v___x_857_ = lean_unbox(v_a_856_);
if (v___x_857_ == 0)
{
lean_dec_ref(v_e_850_);
lean_dec_ref(v_b_842_);
return v___x_855_;
}
else
{
lean_object* v___x_858_; 
lean_dec_ref_known(v___x_855_, 1);
v___x_858_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_840_, v_e_850_, v_b_842_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
return v___x_858_;
}
}
else
{
lean_dec_ref(v_e_850_);
lean_dec_ref(v_b_842_);
return v___x_855_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_840_ = stack[0].m_num;
lean_object* v_a_841_ = stack[1].m_obj;
lean_object* v_b_842_ = stack[2].m_obj;
lean_object* v_a_843_ = stack[3].m_obj;
lean_object* v_a_844_ = stack[4].m_obj;
lean_object* v_a_845_ = stack[5].m_obj;
lean_object* v_a_846_ = stack[6].m_obj;
lean_object* v_res_880_;
v_res_880_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_840_, v_a_841_, v_b_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
stack->m_obj
 = v_res_880_;
}
lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(uint8_t v_mode_881_, lean_object* v_a_882_, lean_object* v_b_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_881_, v_a_882_, v_b_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_905_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_905_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_905_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_905_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = lean_unbox(v_a_890_);
lean_dec(v_a_890_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_895_ = 1;
v___x_896_ = lean_box(v___x_895_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_896_);
v___x_898_ = v___x_892_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_900_ = 0;
v___x_901_ = lean_box(v___x_900_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_901_);
v___x_903_ = v___x_892_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
return v___x_889_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_881_ = stack[0].m_num;
lean_object* v_a_882_ = stack[1].m_obj;
lean_object* v_b_883_ = stack[2].m_obj;
lean_object* v_a_884_ = stack[3].m_obj;
lean_object* v_a_885_ = stack[4].m_obj;
lean_object* v_a_886_ = stack[5].m_obj;
lean_object* v_a_887_ = stack[6].m_obj;
lean_object* v_res_906_;
v_res_906_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_881_, v_a_882_, v_b_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe___boxed(lean_object* v_mode_907_, lean_object* v_a_908_, lean_object* v_b_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
uint8_t v_mode_boxed_915_; lean_object* v_res_916_; 
v_mode_boxed_915_ = lean_unbox(v_mode_907_);
v_res_916_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_someChildGe(v_mode_boxed_915_, v_a_908_, v_b_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair___boxed(lean_object* v_mode_917_, lean_object* v_a_u2081_918_, lean_object* v_a_u2082_919_, lean_object* v_b_u2081_920_, lean_object* v_b_u2082_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
uint8_t v_mode_boxed_927_; lean_object* v_res_928_; 
v_mode_boxed_927_ = lean_unbox(v_mode_917_);
v_res_928_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltPair(v_mode_boxed_927_, v_a_u2081_918_, v_a_u2082_919_, v_b_u2081_920_, v_b_u2082_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg___boxed(lean_object* v_upperBound_929_, lean_object* v_args_930_, lean_object* v_mode_931_, lean_object* v_b_932_, lean_object* v_a_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
uint8_t v_mode_boxed_940_; lean_object* v_res_941_; 
v_mode_boxed_940_ = lean_unbox(v_mode_931_);
v_res_941_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_929_, v_args_930_, v_mode_boxed_940_, v_b_932_, v_a_933_, v_b_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_args_930_);
lean_dec(v_upperBound_929_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt___boxed(lean_object* v_mode_942_, lean_object* v_a_943_, lean_object* v_b_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
uint8_t v_mode_boxed_950_; lean_object* v_res_951_; 
v_mode_boxed_950_ = lean_unbox(v_mode_942_);
v_res_951_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_boxed_950_, v_a_943_, v_b_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg___boxed(lean_object* v_upperBound_952_, lean_object* v_a_953_, lean_object* v_args_954_, lean_object* v_mode_955_, lean_object* v_b_956_, lean_object* v_a_957_, lean_object* v_b_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
uint8_t v_mode_boxed_964_; lean_object* v_res_965_; 
v_mode_boxed_964_ = lean_unbox(v_mode_955_);
v_res_965_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_952_, v_a_953_, v_args_954_, v_mode_boxed_964_, v_b_956_, v_a_957_, v_b_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec_ref(v_args_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_upperBound_952_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt___boxed(lean_object* v_mode_966_, lean_object* v_a_967_, lean_object* v_b_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
uint8_t v_mode_boxed_974_; lean_object* v_res_975_; 
v_mode_boxed_974_ = lean_unbox(v_mode_966_);
v_res_975_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt(v_mode_boxed_974_, v_a_967_, v_b_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo___boxed(lean_object* v_mode_976_, lean_object* v_a_977_, lean_object* v_b_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
uint8_t v_mode_boxed_984_; lean_object* v_res_985_; 
v_mode_boxed_984_ = lean_unbox(v_mode_976_);
v_res_985_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lpo(v_mode_boxed_984_, v_a_977_, v_b_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg___boxed(lean_object* v_upperBound_986_, lean_object* v___x_987_, lean_object* v___x_988_, lean_object* v_mode_989_, lean_object* v_a_990_, lean_object* v_b_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v_mode_boxed_997_; lean_object* v_res_998_; 
v_mode_boxed_997_ = lean_unbox(v_mode_989_);
v_res_998_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_986_, v___x_987_, v___x_988_, v_mode_boxed_997_, v_a_990_, v_b_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v___x_988_);
lean_dec_ref(v___x_987_);
lean_dec(v_upperBound_986_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11___boxed(lean_object* v_mode_999_, lean_object* v_b_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v_mode_boxed_1009_; lean_object* v_res_1010_; 
v_mode_boxed_1009_ = lean_unbox(v_mode_999_);
v_res_1010_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__11(v_mode_boxed_1009_, v_b_1000_, v_x_1001_, v_x_1002_, v_x_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg___boxed(lean_object* v_upperBound_1011_, lean_object* v_a_1012_, lean_object* v___x_1013_, lean_object* v___x_1014_, lean_object* v_mode_1015_, lean_object* v_a_1016_, lean_object* v_b_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
uint8_t v_mode_boxed_1023_; lean_object* v_res_1024_; 
v_mode_boxed_1023_ = lean_unbox(v_mode_1015_);
v_res_1024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_1011_, v_a_1012_, v___x_1013_, v___x_1014_, v_mode_boxed_1023_, v_a_1016_, v_b_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec_ref(v___x_1014_);
lean_dec_ref(v___x_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_upperBound_1011_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp___boxed(lean_object* v_mode_1025_, lean_object* v_a_1026_, lean_object* v_b_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
uint8_t v_mode_boxed_1033_; lean_object* v_res_1034_; 
v_mode_boxed_1033_ = lean_unbox(v_mode_1025_);
v_res_1034_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp(v_mode_boxed_1033_, v_a_1026_, v_b_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor___boxed(lean_object* v_mode_1035_, lean_object* v_a_1036_, lean_object* v_b_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
uint8_t v_mode_boxed_1043_; lean_object* v_res_1044_; 
v_mode_boxed_1043_ = lean_unbox(v_mode_1035_);
v_res_1044_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lexSameCtor(v_mode_boxed_1043_, v_a_1036_, v_b_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
return v_res_1044_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(lean_object* v_upperBound_1045_, lean_object* v___x_1046_, lean_object* v___x_1047_, uint8_t v_mode_1048_, lean_object* v_inst_1049_, lean_object* v_R_1050_, lean_object* v_a_1051_, lean_object* v_b_1052_, lean_object* v_c_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___redArg(v_upperBound_1045_, v___x_1046_, v___x_1047_, v_mode_1048_, v_a_1051_, v_b_1052_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1045_ = stack[0].m_obj;
lean_object* v___x_1046_ = stack[1].m_obj;
lean_object* v___x_1047_ = stack[2].m_obj;
uint8_t v_mode_1048_ = stack[3].m_num;
lean_object* v_a_1051_ = stack[6].m_obj;
lean_object* v_b_1052_ = stack[7].m_obj;
lean_object* v___y_1054_ = stack[9].m_obj;
lean_object* v___y_1055_ = stack[10].m_obj;
lean_object* v___y_1056_ = stack[11].m_obj;
lean_object* v___y_1057_ = stack[12].m_obj;
lean_object* v_res_1060_;
v_res_1060_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_1045_, v___x_1046_, v___x_1047_, v_mode_1048_, lean_box(0), lean_box(0), v_a_1051_, v_b_1052_, lean_box(0), v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
stack->m_obj
 = v_res_1060_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6___boxed(lean_object* v_upperBound_1061_, lean_object* v___x_1062_, lean_object* v___x_1063_, lean_object* v_mode_1064_, lean_object* v_inst_1065_, lean_object* v_R_1066_, lean_object* v_a_1067_, lean_object* v_b_1068_, lean_object* v_c_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v_mode_boxed_1075_; lean_object* v_res_1076_; 
v_mode_boxed_1075_ = lean_unbox(v_mode_1064_);
v_res_1076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__6(v_upperBound_1061_, v___x_1062_, v___x_1063_, v_mode_boxed_1075_, v_inst_1065_, v_R_1066_, v_a_1067_, v_b_1068_, v_c_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v___x_1063_);
lean_dec_ref(v___x_1062_);
lean_dec(v_upperBound_1061_);
return v_res_1076_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(lean_object* v_upperBound_1077_, lean_object* v_a_1078_, lean_object* v___x_1079_, lean_object* v___x_1080_, uint8_t v_mode_1081_, lean_object* v_inst_1082_, lean_object* v_R_1083_, lean_object* v_a_1084_, lean_object* v_b_1085_, lean_object* v_c_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___redArg(v_upperBound_1077_, v_a_1078_, v___x_1079_, v___x_1080_, v_mode_1081_, v_a_1084_, v_b_1085_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1077_ = stack[0].m_obj;
lean_object* v_a_1078_ = stack[1].m_obj;
lean_object* v___x_1079_ = stack[2].m_obj;
lean_object* v___x_1080_ = stack[3].m_obj;
uint8_t v_mode_1081_ = stack[4].m_num;
lean_object* v_a_1084_ = stack[7].m_obj;
lean_object* v_b_1085_ = stack[8].m_obj;
lean_object* v___y_1087_ = stack[10].m_obj;
lean_object* v___y_1088_ = stack[11].m_obj;
lean_object* v___y_1089_ = stack[12].m_obj;
lean_object* v___y_1090_ = stack[13].m_obj;
lean_object* v_res_1093_;
v_res_1093_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_1077_, v_a_1078_, v___x_1079_, v___x_1080_, v_mode_1081_, lean_box(0), lean_box(0), v_a_1084_, v_b_1085_, lean_box(0), v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
stack->m_obj
 = v_res_1093_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7___boxed(lean_object* v_upperBound_1094_, lean_object* v_a_1095_, lean_object* v___x_1096_, lean_object* v___x_1097_, lean_object* v_mode_1098_, lean_object* v_inst_1099_, lean_object* v_R_1100_, lean_object* v_a_1101_, lean_object* v_b_1102_, lean_object* v_c_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
uint8_t v_mode_boxed_1109_; lean_object* v_res_1110_; 
v_mode_boxed_1109_ = lean_unbox(v_mode_1098_);
v_res_1110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_ltApp_spec__7(v_upperBound_1094_, v_a_1095_, v___x_1096_, v___x_1097_, v_mode_boxed_1109_, v_inst_1099_, v_R_1100_, v_a_1101_, v_b_1102_, v_c_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v___x_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_upperBound_1094_);
return v_res_1110_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(lean_object* v_upperBound_1111_, lean_object* v_args_1112_, uint8_t v_mode_1113_, lean_object* v_b_1114_, lean_object* v_inst_1115_, lean_object* v_R_1116_, lean_object* v_a_1117_, lean_object* v_b_1118_, lean_object* v_c_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___redArg(v_upperBound_1111_, v_args_1112_, v_mode_1113_, v_b_1114_, v_a_1117_, v_b_1118_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1111_ = stack[0].m_obj;
lean_object* v_args_1112_ = stack[1].m_obj;
uint8_t v_mode_1113_ = stack[2].m_num;
lean_object* v_b_1114_ = stack[3].m_obj;
lean_object* v_a_1117_ = stack[6].m_obj;
lean_object* v_b_1118_ = stack[7].m_obj;
lean_object* v___y_1120_ = stack[9].m_obj;
lean_object* v___y_1121_ = stack[10].m_obj;
lean_object* v___y_1122_ = stack[11].m_obj;
lean_object* v___y_1123_ = stack[12].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_1111_, v_args_1112_, v_mode_1113_, v_b_1114_, lean_box(0), lean_box(0), v_a_1117_, v_b_1118_, lean_box(0), v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9___boxed(lean_object* v_upperBound_1127_, lean_object* v_args_1128_, lean_object* v_mode_1129_, lean_object* v_b_1130_, lean_object* v_inst_1131_, lean_object* v_R_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_, lean_object* v_c_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v_mode_boxed_1141_; lean_object* v_res_1142_; 
v_mode_boxed_1141_ = lean_unbox(v_mode_1129_);
v_res_1142_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__9(v_upperBound_1127_, v_args_1128_, v_mode_boxed_1141_, v_b_1130_, v_inst_1131_, v_R_1132_, v_a_1133_, v_b_1134_, v_c_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec_ref(v_args_1128_);
lean_dec(v_upperBound_1127_);
return v_res_1142_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(lean_object* v_upperBound_1143_, lean_object* v_a_1144_, lean_object* v_args_1145_, uint8_t v_mode_1146_, lean_object* v_b_1147_, lean_object* v_inst_1148_, lean_object* v_R_1149_, lean_object* v_a_1150_, lean_object* v_b_1151_, lean_object* v_c_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___redArg(v_upperBound_1143_, v_a_1144_, v_args_1145_, v_mode_1146_, v_b_1147_, v_a_1150_, v_b_1151_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1143_ = stack[0].m_obj;
lean_object* v_a_1144_ = stack[1].m_obj;
lean_object* v_args_1145_ = stack[2].m_obj;
uint8_t v_mode_1146_ = stack[3].m_num;
lean_object* v_b_1147_ = stack[4].m_obj;
lean_object* v_a_1150_ = stack[7].m_obj;
lean_object* v_b_1151_ = stack[8].m_obj;
lean_object* v___y_1153_ = stack[10].m_obj;
lean_object* v___y_1154_ = stack[11].m_obj;
lean_object* v___y_1155_ = stack[12].m_obj;
lean_object* v___y_1156_ = stack[13].m_obj;
lean_object* v_res_1159_;
v_res_1159_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_1143_, v_a_1144_, v_args_1145_, v_mode_1146_, v_b_1147_, lean_box(0), lean_box(0), v_a_1150_, v_b_1151_, lean_box(0), v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
stack->m_obj
 = v_res_1159_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10___boxed(lean_object* v_upperBound_1160_, lean_object* v_a_1161_, lean_object* v_args_1162_, lean_object* v_mode_1163_, lean_object* v_b_1164_, lean_object* v_inst_1165_, lean_object* v_R_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_, lean_object* v_c_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v_mode_boxed_1175_; lean_object* v_res_1176_; 
v_mode_boxed_1175_ = lean_unbox(v_mode_1163_);
v_res_1176_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_allChildrenLt_spec__10(v_upperBound_1160_, v_a_1161_, v_args_1162_, v_mode_boxed_1175_, v_b_1164_, v_inst_1165_, v_R_1166_, v_a_1167_, v_b_1168_, v_c_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v_args_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_upperBound_1160_);
return v_res_1176_;
}
}
lean_object* l_Lean_Meta_ACLt_main(lean_object* v_a_1177_, lean_object* v_b_1178_, uint8_t v_mode_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1179_, v_a_1177_, v_b_1178_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT void l_Lean_Meta_ACLt_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1177_ = stack[0].m_obj;
lean_object* v_b_1178_ = stack[1].m_obj;
uint8_t v_mode_1179_ = stack[2].m_num;
lean_object* v_a_1180_ = stack[3].m_obj;
lean_object* v_a_1181_ = stack[4].m_obj;
lean_object* v_a_1182_ = stack[5].m_obj;
lean_object* v_a_1183_ = stack[6].m_obj;
lean_object* v_res_1186_;
v_res_1186_ = l_Lean_Meta_ACLt_main(v_a_1177_, v_b_1178_, v_mode_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
stack->m_obj
 = v_res_1186_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ACLt_main___boxed(lean_object* v_a_1187_, lean_object* v_b_1188_, lean_object* v_mode_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
uint8_t v_mode_boxed_1195_; lean_object* v_res_1196_; 
v_mode_boxed_1195_ = lean_unbox(v_mode_1189_);
v_res_1196_ = l_Lean_Meta_ACLt_main(v_a_1187_, v_b_1188_, v_mode_boxed_1195_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
return v_res_1196_;
}
}
lean_object* l_Lean_Meta_acLt(lean_object* v_a_1197_, lean_object* v_b_1198_, uint8_t v_mode_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l___private_Lean_Meta_ACLt_0__Lean_Meta_ACLt_main_lt(v_mode_1199_, v_a_1197_, v_b_1198_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT void l_Lean_Meta_acLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1197_ = stack[0].m_obj;
lean_object* v_b_1198_ = stack[1].m_obj;
uint8_t v_mode_1199_ = stack[2].m_num;
lean_object* v_a_1200_ = stack[3].m_obj;
lean_object* v_a_1201_ = stack[4].m_obj;
lean_object* v_a_1202_ = stack[5].m_obj;
lean_object* v_a_1203_ = stack[6].m_obj;
lean_object* v_res_1206_;
v_res_1206_ = l_Lean_Meta_acLt(v_a_1197_, v_b_1198_, v_mode_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
stack->m_obj
 = v_res_1206_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_acLt___boxed(lean_object* v_a_1207_, lean_object* v_b_1208_, lean_object* v_mode_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
uint8_t v_mode_boxed_1215_; lean_object* v_res_1216_; 
v_mode_boxed_1215_ = lean_unbox(v_mode_1209_);
v_res_1216_ = l_Lean_Meta_acLt(v_a_1207_, v_b_1208_, v_mode_boxed_1215_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
return v_res_1216_;
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
