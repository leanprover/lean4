// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.StructId
// Imports: public import Lean.Meta.Tactic.Grind.Order.Types import Lean.Meta.Tactic.Grind.OrderInsts import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
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
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OrderedRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___boxed(lean_object**);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f_spec__0(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12_value;
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Order_orderExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_7);
x_13 = lean_grind_canon(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Sym_shareCommon___redArg(x_14, x_7);
lean_dec(x_7);
return x_15;
}
else
{
lean_dec(x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_mkConst(x_1, x_10);
x_12 = l_Lean_Expr_app___override(x_11, x_3);
x_13 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_12, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3));
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_mkConst(x_12, x_14);
x_16 = l_Lean_mkApp5(x_15, x_2, x_3, x_4, x_5, x_6);
x_17 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_16, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_push(x_4, x_1);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_11 = lean_array_push(x_6, x_1);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6;
x_4 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_getDecLevel_x3f(x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
lean_free_object(x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_18, x_17, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_21);
lean_inc_ref(x_1);
lean_inc(x_17);
x_23 = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(x_17, x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_21);
lean_inc_ref(x_1);
lean_inc(x_17);
x_28 = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(x_17, x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_21);
lean_inc_ref(x_1);
lean_inc(x_17);
x_30 = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(x_17, x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_17);
x_33 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_32, x_17, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5));
x_36 = lean_box(0);
lean_inc(x_17);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_36);
lean_inc_ref(x_37);
x_38 = l_Lean_mkConst(x_35, x_37);
lean_inc(x_22);
lean_inc_ref(x_1);
x_39 = l_Lean_mkAppB(x_38, x_1, x_22);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_40 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_34, 0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_34);
lean_inc_ref(x_1);
lean_inc(x_17);
x_82 = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(x_17, x_1, x_34, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_37);
lean_free_object(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_73 = x_83;
x_74 = x_83;
x_75 = x_2;
x_76 = x_10;
x_77 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12));
x_85 = l_Lean_mkConst(x_84, x_37);
lean_inc(x_81);
lean_inc_ref(x_1);
x_86 = l_Lean_mkAppB(x_85, x_1, x_81);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_87 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_89 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
lean_ctor_set(x_15, 0, x_88);
x_91 = 0;
x_92 = 1;
if (lean_obj_tag(x_90) == 1)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_91);
x_95 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_96, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_100, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_94);
lean_dec(x_100);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_98, 3);
lean_inc_ref(x_104);
lean_dec(x_98);
x_105 = lean_ctor_get(x_103, 4);
lean_inc_ref(x_105);
lean_dec(x_103);
lean_inc_ref(x_10);
lean_inc(x_26);
lean_inc(x_81);
lean_inc(x_22);
lean_inc_ref(x_1);
lean_inc(x_17);
x_106 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_17, x_1, x_105, x_22, x_81, x_26, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
if (lean_obj_tag(x_107) == 1)
{
lean_ctor_set_tag(x_101, 1);
lean_ctor_set(x_101, 0, x_104);
x_42 = x_15;
x_43 = x_83;
x_44 = x_90;
x_45 = x_101;
x_46 = x_107;
x_47 = x_92;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_108; 
lean_dec(x_107);
lean_dec_ref(x_104);
lean_free_object(x_101);
lean_dec_ref(x_90);
x_108 = lean_box(0);
x_42 = x_15;
x_43 = x_83;
x_44 = x_108;
x_45 = x_108;
x_46 = x_108;
x_47 = x_92;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_104);
lean_free_object(x_101);
lean_dec_ref(x_15);
lean_dec_ref(x_90);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
lean_dec(x_101);
x_113 = lean_ctor_get(x_98, 3);
lean_inc_ref(x_113);
lean_dec(x_98);
x_114 = lean_ctor_get(x_112, 4);
lean_inc_ref(x_114);
lean_dec(x_112);
lean_inc_ref(x_10);
lean_inc(x_26);
lean_inc(x_81);
lean_inc(x_22);
lean_inc_ref(x_1);
lean_inc(x_17);
x_115 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_17, x_1, x_114, x_22, x_81, x_26, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_113);
x_42 = x_15;
x_43 = x_83;
x_44 = x_90;
x_45 = x_117;
x_46 = x_116;
x_47 = x_92;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_118; 
lean_dec(x_116);
lean_dec_ref(x_113);
lean_dec_ref(x_90);
x_118 = lean_box(0);
x_42 = x_15;
x_43 = x_83;
x_44 = x_118;
x_45 = x_118;
x_46 = x_118;
x_47 = x_92;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_113);
lean_dec_ref(x_15);
lean_dec_ref(x_90);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_120 = x_115;
} else {
 lean_dec_ref(x_115);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_98);
lean_dec_ref(x_94);
lean_dec_ref(x_15);
lean_dec_ref(x_90);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_122 = !lean_is_exclusive(x_99);
if (x_122 == 0)
{
return x_99;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_99, 0);
lean_inc(x_123);
lean_dec(x_99);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec_ref(x_94);
lean_dec_ref(x_15);
lean_dec_ref(x_90);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_95);
if (x_125 == 0)
{
return x_95;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_95, 0);
lean_inc(x_126);
lean_dec(x_95);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_90);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_128 = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 0);
if (lean_obj_tag(x_130) == 1)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 0);
x_132 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_131, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_131, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = lean_ctor_get(x_133, 4);
lean_inc_ref(x_136);
lean_dec(x_133);
x_137 = lean_ctor_get(x_135, 3);
lean_inc_ref(x_137);
lean_dec(x_135);
lean_inc_ref(x_10);
lean_inc(x_26);
lean_inc(x_81);
lean_inc(x_22);
lean_inc_ref(x_1);
lean_inc(x_17);
x_138 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_17, x_1, x_136, x_22, x_81, x_26, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
if (lean_obj_tag(x_139) == 1)
{
lean_ctor_set_tag(x_128, 1);
lean_ctor_set(x_128, 0, x_137);
x_42 = x_15;
x_43 = x_83;
x_44 = x_130;
x_45 = x_128;
x_46 = x_139;
x_47 = x_91;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_140; 
lean_dec(x_139);
lean_dec_ref(x_137);
lean_free_object(x_128);
lean_dec_ref(x_130);
x_140 = lean_box(0);
x_42 = x_15;
x_43 = x_83;
x_44 = x_140;
x_45 = x_140;
x_46 = x_140;
x_47 = x_92;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
}
else
{
uint8_t x_141; 
lean_dec_ref(x_137);
lean_free_object(x_128);
lean_dec_ref(x_130);
lean_dec_ref(x_15);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_141 = !lean_is_exclusive(x_138);
if (x_141 == 0)
{
return x_138;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
lean_dec(x_138);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_133);
lean_free_object(x_128);
lean_dec_ref(x_130);
lean_dec_ref(x_15);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_144 = !lean_is_exclusive(x_134);
if (x_144 == 0)
{
return x_134;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_134, 0);
lean_inc(x_145);
lean_dec(x_134);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_free_object(x_128);
lean_dec_ref(x_130);
lean_dec_ref(x_15);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_147 = !lean_is_exclusive(x_132);
if (x_147 == 0)
{
return x_132;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_132, 0);
lean_inc(x_148);
lean_dec(x_132);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
}
else
{
lean_object* x_150; 
lean_free_object(x_128);
lean_dec(x_130);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_150 = lean_box(0);
x_42 = x_15;
x_43 = x_83;
x_44 = x_150;
x_45 = x_150;
x_46 = x_150;
x_47 = x_91;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_128, 0);
lean_inc(x_151);
lean_dec(x_128);
if (lean_obj_tag(x_151) == 1)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 0);
x_153 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = lean_ctor_get(x_154, 4);
lean_inc_ref(x_157);
lean_dec(x_154);
x_158 = lean_ctor_get(x_156, 3);
lean_inc_ref(x_158);
lean_dec(x_156);
lean_inc_ref(x_10);
lean_inc(x_26);
lean_inc(x_81);
lean_inc(x_22);
lean_inc_ref(x_1);
lean_inc(x_17);
x_159 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_17, x_1, x_157, x_22, x_81, x_26, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
if (lean_obj_tag(x_160) == 1)
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_158);
x_42 = x_15;
x_43 = x_83;
x_44 = x_151;
x_45 = x_161;
x_46 = x_160;
x_47 = x_91;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_162; 
lean_dec(x_160);
lean_dec_ref(x_158);
lean_dec_ref(x_151);
x_162 = lean_box(0);
x_42 = x_15;
x_43 = x_83;
x_44 = x_162;
x_45 = x_162;
x_46 = x_162;
x_47 = x_92;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec_ref(x_158);
lean_dec_ref(x_151);
lean_dec_ref(x_15);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_164 = x_159;
} else {
 lean_dec_ref(x_159);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_154);
lean_dec_ref(x_151);
lean_dec_ref(x_15);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_166 = lean_ctor_get(x_155, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_167 = x_155;
} else {
 lean_dec_ref(x_155);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_151);
lean_dec_ref(x_15);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_169 = lean_ctor_get(x_153, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_170 = x_153;
} else {
 lean_dec_ref(x_153);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
return x_171;
}
}
else
{
lean_object* x_172; 
lean_dec(x_151);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_172 = lean_box(0);
x_42 = x_15;
x_43 = x_83;
x_44 = x_172;
x_45 = x_172;
x_46 = x_172;
x_47 = x_91;
x_48 = x_2;
x_49 = x_10;
x_50 = lean_box(0);
goto block_72;
}
}
}
else
{
lean_dec_ref(x_15);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_128;
}
}
}
else
{
lean_dec(x_88);
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_89;
}
}
else
{
uint8_t x_173; 
lean_dec_ref(x_83);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_173 = !lean_is_exclusive(x_87);
if (x_173 == 0)
{
return x_87;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_87, 0);
lean_inc(x_174);
lean_dec(x_87);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_41);
lean_dec_ref(x_37);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_176 = !lean_is_exclusive(x_82);
if (x_176 == 0)
{
return x_82;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_82, 0);
lean_inc(x_177);
lean_dec(x_82);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; 
lean_dec_ref(x_37);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_179 = lean_box(0);
x_73 = x_179;
x_74 = x_179;
x_75 = x_2;
x_76 = x_10;
x_77 = lean_box(0);
goto block_80;
}
block_72:
{
lean_object* x_51; 
x_51 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_48, x_49);
lean_dec_ref(x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
lean_dec(x_52);
x_54 = lean_array_get_size(x_53);
lean_dec_ref(x_53);
x_55 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8;
x_56 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10;
x_57 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_1);
lean_ctor_set(x_57, 2, x_17);
lean_ctor_set(x_57, 3, x_26);
lean_ctor_set(x_57, 4, x_22);
lean_ctor_set(x_57, 5, x_34);
lean_ctor_set(x_57, 6, x_29);
lean_ctor_set(x_57, 7, x_31);
lean_ctor_set(x_57, 8, x_43);
lean_ctor_set(x_57, 9, x_44);
lean_ctor_set(x_57, 10, x_45);
lean_ctor_set(x_57, 11, x_46);
lean_ctor_set(x_57, 12, x_41);
lean_ctor_set(x_57, 13, x_42);
lean_ctor_set(x_57, 14, x_55);
lean_ctor_set(x_57, 15, x_56);
lean_ctor_set(x_57, 16, x_56);
lean_ctor_set(x_57, 17, x_56);
lean_ctor_set(x_57, 18, x_55);
lean_ctor_set(x_57, 19, x_55);
lean_ctor_set(x_57, 20, x_55);
lean_ctor_set(x_57, 21, x_36);
lean_ctor_set_uint8(x_57, sizeof(void*)*22, x_47);
x_58 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(x_58, 0, x_57);
x_59 = l_Lean_Meta_Grind_Order_orderExt;
x_60 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_59, x_58, x_48);
lean_dec(x_48);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
if (lean_is_scalar(x_27)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_27;
}
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_60);
if (lean_is_scalar(x_27)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_27;
}
lean_ctor_set(x_64, 0, x_54);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_27);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 0);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_51);
if (x_69 == 0)
{
return x_51;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
lean_dec(x_51);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
block_80:
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_box(0);
x_79 = 0;
lean_inc_n(x_73, 2);
x_42 = x_74;
x_43 = x_73;
x_44 = x_78;
x_45 = x_73;
x_46 = x_73;
x_47 = x_79;
x_48 = x_75;
x_49 = x_76;
x_50 = lean_box(0);
goto block_72;
}
}
else
{
uint8_t x_180; 
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_180 = !lean_is_exclusive(x_40);
if (x_180 == 0)
{
return x_40;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
lean_dec(x_40);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = !lean_is_exclusive(x_33);
if (x_183 == 0)
{
return x_33;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_33, 0);
lean_inc(x_184);
lean_dec(x_33);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_186 = !lean_is_exclusive(x_30);
if (x_186 == 0)
{
return x_30;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_30, 0);
lean_inc(x_187);
lean_dec(x_30);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_189 = !lean_is_exclusive(x_28);
if (x_189 == 0)
{
return x_28;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_28, 0);
lean_inc(x_190);
lean_dec(x_28);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_192 = lean_box(0);
lean_ctor_set(x_23, 0, x_192);
return x_23;
}
}
else
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_23, 0);
lean_inc(x_193);
lean_dec(x_23);
if (lean_obj_tag(x_193) == 1)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_21);
lean_inc_ref(x_1);
lean_inc(x_17);
x_196 = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(x_17, x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_21);
lean_inc_ref(x_1);
lean_inc(x_17);
x_198 = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(x_17, x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
x_200 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_17);
x_201 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_200, x_17, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
x_203 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5));
x_204 = lean_box(0);
lean_inc(x_17);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_17);
lean_ctor_set(x_205, 1, x_204);
lean_inc_ref(x_205);
x_206 = l_Lean_mkConst(x_203, x_205);
lean_inc(x_22);
lean_inc_ref(x_1);
x_207 = l_Lean_mkAppB(x_206, x_1, x_22);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_208 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_207, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
if (lean_obj_tag(x_202) == 1)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_202, 0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_202);
lean_inc_ref(x_1);
lean_inc(x_17);
x_248 = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(x_17, x_1, x_202, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
if (lean_obj_tag(x_249) == 0)
{
lean_dec_ref(x_205);
lean_free_object(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_239 = x_249;
x_240 = x_249;
x_241 = x_2;
x_242 = x_10;
x_243 = lean_box(0);
goto block_246;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12));
x_251 = l_Lean_mkConst(x_250, x_205);
lean_inc(x_247);
lean_inc_ref(x_1);
x_252 = l_Lean_mkAppB(x_251, x_1, x_247);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_253 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_252, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_255 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; uint8_t x_257; uint8_t x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
lean_ctor_set(x_15, 0, x_254);
x_257 = 0;
x_258 = 1;
if (lean_obj_tag(x_256) == 1)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_256, 0);
lean_inc(x_259);
x_260 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set_uint8(x_260, sizeof(void*)*1, x_257);
x_261 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_260, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_262, x_260, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_262);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
x_265 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_260, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_266, x_260, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_260);
lean_dec(x_266);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_269 = x_267;
} else {
 lean_dec_ref(x_267);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_264, 3);
lean_inc_ref(x_270);
lean_dec(x_264);
x_271 = lean_ctor_get(x_268, 4);
lean_inc_ref(x_271);
lean_dec(x_268);
lean_inc_ref(x_10);
lean_inc(x_194);
lean_inc(x_247);
lean_inc(x_22);
lean_inc_ref(x_1);
lean_inc(x_17);
x_272 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_17, x_1, x_271, x_22, x_247, x_194, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec_ref(x_272);
if (lean_obj_tag(x_273) == 1)
{
lean_object* x_274; 
if (lean_is_scalar(x_269)) {
 x_274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_274 = x_269;
 lean_ctor_set_tag(x_274, 1);
}
lean_ctor_set(x_274, 0, x_270);
x_210 = x_15;
x_211 = x_249;
x_212 = x_256;
x_213 = x_274;
x_214 = x_273;
x_215 = x_258;
x_216 = x_2;
x_217 = x_10;
x_218 = lean_box(0);
goto block_238;
}
else
{
lean_object* x_275; 
lean_dec(x_273);
lean_dec_ref(x_270);
lean_dec(x_269);
lean_dec_ref(x_256);
x_275 = lean_box(0);
x_210 = x_15;
x_211 = x_249;
x_212 = x_275;
x_213 = x_275;
x_214 = x_275;
x_215 = x_258;
x_216 = x_2;
x_217 = x_10;
x_218 = lean_box(0);
goto block_238;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec_ref(x_270);
lean_dec(x_269);
lean_dec_ref(x_15);
lean_dec_ref(x_256);
lean_dec_ref(x_249);
lean_dec(x_209);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_276 = lean_ctor_get(x_272, 0);
lean_inc(x_276);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_277 = x_272;
} else {
 lean_dec_ref(x_272);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 1, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_264);
lean_dec_ref(x_260);
lean_dec_ref(x_15);
lean_dec_ref(x_256);
lean_dec_ref(x_249);
lean_dec(x_209);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_279 = lean_ctor_get(x_265, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_280 = x_265;
} else {
 lean_dec_ref(x_265);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec_ref(x_260);
lean_dec_ref(x_15);
lean_dec_ref(x_256);
lean_dec_ref(x_249);
lean_dec(x_209);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_282 = lean_ctor_get(x_261, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_283 = x_261;
} else {
 lean_dec_ref(x_261);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 1, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_282);
return x_284;
}
}
else
{
lean_object* x_285; 
lean_dec(x_256);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_285 = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
if (lean_obj_tag(x_286) == 1)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_286, 0);
x_289 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_288, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
x_291 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_288, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = lean_ctor_get(x_290, 4);
lean_inc_ref(x_293);
lean_dec(x_290);
x_294 = lean_ctor_get(x_292, 3);
lean_inc_ref(x_294);
lean_dec(x_292);
lean_inc_ref(x_10);
lean_inc(x_194);
lean_inc(x_247);
lean_inc(x_22);
lean_inc_ref(x_1);
lean_inc(x_17);
x_295 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_17, x_1, x_293, x_22, x_247, x_194, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec_ref(x_295);
if (lean_obj_tag(x_296) == 1)
{
lean_object* x_297; 
if (lean_is_scalar(x_287)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_287;
 lean_ctor_set_tag(x_297, 1);
}
lean_ctor_set(x_297, 0, x_294);
x_210 = x_15;
x_211 = x_249;
x_212 = x_286;
x_213 = x_297;
x_214 = x_296;
x_215 = x_257;
x_216 = x_2;
x_217 = x_10;
x_218 = lean_box(0);
goto block_238;
}
else
{
lean_object* x_298; 
lean_dec(x_296);
lean_dec_ref(x_294);
lean_dec(x_287);
lean_dec_ref(x_286);
x_298 = lean_box(0);
x_210 = x_15;
x_211 = x_249;
x_212 = x_298;
x_213 = x_298;
x_214 = x_298;
x_215 = x_258;
x_216 = x_2;
x_217 = x_10;
x_218 = lean_box(0);
goto block_238;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec_ref(x_294);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_15);
lean_dec_ref(x_249);
lean_dec(x_209);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_299 = lean_ctor_get(x_295, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_300 = x_295;
} else {
 lean_dec_ref(x_295);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_290);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_15);
lean_dec_ref(x_249);
lean_dec(x_209);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_302 = lean_ctor_get(x_291, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_303 = x_291;
} else {
 lean_dec_ref(x_291);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 1, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_302);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_15);
lean_dec_ref(x_249);
lean_dec(x_209);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_305 = lean_ctor_get(x_289, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 x_306 = x_289;
} else {
 lean_dec_ref(x_289);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 1, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_305);
return x_307;
}
}
else
{
lean_object* x_308; 
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_308 = lean_box(0);
x_210 = x_15;
x_211 = x_249;
x_212 = x_308;
x_213 = x_308;
x_214 = x_308;
x_215 = x_257;
x_216 = x_2;
x_217 = x_10;
x_218 = lean_box(0);
goto block_238;
}
}
else
{
lean_dec_ref(x_15);
lean_dec_ref(x_249);
lean_dec(x_209);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_285;
}
}
}
else
{
lean_dec(x_254);
lean_dec_ref(x_249);
lean_dec(x_209);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_255;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec_ref(x_249);
lean_dec(x_209);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_309 = lean_ctor_get(x_253, 0);
lean_inc(x_309);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_310 = x_253;
} else {
 lean_dec_ref(x_253);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 1, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_309);
return x_311;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_209);
lean_dec_ref(x_205);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_312 = lean_ctor_get(x_248, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_313 = x_248;
} else {
 lean_dec_ref(x_248);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 1, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_312);
return x_314;
}
}
else
{
lean_object* x_315; 
lean_dec_ref(x_205);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_315 = lean_box(0);
x_239 = x_315;
x_240 = x_315;
x_241 = x_2;
x_242 = x_10;
x_243 = lean_box(0);
goto block_246;
}
block_238:
{
lean_object* x_219; 
x_219 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_216, x_217);
lean_dec_ref(x_217);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = lean_ctor_get(x_220, 0);
lean_inc_ref(x_221);
lean_dec(x_220);
x_222 = lean_array_get_size(x_221);
lean_dec_ref(x_221);
x_223 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8;
x_224 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10;
x_225 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_1);
lean_ctor_set(x_225, 2, x_17);
lean_ctor_set(x_225, 3, x_194);
lean_ctor_set(x_225, 4, x_22);
lean_ctor_set(x_225, 5, x_202);
lean_ctor_set(x_225, 6, x_197);
lean_ctor_set(x_225, 7, x_199);
lean_ctor_set(x_225, 8, x_211);
lean_ctor_set(x_225, 9, x_212);
lean_ctor_set(x_225, 10, x_213);
lean_ctor_set(x_225, 11, x_214);
lean_ctor_set(x_225, 12, x_209);
lean_ctor_set(x_225, 13, x_210);
lean_ctor_set(x_225, 14, x_223);
lean_ctor_set(x_225, 15, x_224);
lean_ctor_set(x_225, 16, x_224);
lean_ctor_set(x_225, 17, x_224);
lean_ctor_set(x_225, 18, x_223);
lean_ctor_set(x_225, 19, x_223);
lean_ctor_set(x_225, 20, x_223);
lean_ctor_set(x_225, 21, x_204);
lean_ctor_set_uint8(x_225, sizeof(void*)*22, x_215);
x_226 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(x_226, 0, x_225);
x_227 = l_Lean_Meta_Grind_Order_orderExt;
x_228 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_227, x_226, x_216);
lean_dec(x_216);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_229 = x_228;
} else {
 lean_dec_ref(x_228);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_195;
}
lean_ctor_set(x_230, 0, x_222);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(0, 1, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_195);
x_232 = lean_ctor_get(x_228, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_233 = x_228;
} else {
 lean_dec_ref(x_228);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_1);
x_235 = lean_ctor_get(x_219, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_236 = x_219;
} else {
 lean_dec_ref(x_219);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 1, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_235);
return x_237;
}
}
block_246:
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_box(0);
x_245 = 0;
lean_inc_n(x_239, 2);
x_210 = x_240;
x_211 = x_239;
x_212 = x_244;
x_213 = x_239;
x_214 = x_239;
x_215 = x_245;
x_216 = x_241;
x_217 = x_242;
x_218 = lean_box(0);
goto block_238;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec_ref(x_205);
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_316 = lean_ctor_get(x_208, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_317 = x_208;
} else {
 lean_dec_ref(x_208);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 1, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_316);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_319 = lean_ctor_get(x_201, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_320 = x_201;
} else {
 lean_dec_ref(x_201);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 1, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_322 = lean_ctor_get(x_198, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_323 = x_198;
} else {
 lean_dec_ref(x_198);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 1, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_322);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_325 = lean_ctor_get(x_196, 0);
lean_inc(x_325);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_326 = x_196;
} else {
 lean_dec_ref(x_196);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 1, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_193);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_328 = lean_box(0);
x_329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_329, 0, x_328);
return x_329;
}
}
}
else
{
uint8_t x_330; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_330 = !lean_is_exclusive(x_23);
if (x_330 == 0)
{
return x_23;
}
else
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_23, 0);
lean_inc(x_331);
lean_dec(x_23);
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_331);
return x_332;
}
}
}
else
{
lean_object* x_333; 
lean_dec(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_333 = lean_box(0);
lean_ctor_set(x_19, 0, x_333);
return x_19;
}
}
else
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_19, 0);
lean_inc(x_334);
lean_dec(x_19);
if (lean_obj_tag(x_334) == 1)
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_334);
lean_inc_ref(x_1);
lean_inc(x_17);
x_336 = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(x_17, x_1, x_334, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_338 = x_336;
} else {
 lean_dec_ref(x_336);
 x_338 = lean_box(0);
}
if (lean_obj_tag(x_337) == 1)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_338);
x_339 = lean_ctor_get(x_337, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_334);
lean_inc_ref(x_1);
lean_inc(x_17);
x_341 = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(x_17, x_1, x_334, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
lean_dec_ref(x_341);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_334);
lean_inc_ref(x_1);
lean_inc(x_17);
x_343 = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(x_17, x_1, x_334, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
x_345 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_17);
x_346 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_345, x_17, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
lean_dec_ref(x_346);
x_348 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5));
x_349 = lean_box(0);
lean_inc(x_17);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_17);
lean_ctor_set(x_350, 1, x_349);
lean_inc_ref(x_350);
x_351 = l_Lean_mkConst(x_348, x_350);
lean_inc(x_335);
lean_inc_ref(x_1);
x_352 = l_Lean_mkAppB(x_351, x_1, x_335);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_353 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_352, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
lean_dec_ref(x_353);
if (lean_obj_tag(x_347) == 1)
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_347, 0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_347);
lean_inc_ref(x_1);
lean_inc(x_17);
x_393 = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(x_17, x_1, x_347, x_334, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
lean_dec_ref(x_393);
if (lean_obj_tag(x_394) == 0)
{
lean_dec_ref(x_350);
lean_free_object(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_384 = x_394;
x_385 = x_394;
x_386 = x_2;
x_387 = x_10;
x_388 = lean_box(0);
goto block_391;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_395 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12));
x_396 = l_Lean_mkConst(x_395, x_350);
lean_inc(x_392);
lean_inc_ref(x_1);
x_397 = l_Lean_mkAppB(x_396, x_1, x_392);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_398 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_397, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_400 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; uint8_t x_402; uint8_t x_403; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
lean_ctor_set(x_15, 0, x_399);
x_402 = 0;
x_403 = 1;
if (lean_obj_tag(x_401) == 1)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_401, 0);
lean_inc(x_404);
x_405 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set_uint8(x_405, sizeof(void*)*1, x_402);
x_406 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_405, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec_ref(x_406);
x_408 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_407, x_405, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_407);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
lean_dec_ref(x_408);
x_410 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_405, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
x_412 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_411, x_405, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_405);
lean_dec(x_411);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_414 = x_412;
} else {
 lean_dec_ref(x_412);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_409, 3);
lean_inc_ref(x_415);
lean_dec(x_409);
x_416 = lean_ctor_get(x_413, 4);
lean_inc_ref(x_416);
lean_dec(x_413);
lean_inc_ref(x_10);
lean_inc(x_339);
lean_inc(x_392);
lean_inc(x_335);
lean_inc_ref(x_1);
lean_inc(x_17);
x_417 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_17, x_1, x_416, x_335, x_392, x_339, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
lean_dec_ref(x_417);
if (lean_obj_tag(x_418) == 1)
{
lean_object* x_419; 
if (lean_is_scalar(x_414)) {
 x_419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_419 = x_414;
 lean_ctor_set_tag(x_419, 1);
}
lean_ctor_set(x_419, 0, x_415);
x_355 = x_15;
x_356 = x_394;
x_357 = x_401;
x_358 = x_419;
x_359 = x_418;
x_360 = x_403;
x_361 = x_2;
x_362 = x_10;
x_363 = lean_box(0);
goto block_383;
}
else
{
lean_object* x_420; 
lean_dec(x_418);
lean_dec_ref(x_415);
lean_dec(x_414);
lean_dec_ref(x_401);
x_420 = lean_box(0);
x_355 = x_15;
x_356 = x_394;
x_357 = x_420;
x_358 = x_420;
x_359 = x_420;
x_360 = x_403;
x_361 = x_2;
x_362 = x_10;
x_363 = lean_box(0);
goto block_383;
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec_ref(x_415);
lean_dec(x_414);
lean_dec_ref(x_15);
lean_dec_ref(x_401);
lean_dec_ref(x_394);
lean_dec(x_354);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_17);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_421 = lean_ctor_get(x_417, 0);
lean_inc(x_421);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 x_422 = x_417;
} else {
 lean_dec_ref(x_417);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(1, 1, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_421);
return x_423;
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_409);
lean_dec_ref(x_405);
lean_dec_ref(x_15);
lean_dec_ref(x_401);
lean_dec_ref(x_394);
lean_dec(x_354);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_424 = lean_ctor_get(x_410, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 x_425 = x_410;
} else {
 lean_dec_ref(x_410);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 1, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec_ref(x_405);
lean_dec_ref(x_15);
lean_dec_ref(x_401);
lean_dec_ref(x_394);
lean_dec(x_354);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_427 = lean_ctor_get(x_406, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_428 = x_406;
} else {
 lean_dec_ref(x_406);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_427);
return x_429;
}
}
else
{
lean_object* x_430; 
lean_dec(x_401);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_430 = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 x_432 = x_430;
} else {
 lean_dec_ref(x_430);
 x_432 = lean_box(0);
}
if (lean_obj_tag(x_431) == 1)
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_ctor_get(x_431, 0);
x_434 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_433, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
lean_dec_ref(x_434);
x_436 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_433, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
x_438 = lean_ctor_get(x_435, 4);
lean_inc_ref(x_438);
lean_dec(x_435);
x_439 = lean_ctor_get(x_437, 3);
lean_inc_ref(x_439);
lean_dec(x_437);
lean_inc_ref(x_10);
lean_inc(x_339);
lean_inc(x_392);
lean_inc(x_335);
lean_inc_ref(x_1);
lean_inc(x_17);
x_440 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_17, x_1, x_438, x_335, x_392, x_339, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
lean_dec_ref(x_440);
if (lean_obj_tag(x_441) == 1)
{
lean_object* x_442; 
if (lean_is_scalar(x_432)) {
 x_442 = lean_alloc_ctor(1, 1, 0);
} else {
 x_442 = x_432;
 lean_ctor_set_tag(x_442, 1);
}
lean_ctor_set(x_442, 0, x_439);
x_355 = x_15;
x_356 = x_394;
x_357 = x_431;
x_358 = x_442;
x_359 = x_441;
x_360 = x_402;
x_361 = x_2;
x_362 = x_10;
x_363 = lean_box(0);
goto block_383;
}
else
{
lean_object* x_443; 
lean_dec(x_441);
lean_dec_ref(x_439);
lean_dec(x_432);
lean_dec_ref(x_431);
x_443 = lean_box(0);
x_355 = x_15;
x_356 = x_394;
x_357 = x_443;
x_358 = x_443;
x_359 = x_443;
x_360 = x_403;
x_361 = x_2;
x_362 = x_10;
x_363 = lean_box(0);
goto block_383;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec_ref(x_439);
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec_ref(x_15);
lean_dec_ref(x_394);
lean_dec(x_354);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_17);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_444 = lean_ctor_get(x_440, 0);
lean_inc(x_444);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_445 = x_440;
} else {
 lean_dec_ref(x_440);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 1, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_444);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_435);
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec_ref(x_15);
lean_dec_ref(x_394);
lean_dec(x_354);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_447 = lean_ctor_get(x_436, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_448 = x_436;
} else {
 lean_dec_ref(x_436);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 1, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_447);
return x_449;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec_ref(x_15);
lean_dec_ref(x_394);
lean_dec(x_354);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_450 = lean_ctor_get(x_434, 0);
lean_inc(x_450);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 x_451 = x_434;
} else {
 lean_dec_ref(x_434);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 1, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_450);
return x_452;
}
}
else
{
lean_object* x_453; 
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_453 = lean_box(0);
x_355 = x_15;
x_356 = x_394;
x_357 = x_453;
x_358 = x_453;
x_359 = x_453;
x_360 = x_402;
x_361 = x_2;
x_362 = x_10;
x_363 = lean_box(0);
goto block_383;
}
}
else
{
lean_dec_ref(x_15);
lean_dec_ref(x_394);
lean_dec(x_354);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_430;
}
}
}
else
{
lean_dec(x_399);
lean_dec_ref(x_394);
lean_dec(x_354);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_400;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec_ref(x_394);
lean_dec(x_354);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_454 = lean_ctor_get(x_398, 0);
lean_inc(x_454);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_455 = x_398;
} else {
 lean_dec_ref(x_398);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 1, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_454);
return x_456;
}
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_354);
lean_dec_ref(x_350);
lean_dec_ref(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_457 = lean_ctor_get(x_393, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 x_458 = x_393;
} else {
 lean_dec_ref(x_393);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 1, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_457);
return x_459;
}
}
else
{
lean_object* x_460; 
lean_dec_ref(x_350);
lean_dec_ref(x_334);
lean_free_object(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_460 = lean_box(0);
x_384 = x_460;
x_385 = x_460;
x_386 = x_2;
x_387 = x_10;
x_388 = lean_box(0);
goto block_391;
}
block_383:
{
lean_object* x_364; 
x_364 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_361, x_362);
lean_dec_ref(x_362);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec_ref(x_364);
x_366 = lean_ctor_get(x_365, 0);
lean_inc_ref(x_366);
lean_dec(x_365);
x_367 = lean_array_get_size(x_366);
lean_dec_ref(x_366);
x_368 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8;
x_369 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10;
x_370 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_1);
lean_ctor_set(x_370, 2, x_17);
lean_ctor_set(x_370, 3, x_339);
lean_ctor_set(x_370, 4, x_335);
lean_ctor_set(x_370, 5, x_347);
lean_ctor_set(x_370, 6, x_342);
lean_ctor_set(x_370, 7, x_344);
lean_ctor_set(x_370, 8, x_356);
lean_ctor_set(x_370, 9, x_357);
lean_ctor_set(x_370, 10, x_358);
lean_ctor_set(x_370, 11, x_359);
lean_ctor_set(x_370, 12, x_354);
lean_ctor_set(x_370, 13, x_355);
lean_ctor_set(x_370, 14, x_368);
lean_ctor_set(x_370, 15, x_369);
lean_ctor_set(x_370, 16, x_369);
lean_ctor_set(x_370, 17, x_369);
lean_ctor_set(x_370, 18, x_368);
lean_ctor_set(x_370, 19, x_368);
lean_ctor_set(x_370, 20, x_368);
lean_ctor_set(x_370, 21, x_349);
lean_ctor_set_uint8(x_370, sizeof(void*)*22, x_360);
x_371 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(x_371, 0, x_370);
x_372 = l_Lean_Meta_Grind_Order_orderExt;
x_373 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_372, x_371, x_361);
lean_dec(x_361);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_374 = x_373;
} else {
 lean_dec_ref(x_373);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_375 = lean_alloc_ctor(1, 1, 0);
} else {
 x_375 = x_340;
}
lean_ctor_set(x_375, 0, x_367);
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(0, 1, 0);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_340);
x_377 = lean_ctor_get(x_373, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_378 = x_373;
} else {
 lean_dec_ref(x_373);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_377);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_361);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_17);
lean_dec_ref(x_1);
x_380 = lean_ctor_get(x_364, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 x_381 = x_364;
} else {
 lean_dec_ref(x_364);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 1, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_380);
return x_382;
}
}
block_391:
{
lean_object* x_389; uint8_t x_390; 
x_389 = lean_box(0);
x_390 = 0;
lean_inc_n(x_384, 2);
x_355 = x_385;
x_356 = x_384;
x_357 = x_389;
x_358 = x_384;
x_359 = x_384;
x_360 = x_390;
x_361 = x_386;
x_362 = x_387;
x_363 = lean_box(0);
goto block_383;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec_ref(x_350);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_461 = lean_ctor_get(x_353, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_462 = x_353;
} else {
 lean_dec_ref(x_353);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 1, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_461);
return x_463;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_464 = lean_ctor_get(x_346, 0);
lean_inc(x_464);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_465 = x_346;
} else {
 lean_dec_ref(x_346);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(1, 1, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_464);
return x_466;
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_467 = lean_ctor_get(x_343, 0);
lean_inc(x_467);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_468 = x_343;
} else {
 lean_dec_ref(x_343);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(1, 1, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_467);
return x_469;
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_470 = lean_ctor_get(x_341, 0);
lean_inc(x_470);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_471 = x_341;
} else {
 lean_dec_ref(x_341);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(1, 1, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_470);
return x_472;
}
}
else
{
lean_object* x_473; lean_object* x_474; 
lean_dec(x_337);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_473 = lean_box(0);
if (lean_is_scalar(x_338)) {
 x_474 = lean_alloc_ctor(0, 1, 0);
} else {
 x_474 = x_338;
}
lean_ctor_set(x_474, 0, x_473);
return x_474;
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_335);
lean_dec_ref(x_334);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_475 = lean_ctor_get(x_336, 0);
lean_inc(x_475);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_476 = x_336;
} else {
 lean_dec_ref(x_336);
 x_476 = lean_box(0);
}
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(1, 1, 0);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_475);
return x_477;
}
}
else
{
lean_object* x_478; lean_object* x_479; 
lean_dec(x_334);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_478 = lean_box(0);
x_479 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_479, 0, x_478);
return x_479;
}
}
}
else
{
uint8_t x_480; 
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_480 = !lean_is_exclusive(x_19);
if (x_480 == 0)
{
return x_19;
}
else
{
lean_object* x_481; lean_object* x_482; 
x_481 = lean_ctor_get(x_19, 0);
lean_inc(x_481);
lean_dec(x_19);
x_482 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_482, 0, x_481);
return x_482;
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_15, 0);
lean_inc(x_483);
lean_dec(x_15);
x_484 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_483);
x_485 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_484, x_483, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 x_487 = x_485;
} else {
 lean_dec_ref(x_485);
 x_487 = lean_box(0);
}
if (lean_obj_tag(x_486) == 1)
{
lean_object* x_488; lean_object* x_489; 
lean_dec(x_487);
x_488 = lean_ctor_get(x_486, 0);
lean_inc(x_488);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_486);
lean_inc_ref(x_1);
lean_inc(x_483);
x_489 = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(x_483, x_1, x_486, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; 
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 x_491 = x_489;
} else {
 lean_dec_ref(x_489);
 x_491 = lean_box(0);
}
if (lean_obj_tag(x_490) == 1)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_491);
x_492 = lean_ctor_get(x_490, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 x_493 = x_490;
} else {
 lean_dec_ref(x_490);
 x_493 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_486);
lean_inc_ref(x_1);
lean_inc(x_483);
x_494 = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(x_483, x_1, x_486, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
lean_dec_ref(x_494);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_486);
lean_inc_ref(x_1);
lean_inc(x_483);
x_496 = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(x_483, x_1, x_486, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
lean_dec_ref(x_496);
x_498 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_483);
x_499 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_498, x_483, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
lean_dec_ref(x_499);
x_501 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5));
x_502 = lean_box(0);
lean_inc(x_483);
x_503 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_503, 0, x_483);
lean_ctor_set(x_503, 1, x_502);
lean_inc_ref(x_503);
x_504 = l_Lean_mkConst(x_501, x_503);
lean_inc(x_488);
lean_inc_ref(x_1);
x_505 = l_Lean_mkAppB(x_504, x_1, x_488);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_506 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_505, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
lean_dec_ref(x_506);
if (lean_obj_tag(x_500) == 1)
{
lean_object* x_545; lean_object* x_546; 
x_545 = lean_ctor_get(x_500, 0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_500);
lean_inc_ref(x_1);
lean_inc(x_483);
x_546 = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(x_483, x_1, x_500, x_486, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
lean_dec_ref(x_546);
if (lean_obj_tag(x_547) == 0)
{
lean_dec_ref(x_503);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_537 = x_547;
x_538 = x_547;
x_539 = x_2;
x_540 = x_10;
x_541 = lean_box(0);
goto block_544;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_548 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12));
x_549 = l_Lean_mkConst(x_548, x_503);
lean_inc(x_545);
lean_inc_ref(x_1);
x_550 = l_Lean_mkAppB(x_549, x_1, x_545);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_551 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_550, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
lean_dec_ref(x_551);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_553 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; uint8_t x_556; uint8_t x_557; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
lean_dec_ref(x_553);
x_555 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_555, 0, x_552);
x_556 = 0;
x_557 = 1;
if (lean_obj_tag(x_554) == 1)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_554, 0);
lean_inc(x_558);
x_559 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set_uint8(x_559, sizeof(void*)*1, x_556);
x_560 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_559, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
lean_dec_ref(x_560);
x_562 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_561, x_559, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_561);
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
lean_dec_ref(x_562);
x_564 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_559, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
lean_dec_ref(x_564);
x_566 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_565, x_559, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_559);
lean_dec(x_565);
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 x_568 = x_566;
} else {
 lean_dec_ref(x_566);
 x_568 = lean_box(0);
}
x_569 = lean_ctor_get(x_563, 3);
lean_inc_ref(x_569);
lean_dec(x_563);
x_570 = lean_ctor_get(x_567, 4);
lean_inc_ref(x_570);
lean_dec(x_567);
lean_inc_ref(x_10);
lean_inc(x_492);
lean_inc(x_545);
lean_inc(x_488);
lean_inc_ref(x_1);
lean_inc(x_483);
x_571 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_483, x_1, x_570, x_488, x_545, x_492, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec_ref(x_571);
if (lean_obj_tag(x_572) == 1)
{
lean_object* x_573; 
if (lean_is_scalar(x_568)) {
 x_573 = lean_alloc_ctor(1, 1, 0);
} else {
 x_573 = x_568;
 lean_ctor_set_tag(x_573, 1);
}
lean_ctor_set(x_573, 0, x_569);
x_508 = x_555;
x_509 = x_547;
x_510 = x_554;
x_511 = x_573;
x_512 = x_572;
x_513 = x_557;
x_514 = x_2;
x_515 = x_10;
x_516 = lean_box(0);
goto block_536;
}
else
{
lean_object* x_574; 
lean_dec(x_572);
lean_dec_ref(x_569);
lean_dec(x_568);
lean_dec_ref(x_554);
x_574 = lean_box(0);
x_508 = x_555;
x_509 = x_547;
x_510 = x_574;
x_511 = x_574;
x_512 = x_574;
x_513 = x_557;
x_514 = x_2;
x_515 = x_10;
x_516 = lean_box(0);
goto block_536;
}
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec_ref(x_569);
lean_dec(x_568);
lean_dec_ref(x_555);
lean_dec_ref(x_554);
lean_dec_ref(x_547);
lean_dec(x_507);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_575 = lean_ctor_get(x_571, 0);
lean_inc(x_575);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 x_576 = x_571;
} else {
 lean_dec_ref(x_571);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_576)) {
 x_577 = lean_alloc_ctor(1, 1, 0);
} else {
 x_577 = x_576;
}
lean_ctor_set(x_577, 0, x_575);
return x_577;
}
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_563);
lean_dec_ref(x_559);
lean_dec_ref(x_555);
lean_dec_ref(x_554);
lean_dec_ref(x_547);
lean_dec(x_507);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_578 = lean_ctor_get(x_564, 0);
lean_inc(x_578);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 x_579 = x_564;
} else {
 lean_dec_ref(x_564);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(1, 1, 0);
} else {
 x_580 = x_579;
}
lean_ctor_set(x_580, 0, x_578);
return x_580;
}
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec_ref(x_559);
lean_dec_ref(x_555);
lean_dec_ref(x_554);
lean_dec_ref(x_547);
lean_dec(x_507);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_581 = lean_ctor_get(x_560, 0);
lean_inc(x_581);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 x_582 = x_560;
} else {
 lean_dec_ref(x_560);
 x_582 = lean_box(0);
}
if (lean_is_scalar(x_582)) {
 x_583 = lean_alloc_ctor(1, 1, 0);
} else {
 x_583 = x_582;
}
lean_ctor_set(x_583, 0, x_581);
return x_583;
}
}
else
{
lean_object* x_584; 
lean_dec(x_554);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_584 = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 x_586 = x_584;
} else {
 lean_dec_ref(x_584);
 x_586 = lean_box(0);
}
if (lean_obj_tag(x_585) == 1)
{
lean_object* x_587; lean_object* x_588; 
x_587 = lean_ctor_get(x_585, 0);
x_588 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_587, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
lean_dec_ref(x_588);
x_590 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_587, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
lean_dec_ref(x_590);
x_592 = lean_ctor_get(x_589, 4);
lean_inc_ref(x_592);
lean_dec(x_589);
x_593 = lean_ctor_get(x_591, 3);
lean_inc_ref(x_593);
lean_dec(x_591);
lean_inc_ref(x_10);
lean_inc(x_492);
lean_inc(x_545);
lean_inc(x_488);
lean_inc_ref(x_1);
lean_inc(x_483);
x_594 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_483, x_1, x_592, x_488, x_545, x_492, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
lean_dec_ref(x_594);
if (lean_obj_tag(x_595) == 1)
{
lean_object* x_596; 
if (lean_is_scalar(x_586)) {
 x_596 = lean_alloc_ctor(1, 1, 0);
} else {
 x_596 = x_586;
 lean_ctor_set_tag(x_596, 1);
}
lean_ctor_set(x_596, 0, x_593);
x_508 = x_555;
x_509 = x_547;
x_510 = x_585;
x_511 = x_596;
x_512 = x_595;
x_513 = x_556;
x_514 = x_2;
x_515 = x_10;
x_516 = lean_box(0);
goto block_536;
}
else
{
lean_object* x_597; 
lean_dec(x_595);
lean_dec_ref(x_593);
lean_dec(x_586);
lean_dec_ref(x_585);
x_597 = lean_box(0);
x_508 = x_555;
x_509 = x_547;
x_510 = x_597;
x_511 = x_597;
x_512 = x_597;
x_513 = x_557;
x_514 = x_2;
x_515 = x_10;
x_516 = lean_box(0);
goto block_536;
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec_ref(x_593);
lean_dec(x_586);
lean_dec_ref(x_585);
lean_dec_ref(x_555);
lean_dec_ref(x_547);
lean_dec(x_507);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_598 = lean_ctor_get(x_594, 0);
lean_inc(x_598);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 x_599 = x_594;
} else {
 lean_dec_ref(x_594);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 1, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_598);
return x_600;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_589);
lean_dec(x_586);
lean_dec_ref(x_585);
lean_dec_ref(x_555);
lean_dec_ref(x_547);
lean_dec(x_507);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_601 = lean_ctor_get(x_590, 0);
lean_inc(x_601);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_602 = x_590;
} else {
 lean_dec_ref(x_590);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(1, 1, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_601);
return x_603;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_586);
lean_dec_ref(x_585);
lean_dec_ref(x_555);
lean_dec_ref(x_547);
lean_dec(x_507);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_604 = lean_ctor_get(x_588, 0);
lean_inc(x_604);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 x_605 = x_588;
} else {
 lean_dec_ref(x_588);
 x_605 = lean_box(0);
}
if (lean_is_scalar(x_605)) {
 x_606 = lean_alloc_ctor(1, 1, 0);
} else {
 x_606 = x_605;
}
lean_ctor_set(x_606, 0, x_604);
return x_606;
}
}
else
{
lean_object* x_607; 
lean_dec(x_586);
lean_dec(x_585);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_607 = lean_box(0);
x_508 = x_555;
x_509 = x_547;
x_510 = x_607;
x_511 = x_607;
x_512 = x_607;
x_513 = x_556;
x_514 = x_2;
x_515 = x_10;
x_516 = lean_box(0);
goto block_536;
}
}
else
{
lean_dec_ref(x_555);
lean_dec_ref(x_547);
lean_dec(x_507);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_584;
}
}
}
else
{
lean_dec(x_552);
lean_dec_ref(x_547);
lean_dec(x_507);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_553;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec_ref(x_547);
lean_dec(x_507);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_608 = lean_ctor_get(x_551, 0);
lean_inc(x_608);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 x_609 = x_551;
} else {
 lean_dec_ref(x_551);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(1, 1, 0);
} else {
 x_610 = x_609;
}
lean_ctor_set(x_610, 0, x_608);
return x_610;
}
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_507);
lean_dec_ref(x_503);
lean_dec_ref(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_611 = lean_ctor_get(x_546, 0);
lean_inc(x_611);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 x_612 = x_546;
} else {
 lean_dec_ref(x_546);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 1, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_611);
return x_613;
}
}
else
{
lean_object* x_614; 
lean_dec_ref(x_503);
lean_dec_ref(x_486);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_614 = lean_box(0);
x_537 = x_614;
x_538 = x_614;
x_539 = x_2;
x_540 = x_10;
x_541 = lean_box(0);
goto block_544;
}
block_536:
{
lean_object* x_517; 
x_517 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_514, x_515);
lean_dec_ref(x_515);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
lean_dec_ref(x_517);
x_519 = lean_ctor_get(x_518, 0);
lean_inc_ref(x_519);
lean_dec(x_518);
x_520 = lean_array_get_size(x_519);
lean_dec_ref(x_519);
x_521 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8;
x_522 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10;
x_523 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_1);
lean_ctor_set(x_523, 2, x_483);
lean_ctor_set(x_523, 3, x_492);
lean_ctor_set(x_523, 4, x_488);
lean_ctor_set(x_523, 5, x_500);
lean_ctor_set(x_523, 6, x_495);
lean_ctor_set(x_523, 7, x_497);
lean_ctor_set(x_523, 8, x_509);
lean_ctor_set(x_523, 9, x_510);
lean_ctor_set(x_523, 10, x_511);
lean_ctor_set(x_523, 11, x_512);
lean_ctor_set(x_523, 12, x_507);
lean_ctor_set(x_523, 13, x_508);
lean_ctor_set(x_523, 14, x_521);
lean_ctor_set(x_523, 15, x_522);
lean_ctor_set(x_523, 16, x_522);
lean_ctor_set(x_523, 17, x_522);
lean_ctor_set(x_523, 18, x_521);
lean_ctor_set(x_523, 19, x_521);
lean_ctor_set(x_523, 20, x_521);
lean_ctor_set(x_523, 21, x_502);
lean_ctor_set_uint8(x_523, sizeof(void*)*22, x_513);
x_524 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(x_524, 0, x_523);
x_525 = l_Lean_Meta_Grind_Order_orderExt;
x_526 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_525, x_524, x_514);
lean_dec(x_514);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 x_527 = x_526;
} else {
 lean_dec_ref(x_526);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_528 = lean_alloc_ctor(1, 1, 0);
} else {
 x_528 = x_493;
}
lean_ctor_set(x_528, 0, x_520);
if (lean_is_scalar(x_527)) {
 x_529 = lean_alloc_ctor(0, 1, 0);
} else {
 x_529 = x_527;
}
lean_ctor_set(x_529, 0, x_528);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_493);
x_530 = lean_ctor_get(x_526, 0);
lean_inc(x_530);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 x_531 = x_526;
} else {
 lean_dec_ref(x_526);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 1, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_530);
return x_532;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_514);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_483);
lean_dec_ref(x_1);
x_533 = lean_ctor_get(x_517, 0);
lean_inc(x_533);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 x_534 = x_517;
} else {
 lean_dec_ref(x_517);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 1, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_533);
return x_535;
}
}
block_544:
{
lean_object* x_542; uint8_t x_543; 
x_542 = lean_box(0);
x_543 = 0;
lean_inc_n(x_537, 2);
x_508 = x_538;
x_509 = x_537;
x_510 = x_542;
x_511 = x_537;
x_512 = x_537;
x_513 = x_543;
x_514 = x_539;
x_515 = x_540;
x_516 = lean_box(0);
goto block_536;
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec_ref(x_503);
lean_dec(x_500);
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec_ref(x_486);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_615 = lean_ctor_get(x_506, 0);
lean_inc(x_615);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 x_616 = x_506;
} else {
 lean_dec_ref(x_506);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 1, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_615);
return x_617;
}
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_497);
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec_ref(x_486);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_618 = lean_ctor_get(x_499, 0);
lean_inc(x_618);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 x_619 = x_499;
} else {
 lean_dec_ref(x_499);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(1, 1, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_618);
return x_620;
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec_ref(x_486);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_621 = lean_ctor_get(x_496, 0);
lean_inc(x_621);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 x_622 = x_496;
} else {
 lean_dec_ref(x_496);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(1, 1, 0);
} else {
 x_623 = x_622;
}
lean_ctor_set(x_623, 0, x_621);
return x_623;
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_488);
lean_dec_ref(x_486);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_624 = lean_ctor_get(x_494, 0);
lean_inc(x_624);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 x_625 = x_494;
} else {
 lean_dec_ref(x_494);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(1, 1, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_624);
return x_626;
}
}
else
{
lean_object* x_627; lean_object* x_628; 
lean_dec(x_490);
lean_dec(x_488);
lean_dec_ref(x_486);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_627 = lean_box(0);
if (lean_is_scalar(x_491)) {
 x_628 = lean_alloc_ctor(0, 1, 0);
} else {
 x_628 = x_491;
}
lean_ctor_set(x_628, 0, x_627);
return x_628;
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_488);
lean_dec_ref(x_486);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_629 = lean_ctor_get(x_489, 0);
lean_inc(x_629);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 x_630 = x_489;
} else {
 lean_dec_ref(x_489);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(1, 1, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_629);
return x_631;
}
}
else
{
lean_object* x_632; lean_object* x_633; 
lean_dec(x_486);
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_632 = lean_box(0);
if (lean_is_scalar(x_487)) {
 x_633 = lean_alloc_ctor(0, 1, 0);
} else {
 x_633 = x_487;
}
lean_ctor_set(x_633, 0, x_632);
return x_633;
}
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_483);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_634 = lean_ctor_get(x_485, 0);
lean_inc(x_634);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 x_635 = x_485;
} else {
 lean_dec_ref(x_485);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 1, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_634);
return x_636;
}
}
}
else
{
lean_object* x_637; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_637 = lean_box(0);
lean_ctor_set(x_13, 0, x_637);
return x_13;
}
}
else
{
lean_object* x_638; 
x_638 = lean_ctor_get(x_13, 0);
lean_inc(x_638);
lean_dec(x_13);
if (lean_obj_tag(x_638) == 1)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 x_640 = x_638;
} else {
 lean_dec_ref(x_638);
 x_640 = lean_box(0);
}
x_641 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_639);
x_642 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_641, x_639, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; lean_object* x_644; 
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 x_644 = x_642;
} else {
 lean_dec_ref(x_642);
 x_644 = lean_box(0);
}
if (lean_obj_tag(x_643) == 1)
{
lean_object* x_645; lean_object* x_646; 
lean_dec(x_644);
x_645 = lean_ctor_get(x_643, 0);
lean_inc(x_645);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_643);
lean_inc_ref(x_1);
lean_inc(x_639);
x_646 = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(x_639, x_1, x_643, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 x_648 = x_646;
} else {
 lean_dec_ref(x_646);
 x_648 = lean_box(0);
}
if (lean_obj_tag(x_647) == 1)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_648);
x_649 = lean_ctor_get(x_647, 0);
lean_inc(x_649);
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 x_650 = x_647;
} else {
 lean_dec_ref(x_647);
 x_650 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_643);
lean_inc_ref(x_1);
lean_inc(x_639);
x_651 = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(x_639, x_1, x_643, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
lean_dec_ref(x_651);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_643);
lean_inc_ref(x_1);
lean_inc(x_639);
x_653 = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(x_639, x_1, x_643, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
lean_dec_ref(x_653);
x_655 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_639);
x_656 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(x_655, x_639, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
lean_dec_ref(x_656);
x_658 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5));
x_659 = lean_box(0);
lean_inc(x_639);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_639);
lean_ctor_set(x_660, 1, x_659);
lean_inc_ref(x_660);
x_661 = l_Lean_mkConst(x_658, x_660);
lean_inc(x_645);
lean_inc_ref(x_1);
x_662 = l_Lean_mkAppB(x_661, x_1, x_645);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_663 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_662, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
lean_dec_ref(x_663);
if (lean_obj_tag(x_657) == 1)
{
lean_object* x_702; lean_object* x_703; 
x_702 = lean_ctor_get(x_657, 0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_657);
lean_inc_ref(x_1);
lean_inc(x_639);
x_703 = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(x_639, x_1, x_657, x_643, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; 
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
lean_dec_ref(x_703);
if (lean_obj_tag(x_704) == 0)
{
lean_dec_ref(x_660);
lean_dec(x_640);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_694 = x_704;
x_695 = x_704;
x_696 = x_2;
x_697 = x_10;
x_698 = lean_box(0);
goto block_701;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_705 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__12));
x_706 = l_Lean_mkConst(x_705, x_660);
lean_inc(x_702);
lean_inc_ref(x_1);
x_707 = l_Lean_mkAppB(x_706, x_1, x_702);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_708 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(x_707, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
lean_dec_ref(x_708);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_710 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; lean_object* x_712; uint8_t x_713; uint8_t x_714; 
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
lean_dec_ref(x_710);
if (lean_is_scalar(x_640)) {
 x_712 = lean_alloc_ctor(1, 1, 0);
} else {
 x_712 = x_640;
}
lean_ctor_set(x_712, 0, x_709);
x_713 = 0;
x_714 = 1;
if (lean_obj_tag(x_711) == 1)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_711, 0);
lean_inc(x_715);
x_716 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set_uint8(x_716, sizeof(void*)*1, x_713);
x_717 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_716, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
lean_dec_ref(x_717);
x_719 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_718, x_716, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_718);
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
lean_dec_ref(x_719);
x_721 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_716, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
lean_dec_ref(x_721);
x_723 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(x_722, x_716, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_716);
lean_dec(x_722);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 x_725 = x_723;
} else {
 lean_dec_ref(x_723);
 x_725 = lean_box(0);
}
x_726 = lean_ctor_get(x_720, 3);
lean_inc_ref(x_726);
lean_dec(x_720);
x_727 = lean_ctor_get(x_724, 4);
lean_inc_ref(x_727);
lean_dec(x_724);
lean_inc_ref(x_10);
lean_inc(x_649);
lean_inc(x_702);
lean_inc(x_645);
lean_inc_ref(x_1);
lean_inc(x_639);
x_728 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_639, x_1, x_727, x_645, x_702, x_649, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; 
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
lean_dec_ref(x_728);
if (lean_obj_tag(x_729) == 1)
{
lean_object* x_730; 
if (lean_is_scalar(x_725)) {
 x_730 = lean_alloc_ctor(1, 1, 0);
} else {
 x_730 = x_725;
 lean_ctor_set_tag(x_730, 1);
}
lean_ctor_set(x_730, 0, x_726);
x_665 = x_712;
x_666 = x_704;
x_667 = x_711;
x_668 = x_730;
x_669 = x_729;
x_670 = x_714;
x_671 = x_2;
x_672 = x_10;
x_673 = lean_box(0);
goto block_693;
}
else
{
lean_object* x_731; 
lean_dec(x_729);
lean_dec_ref(x_726);
lean_dec(x_725);
lean_dec_ref(x_711);
x_731 = lean_box(0);
x_665 = x_712;
x_666 = x_704;
x_667 = x_731;
x_668 = x_731;
x_669 = x_731;
x_670 = x_714;
x_671 = x_2;
x_672 = x_10;
x_673 = lean_box(0);
goto block_693;
}
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec_ref(x_726);
lean_dec(x_725);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_704);
lean_dec(x_664);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_639);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_732 = lean_ctor_get(x_728, 0);
lean_inc(x_732);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 x_733 = x_728;
} else {
 lean_dec_ref(x_728);
 x_733 = lean_box(0);
}
if (lean_is_scalar(x_733)) {
 x_734 = lean_alloc_ctor(1, 1, 0);
} else {
 x_734 = x_733;
}
lean_ctor_set(x_734, 0, x_732);
return x_734;
}
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_720);
lean_dec_ref(x_716);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_704);
lean_dec(x_664);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_735 = lean_ctor_get(x_721, 0);
lean_inc(x_735);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 x_736 = x_721;
} else {
 lean_dec_ref(x_721);
 x_736 = lean_box(0);
}
if (lean_is_scalar(x_736)) {
 x_737 = lean_alloc_ctor(1, 1, 0);
} else {
 x_737 = x_736;
}
lean_ctor_set(x_737, 0, x_735);
return x_737;
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec_ref(x_716);
lean_dec_ref(x_712);
lean_dec_ref(x_711);
lean_dec_ref(x_704);
lean_dec(x_664);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_738 = lean_ctor_get(x_717, 0);
lean_inc(x_738);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 x_739 = x_717;
} else {
 lean_dec_ref(x_717);
 x_739 = lean_box(0);
}
if (lean_is_scalar(x_739)) {
 x_740 = lean_alloc_ctor(1, 1, 0);
} else {
 x_740 = x_739;
}
lean_ctor_set(x_740, 0, x_738);
return x_740;
}
}
else
{
lean_object* x_741; 
lean_dec(x_711);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_741 = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; 
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 x_743 = x_741;
} else {
 lean_dec_ref(x_741);
 x_743 = lean_box(0);
}
if (lean_obj_tag(x_742) == 1)
{
lean_object* x_744; lean_object* x_745; 
x_744 = lean_ctor_get(x_742, 0);
x_745 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_744, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; lean_object* x_747; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
lean_dec_ref(x_745);
x_747 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_744, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
lean_dec_ref(x_747);
x_749 = lean_ctor_get(x_746, 4);
lean_inc_ref(x_749);
lean_dec(x_746);
x_750 = lean_ctor_get(x_748, 3);
lean_inc_ref(x_750);
lean_dec(x_748);
lean_inc_ref(x_10);
lean_inc(x_649);
lean_inc(x_702);
lean_inc(x_645);
lean_inc_ref(x_1);
lean_inc(x_639);
x_751 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(x_639, x_1, x_749, x_645, x_702, x_649, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
lean_dec_ref(x_751);
if (lean_obj_tag(x_752) == 1)
{
lean_object* x_753; 
if (lean_is_scalar(x_743)) {
 x_753 = lean_alloc_ctor(1, 1, 0);
} else {
 x_753 = x_743;
 lean_ctor_set_tag(x_753, 1);
}
lean_ctor_set(x_753, 0, x_750);
x_665 = x_712;
x_666 = x_704;
x_667 = x_742;
x_668 = x_753;
x_669 = x_752;
x_670 = x_713;
x_671 = x_2;
x_672 = x_10;
x_673 = lean_box(0);
goto block_693;
}
else
{
lean_object* x_754; 
lean_dec(x_752);
lean_dec_ref(x_750);
lean_dec(x_743);
lean_dec_ref(x_742);
x_754 = lean_box(0);
x_665 = x_712;
x_666 = x_704;
x_667 = x_754;
x_668 = x_754;
x_669 = x_754;
x_670 = x_714;
x_671 = x_2;
x_672 = x_10;
x_673 = lean_box(0);
goto block_693;
}
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; 
lean_dec_ref(x_750);
lean_dec(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_712);
lean_dec_ref(x_704);
lean_dec(x_664);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_639);
lean_dec_ref(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
x_755 = lean_ctor_get(x_751, 0);
lean_inc(x_755);
if (lean_is_exclusive(x_751)) {
 lean_ctor_release(x_751, 0);
 x_756 = x_751;
} else {
 lean_dec_ref(x_751);
 x_756 = lean_box(0);
}
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(1, 1, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_755);
return x_757;
}
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_746);
lean_dec(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_712);
lean_dec_ref(x_704);
lean_dec(x_664);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_758 = lean_ctor_get(x_747, 0);
lean_inc(x_758);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 x_759 = x_747;
} else {
 lean_dec_ref(x_747);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(1, 1, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_758);
return x_760;
}
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_dec(x_743);
lean_dec_ref(x_742);
lean_dec_ref(x_712);
lean_dec_ref(x_704);
lean_dec(x_664);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_761 = lean_ctor_get(x_745, 0);
lean_inc(x_761);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 x_762 = x_745;
} else {
 lean_dec_ref(x_745);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(1, 1, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_761);
return x_763;
}
}
else
{
lean_object* x_764; 
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_764 = lean_box(0);
x_665 = x_712;
x_666 = x_704;
x_667 = x_764;
x_668 = x_764;
x_669 = x_764;
x_670 = x_713;
x_671 = x_2;
x_672 = x_10;
x_673 = lean_box(0);
goto block_693;
}
}
else
{
lean_dec_ref(x_712);
lean_dec_ref(x_704);
lean_dec(x_664);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_741;
}
}
}
else
{
lean_dec(x_709);
lean_dec_ref(x_704);
lean_dec(x_664);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_710;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
lean_dec_ref(x_704);
lean_dec(x_664);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_765 = lean_ctor_get(x_708, 0);
lean_inc(x_765);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 x_766 = x_708;
} else {
 lean_dec_ref(x_708);
 x_766 = lean_box(0);
}
if (lean_is_scalar(x_766)) {
 x_767 = lean_alloc_ctor(1, 1, 0);
} else {
 x_767 = x_766;
}
lean_ctor_set(x_767, 0, x_765);
return x_767;
}
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_664);
lean_dec_ref(x_660);
lean_dec_ref(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_768 = lean_ctor_get(x_703, 0);
lean_inc(x_768);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 x_769 = x_703;
} else {
 lean_dec_ref(x_703);
 x_769 = lean_box(0);
}
if (lean_is_scalar(x_769)) {
 x_770 = lean_alloc_ctor(1, 1, 0);
} else {
 x_770 = x_769;
}
lean_ctor_set(x_770, 0, x_768);
return x_770;
}
}
else
{
lean_object* x_771; 
lean_dec_ref(x_660);
lean_dec_ref(x_643);
lean_dec(x_640);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_771 = lean_box(0);
x_694 = x_771;
x_695 = x_771;
x_696 = x_2;
x_697 = x_10;
x_698 = lean_box(0);
goto block_701;
}
block_693:
{
lean_object* x_674; 
x_674 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_671, x_672);
lean_dec_ref(x_672);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
lean_dec_ref(x_674);
x_676 = lean_ctor_get(x_675, 0);
lean_inc_ref(x_676);
lean_dec(x_675);
x_677 = lean_array_get_size(x_676);
lean_dec_ref(x_676);
x_678 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8;
x_679 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10;
x_680 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_1);
lean_ctor_set(x_680, 2, x_639);
lean_ctor_set(x_680, 3, x_649);
lean_ctor_set(x_680, 4, x_645);
lean_ctor_set(x_680, 5, x_657);
lean_ctor_set(x_680, 6, x_652);
lean_ctor_set(x_680, 7, x_654);
lean_ctor_set(x_680, 8, x_666);
lean_ctor_set(x_680, 9, x_667);
lean_ctor_set(x_680, 10, x_668);
lean_ctor_set(x_680, 11, x_669);
lean_ctor_set(x_680, 12, x_664);
lean_ctor_set(x_680, 13, x_665);
lean_ctor_set(x_680, 14, x_678);
lean_ctor_set(x_680, 15, x_679);
lean_ctor_set(x_680, 16, x_679);
lean_ctor_set(x_680, 17, x_679);
lean_ctor_set(x_680, 18, x_678);
lean_ctor_set(x_680, 19, x_678);
lean_ctor_set(x_680, 20, x_678);
lean_ctor_set(x_680, 21, x_659);
lean_ctor_set_uint8(x_680, sizeof(void*)*22, x_670);
x_681 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(x_681, 0, x_680);
x_682 = l_Lean_Meta_Grind_Order_orderExt;
x_683 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_682, x_681, x_671);
lean_dec(x_671);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 x_684 = x_683;
} else {
 lean_dec_ref(x_683);
 x_684 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_685 = lean_alloc_ctor(1, 1, 0);
} else {
 x_685 = x_650;
}
lean_ctor_set(x_685, 0, x_677);
if (lean_is_scalar(x_684)) {
 x_686 = lean_alloc_ctor(0, 1, 0);
} else {
 x_686 = x_684;
}
lean_ctor_set(x_686, 0, x_685);
return x_686;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_650);
x_687 = lean_ctor_get(x_683, 0);
lean_inc(x_687);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 x_688 = x_683;
} else {
 lean_dec_ref(x_683);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(1, 1, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_687);
return x_689;
}
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; 
lean_dec(x_671);
lean_dec(x_669);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec(x_639);
lean_dec_ref(x_1);
x_690 = lean_ctor_get(x_674, 0);
lean_inc(x_690);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 x_691 = x_674;
} else {
 lean_dec_ref(x_674);
 x_691 = lean_box(0);
}
if (lean_is_scalar(x_691)) {
 x_692 = lean_alloc_ctor(1, 1, 0);
} else {
 x_692 = x_691;
}
lean_ctor_set(x_692, 0, x_690);
return x_692;
}
}
block_701:
{
lean_object* x_699; uint8_t x_700; 
x_699 = lean_box(0);
x_700 = 0;
lean_inc_n(x_694, 2);
x_665 = x_695;
x_666 = x_694;
x_667 = x_699;
x_668 = x_694;
x_669 = x_694;
x_670 = x_700;
x_671 = x_696;
x_672 = x_697;
x_673 = lean_box(0);
goto block_693;
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec_ref(x_660);
lean_dec(x_657);
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec_ref(x_643);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_772 = lean_ctor_get(x_663, 0);
lean_inc(x_772);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 x_773 = x_663;
} else {
 lean_dec_ref(x_663);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_773)) {
 x_774 = lean_alloc_ctor(1, 1, 0);
} else {
 x_774 = x_773;
}
lean_ctor_set(x_774, 0, x_772);
return x_774;
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec_ref(x_643);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_775 = lean_ctor_get(x_656, 0);
lean_inc(x_775);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 x_776 = x_656;
} else {
 lean_dec_ref(x_656);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_777 = lean_alloc_ctor(1, 1, 0);
} else {
 x_777 = x_776;
}
lean_ctor_set(x_777, 0, x_775);
return x_777;
}
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec_ref(x_643);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_778 = lean_ctor_get(x_653, 0);
lean_inc(x_778);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 x_779 = x_653;
} else {
 lean_dec_ref(x_653);
 x_779 = lean_box(0);
}
if (lean_is_scalar(x_779)) {
 x_780 = lean_alloc_ctor(1, 1, 0);
} else {
 x_780 = x_779;
}
lean_ctor_set(x_780, 0, x_778);
return x_780;
}
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_645);
lean_dec_ref(x_643);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_781 = lean_ctor_get(x_651, 0);
lean_inc(x_781);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 x_782 = x_651;
} else {
 lean_dec_ref(x_651);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(1, 1, 0);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_781);
return x_783;
}
}
else
{
lean_object* x_784; lean_object* x_785; 
lean_dec(x_647);
lean_dec(x_645);
lean_dec_ref(x_643);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_784 = lean_box(0);
if (lean_is_scalar(x_648)) {
 x_785 = lean_alloc_ctor(0, 1, 0);
} else {
 x_785 = x_648;
}
lean_ctor_set(x_785, 0, x_784);
return x_785;
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
lean_dec(x_645);
lean_dec_ref(x_643);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_786 = lean_ctor_get(x_646, 0);
lean_inc(x_786);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 x_787 = x_646;
} else {
 lean_dec_ref(x_646);
 x_787 = lean_box(0);
}
if (lean_is_scalar(x_787)) {
 x_788 = lean_alloc_ctor(1, 1, 0);
} else {
 x_788 = x_787;
}
lean_ctor_set(x_788, 0, x_786);
return x_788;
}
}
else
{
lean_object* x_789; lean_object* x_790; 
lean_dec(x_643);
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_789 = lean_box(0);
if (lean_is_scalar(x_644)) {
 x_790 = lean_alloc_ctor(0, 1, 0);
} else {
 x_790 = x_644;
}
lean_ctor_set(x_790, 0, x_789);
return x_790;
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
lean_dec(x_640);
lean_dec(x_639);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_791 = lean_ctor_get(x_642, 0);
lean_inc(x_791);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 x_792 = x_642;
} else {
 lean_dec_ref(x_642);
 x_792 = lean_box(0);
}
if (lean_is_scalar(x_792)) {
 x_793 = lean_alloc_ctor(1, 1, 0);
} else {
 x_793 = x_792;
}
lean_ctor_set(x_793, 0, x_791);
return x_793;
}
}
else
{
lean_object* x_794; lean_object* x_795; 
lean_dec(x_638);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_794 = lean_box(0);
x_795 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_795, 0, x_794);
return x_795;
}
}
}
else
{
uint8_t x_796; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_796 = !lean_is_exclusive(x_13);
if (x_796 == 0)
{
return x_13;
}
else
{
lean_object* x_797; lean_object* x_798; 
x_797 = lean_ctor_get(x_13, 0);
lean_inc(x_797);
lean_dec(x_13);
x_798 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_798, 0, x_797);
return x_798;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(x_5, x_1, x_2);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_12 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(x_8, x_1, x_2);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 26);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; 
lean_free_object(x_13);
x_18 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_21);
lean_dec(x_20);
x_22 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(x_21, x_1);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; 
lean_dec(x_22);
lean_free_object(x_18);
lean_inc(x_2);
lean_inc_ref(x_1);
x_24 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_Grind_Order_orderExt;
x_28 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_27, x_26, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_25);
return x_28;
}
else
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_25);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_24;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_35, 1);
lean_inc_ref(x_36);
lean_dec(x_35);
x_37 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(x_36, x_1);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_37);
lean_inc(x_2);
lean_inc_ref(x_1);
x_40 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_41);
x_42 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_Grind_Order_orderExt;
x_44 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_43, x_42, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_45 = x_44;
} else {
 lean_dec_ref(x_44);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_41);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_41);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_40;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
return x_18;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_18, 0);
lean_inc(x_51);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
lean_dec(x_13);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*11 + 26);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
lean_dec(x_58);
x_61 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(x_60, x_1);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_59);
lean_inc(x_2);
lean_inc_ref(x_1);
x_64 = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc(x_65);
x_66 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_66, 0, x_1);
lean_closure_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_Grind_Order_orderExt;
x_68 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_67, x_66, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_69 = x_68;
} else {
 lean_dec_ref(x_68);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_65);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_65);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_72 = x_68;
} else {
 lean_dec_ref(x_68);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_64;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_74 = lean_ctor_get(x_57, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_75 = x_57;
} else {
 lean_dec_ref(x_57);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_13);
if (x_77 == 0)
{
return x_13;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_13, 0);
lean_inc(x_78);
lean_dec(x_13);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Order_getStructId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_StructId(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6);
l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7);
l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8);
l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9);
l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
