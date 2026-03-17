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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Order_orderExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_13_; 
lean_inc(v_a_7_);
v___x_13_ = lean_grind_canon(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_14_, v_a_7_);
lean_dec(v_a_7_);
return v___x_15_;
}
else
{
lean_dec(v_a_7_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___boxed(lean_object* v_e_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(v_e_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(lean_object* v_fn_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(v_fn_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___boxed(lean_object* v_fn_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(v_fn_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(lean_object* v_declName_55_, lean_object* v_u_56_, lean_object* v_type_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_63_ = lean_box(0);
v___x_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_64_, 0, v_u_56_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = l_Lean_mkConst(v_declName_55_, v___x_64_);
v___x_66_ = l_Lean_Expr_app___override(v___x_65_, v_type_57_);
v___x_67_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_66_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg___boxed(lean_object* v_declName_68_, lean_object* v_u_69_, lean_object* v_type_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v_declName_68_, v_u_69_, v_type_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f(lean_object* v_declName_77_, lean_object* v_u_78_, lean_object* v_type_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v_declName_77_, v_u_78_, v_type_79_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___boxed(lean_object* v_declName_92_, lean_object* v_u_93_, lean_object* v_type_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f(v_declName_92_, v_u_93_, v_type_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec(v_a_95_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(lean_object* v_u_114_, lean_object* v_00_u03b1_115_, lean_object* v_semiringInst_116_, lean_object* v_leInst_117_, lean_object* v_ltInst_118_, lean_object* v_isPreorderInst_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_e_129_; lean_object* v___x_130_; 
v___x_125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3));
v___x_126_ = lean_box(0);
v___x_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_127_, 0, v_u_114_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = l_Lean_mkConst(v___x_125_, v___x_127_);
v_e_129_ = l_Lean_mkApp5(v___x_128_, v_00_u03b1_115_, v_semiringInst_116_, v_leInst_117_, v_ltInst_118_, v_isPreorderInst_119_);
v___x_130_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_e_129_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_131_, lean_object* v_00_u03b1_132_, lean_object* v_semiringInst_133_, lean_object* v_leInst_134_, lean_object* v_ltInst_135_, lean_object* v_isPreorderInst_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_u_131_, v_00_u03b1_132_, v_semiringInst_133_, v_leInst_134_, v_ltInst_135_, v_isPreorderInst_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(lean_object* v_u_143_, lean_object* v_00_u03b1_144_, lean_object* v_semiringInst_145_, lean_object* v_leInst_146_, lean_object* v_ltInst_147_, lean_object* v_isPreorderInst_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_u_143_, v_00_u03b1_144_, v_semiringInst_145_, v_leInst_146_, v_ltInst_147_, v_isPreorderInst_148_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_161_ = _args[0];
lean_object* v_00_u03b1_162_ = _args[1];
lean_object* v_semiringInst_163_ = _args[2];
lean_object* v_leInst_164_ = _args[3];
lean_object* v_ltInst_165_ = _args[4];
lean_object* v_isPreorderInst_166_ = _args[5];
lean_object* v_a_167_ = _args[6];
lean_object* v_a_168_ = _args[7];
lean_object* v_a_169_ = _args[8];
lean_object* v_a_170_ = _args[9];
lean_object* v_a_171_ = _args[10];
lean_object* v_a_172_ = _args[11];
lean_object* v_a_173_ = _args[12];
lean_object* v_a_174_ = _args[13];
lean_object* v_a_175_ = _args[14];
lean_object* v_a_176_ = _args[15];
lean_object* v_a_177_ = _args[16];
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(v_u_161_, v_00_u03b1_162_, v_semiringInst_163_, v_leInst_164_, v_ltInst_165_, v_isPreorderInst_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec(v_a_167_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f_spec__0(lean_object* v_msg_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = l_Lean_instInhabitedExpr;
v___x_181_ = lean_panic_fn(v___x_180_, v_msg_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0(lean_object* v___x_182_, lean_object* v_s_183_){
_start:
{
lean_object* v_structs_184_; lean_object* v_typeIdOf_185_; lean_object* v_exprToStructId_186_; lean_object* v_termMap_187_; lean_object* v_termMapInv_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_196_; 
v_structs_184_ = lean_ctor_get(v_s_183_, 0);
v_typeIdOf_185_ = lean_ctor_get(v_s_183_, 1);
v_exprToStructId_186_ = lean_ctor_get(v_s_183_, 2);
v_termMap_187_ = lean_ctor_get(v_s_183_, 3);
v_termMapInv_188_ = lean_ctor_get(v_s_183_, 4);
v_isSharedCheck_196_ = !lean_is_exclusive(v_s_183_);
if (v_isSharedCheck_196_ == 0)
{
v___x_190_ = v_s_183_;
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_termMapInv_188_);
lean_inc(v_termMap_187_);
lean_inc(v_exprToStructId_186_);
lean_inc(v_typeIdOf_185_);
lean_inc(v_structs_184_);
lean_dec(v_s_183_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = lean_array_push(v_structs_184_, v___x_182_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_192_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_typeIdOf_185_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_exprToStructId_186_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_termMap_187_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v_termMapInv_188_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(lean_object* v_____do__lift_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_toRing_210_; lean_object* v___x_211_; 
v_toRing_210_ = lean_ctor_get(v_____do__lift_197_, 0);
lean_inc_ref(v_toRing_210_);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v_toRing_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1___boxed(lean_object* v_____do__lift_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_____do__lift_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec_ref(v_____do__lift_212_);
return v_res_225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_unsigned_to_nat(32u);
v___x_237_ = lean_mk_empty_array_with_capacity(v___x_236_);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7(void){
_start:
{
size_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_239_ = ((size_t)5ULL);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_unsigned_to_nat(32u);
v___x_242_ = lean_mk_empty_array_with_capacity(v___x_241_);
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6);
v___x_244_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
lean_ctor_set(v___x_244_, 2, v___x_240_);
lean_ctor_set(v___x_244_, 3, v___x_240_);
lean_ctor_set_usize(v___x_244_, 4, v___x_239_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(lean_object* v_type_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc_ref(v_type_252_);
v___x_264_ = l_Lean_Meta_getDecLevel_x3f(v_type_252_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_542_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_542_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_542_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_542_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
if (lean_obj_tag(v_a_265_) == 1)
{
lean_object* v_val_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_537_; 
lean_del_object(v___x_267_);
v_val_269_ = lean_ctor_get(v_a_265_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_a_265_);
if (v_isSharedCheck_537_ == 0)
{
v___x_271_ = v_a_265_;
v_isShared_272_ = v_isSharedCheck_537_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_val_269_);
lean_dec(v_a_265_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_537_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1));
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc_ref(v_type_252_);
lean_inc(v_val_269_);
v___x_274_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v___x_273_, v_val_269_, v_type_252_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_528_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_528_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_528_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_528_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
if (lean_obj_tag(v_a_275_) == 1)
{
lean_object* v_val_279_; lean_object* v___x_280_; 
lean_del_object(v___x_277_);
v_val_279_ = lean_ctor_get(v_a_275_, 0);
lean_inc(v_val_279_);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc_ref(v_a_275_);
lean_inc_ref(v_type_252_);
lean_inc(v_val_269_);
v___x_280_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_269_, v_type_252_, v_a_275_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_515_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_515_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_515_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_515_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
if (lean_obj_tag(v_a_281_) == 1)
{
lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_510_; 
lean_del_object(v___x_283_);
v_val_285_ = lean_ctor_get(v_a_281_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_a_281_);
if (v_isSharedCheck_510_ == 0)
{
v___x_287_ = v_a_281_;
v_isShared_288_ = v_isSharedCheck_510_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_dec(v_a_281_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_510_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; 
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc_ref(v_a_275_);
lean_inc_ref(v_type_252_);
lean_inc(v_val_269_);
v___x_289_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_val_269_, v_type_252_, v_a_275_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_291_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref(v___x_289_);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc_ref(v_a_275_);
lean_inc_ref(v_type_252_);
lean_inc(v_val_269_);
v___x_291_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_val_269_, v_type_252_, v_a_275_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref(v___x_291_);
v___x_293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3));
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc_ref(v_type_252_);
lean_inc(v_val_269_);
v___x_294_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v___x_293_, v_val_269_, v_type_252_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref(v___x_294_);
v___x_296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5));
v___x_297_ = lean_box(0);
lean_inc(v_val_269_);
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v_val_269_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_inc_ref(v___x_298_);
v___x_299_ = l_Lean_mkConst(v___x_296_, v___x_298_);
lean_inc(v_val_279_);
lean_inc_ref(v_type_252_);
v___x_300_ = l_Lean_mkAppB(v___x_299_, v_type_252_, v_val_279_);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
lean_inc(v_a_256_);
lean_inc_ref(v_a_255_);
lean_inc(v_a_254_);
lean_inc(v_a_253_);
v___x_301_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(v___x_300_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v_fst_306_; lean_object* v_fst_307_; lean_object* v_fst_308_; uint8_t v_snd_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___y_352_; lean_object* v___y_353_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref(v___x_301_);
if (lean_obj_tag(v_a_295_) == 1)
{
lean_object* v_val_356_; lean_object* v___x_357_; 
v_val_356_ = lean_ctor_get(v_a_295_, 0);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc_ref(v_a_295_);
lean_inc_ref(v_type_252_);
lean_inc(v_val_269_);
v___x_357_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_val_269_, v_type_252_, v_a_295_, v_a_275_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
if (lean_obj_tag(v_a_358_) == 0)
{
lean_dec_ref(v___x_298_);
lean_del_object(v___x_271_);
lean_dec(v_a_262_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
v_fst_350_ = v_a_358_;
v_snd_351_ = v_a_358_;
v___y_352_ = v_a_253_;
v___y_353_ = v_a_261_;
goto v___jp_349_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11));
v___x_360_ = l_Lean_mkConst(v___x_359_, v___x_298_);
lean_inc(v_val_356_);
lean_inc_ref(v_type_252_);
v___x_361_ = l_Lean_mkAppB(v___x_360_, v_type_252_, v_val_356_);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
lean_inc(v_a_256_);
lean_inc_ref(v_a_255_);
lean_inc(v_a_254_);
lean_inc(v_a_253_);
v___x_362_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(v___x_361_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref(v___x_362_);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
lean_inc(v_a_256_);
lean_inc_ref(v_a_255_);
lean_inc(v_a_254_);
lean_inc(v_a_253_);
lean_inc_ref(v_type_252_);
v___x_364_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref(v___x_364_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v_a_363_);
v___x_367_ = v___x_271_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_363_);
v___x_367_ = v_reuseFailAlloc_460_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
uint8_t v___x_368_; uint8_t v___x_369_; 
v___x_368_ = 0;
v___x_369_ = 1;
if (lean_obj_tag(v_a_365_) == 1)
{
lean_object* v_val_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_val_370_ = lean_ctor_get(v_a_365_, 0);
lean_inc(v_val_370_);
v___x_371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_371_, 0, v_val_370_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_368_);
v___x_372_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_371_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref(v___x_372_);
v___x_374_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_a_373_, v___x_371_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_373_);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref(v___x_374_);
v___x_376_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_371_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_399_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref(v___x_376_);
v___x_378_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_a_377_, v___x_371_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec_ref(v___x_371_);
lean_dec(v_a_377_);
v_a_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_399_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_399_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_399_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_ringInst_383_; lean_object* v_semiringInst_384_; lean_object* v___x_385_; 
v_ringInst_383_ = lean_ctor_get(v_a_375_, 3);
lean_inc_ref(v_ringInst_383_);
lean_dec(v_a_375_);
v_semiringInst_384_ = lean_ctor_get(v_a_379_, 4);
lean_inc_ref(v_semiringInst_384_);
lean_dec(v_a_379_);
lean_inc_ref(v_a_261_);
lean_inc(v_val_285_);
lean_inc(v_val_356_);
lean_inc(v_val_279_);
lean_inc_ref(v_type_252_);
lean_inc(v_val_269_);
v___x_385_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_val_269_, v_type_252_, v_semiringInst_384_, v_val_279_, v_val_356_, v_val_285_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v___x_385_);
if (lean_obj_tag(v_a_386_) == 1)
{
lean_object* v___x_388_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 1);
lean_ctor_set(v___x_381_, 0, v_ringInst_383_);
v___x_388_ = v___x_381_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_ringInst_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v___y_304_ = v_a_358_;
v___y_305_ = v___x_367_;
v_fst_306_ = v_a_365_;
v_fst_307_ = v___x_388_;
v_fst_308_ = v_a_386_;
v_snd_309_ = v___x_369_;
v___y_310_ = v_a_253_;
v___y_311_ = v_a_261_;
goto v___jp_303_;
}
}
else
{
lean_object* v___x_390_; 
lean_dec(v_a_386_);
lean_dec_ref(v_ringInst_383_);
lean_del_object(v___x_381_);
lean_dec_ref(v_a_365_);
v___x_390_ = lean_box(0);
v___y_304_ = v_a_358_;
v___y_305_ = v___x_367_;
v_fst_306_ = v___x_390_;
v_fst_307_ = v___x_390_;
v_fst_308_ = v___x_390_;
v_snd_309_ = v___x_369_;
v___y_310_ = v_a_253_;
v___y_311_ = v_a_261_;
goto v___jp_303_;
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v_ringInst_383_);
lean_del_object(v___x_381_);
lean_dec_ref(v_a_365_);
lean_dec_ref(v___x_367_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_dec(v_val_269_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_391_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_385_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_385_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_a_375_);
lean_dec_ref(v___x_371_);
lean_dec_ref(v_a_365_);
lean_dec_ref(v___x_367_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_400_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_376_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_376_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v___x_371_);
lean_dec_ref(v_a_365_);
lean_dec_ref(v___x_367_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_408_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_372_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_372_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
lean_object* v___x_416_; 
lean_dec(v_a_365_);
lean_inc(v_a_262_);
lean_inc_ref(v_a_261_);
lean_inc(v_a_260_);
lean_inc_ref(v_a_259_);
lean_inc(v_a_258_);
lean_inc_ref(v_a_257_);
lean_inc(v_a_256_);
lean_inc_ref(v_a_255_);
lean_inc(v_a_254_);
lean_inc(v_a_253_);
lean_inc_ref(v_type_252_);
v___x_416_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_459_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_459_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_459_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_459_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
if (lean_obj_tag(v_a_417_) == 1)
{
lean_object* v_val_421_; lean_object* v___x_422_; 
v_val_421_ = lean_ctor_get(v_a_417_, 0);
v___x_422_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_val_421_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref(v___x_422_);
v___x_424_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_val_421_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v_semiringInst_426_; lean_object* v_ringInst_427_; lean_object* v___x_428_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref(v___x_424_);
v_semiringInst_426_ = lean_ctor_get(v_a_423_, 4);
lean_inc_ref(v_semiringInst_426_);
lean_dec(v_a_423_);
v_ringInst_427_ = lean_ctor_get(v_a_425_, 3);
lean_inc_ref(v_ringInst_427_);
lean_dec(v_a_425_);
lean_inc_ref(v_a_261_);
lean_inc(v_val_285_);
lean_inc(v_val_356_);
lean_inc(v_val_279_);
lean_inc_ref(v_type_252_);
lean_inc(v_val_269_);
v___x_428_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_val_269_, v_type_252_, v_semiringInst_426_, v_val_279_, v_val_356_, v_val_285_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref(v___x_428_);
if (lean_obj_tag(v_a_429_) == 1)
{
lean_object* v___x_431_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 1);
lean_ctor_set(v___x_419_, 0, v_ringInst_427_);
v___x_431_ = v___x_419_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_ringInst_427_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v___y_304_ = v_a_358_;
v___y_305_ = v___x_367_;
v_fst_306_ = v_a_417_;
v_fst_307_ = v___x_431_;
v_fst_308_ = v_a_429_;
v_snd_309_ = v___x_368_;
v___y_310_ = v_a_253_;
v___y_311_ = v_a_261_;
goto v___jp_303_;
}
}
else
{
lean_object* v___x_433_; 
lean_dec(v_a_429_);
lean_dec_ref(v_ringInst_427_);
lean_dec_ref(v_a_417_);
lean_del_object(v___x_419_);
v___x_433_ = lean_box(0);
v___y_304_ = v_a_358_;
v___y_305_ = v___x_367_;
v_fst_306_ = v___x_433_;
v_fst_307_ = v___x_433_;
v_fst_308_ = v___x_433_;
v_snd_309_ = v___x_369_;
v___y_310_ = v_a_253_;
v___y_311_ = v_a_261_;
goto v___jp_303_;
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_ringInst_427_);
lean_dec_ref(v_a_417_);
lean_del_object(v___x_419_);
lean_dec_ref(v___x_367_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_dec(v_val_269_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_434_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_428_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_428_);
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
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec(v_a_423_);
lean_dec_ref(v_a_417_);
lean_del_object(v___x_419_);
lean_dec_ref(v___x_367_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_442_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_424_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_424_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
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
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec_ref(v_a_417_);
lean_del_object(v___x_419_);
lean_dec_ref(v___x_367_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_450_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_422_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_422_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
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
lean_object* v___x_458_; 
lean_del_object(v___x_419_);
lean_dec(v_a_417_);
lean_dec(v_a_262_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
v___x_458_ = lean_box(0);
v___y_304_ = v_a_358_;
v___y_305_ = v___x_367_;
v_fst_306_ = v___x_458_;
v_fst_307_ = v___x_458_;
v_fst_308_ = v___x_458_;
v_snd_309_ = v___x_368_;
v___y_310_ = v_a_253_;
v___y_311_ = v_a_261_;
goto v___jp_303_;
}
}
}
else
{
lean_dec_ref(v___x_367_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
return v___x_416_;
}
}
}
}
else
{
lean_dec(v_a_363_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
return v___x_364_;
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_461_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_362_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_362_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v_a_295_);
lean_dec(v_a_302_);
lean_dec_ref(v___x_298_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_469_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_357_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_357_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v___x_477_; 
lean_dec_ref(v___x_298_);
lean_dec_ref(v_a_275_);
lean_del_object(v___x_271_);
lean_dec(v_a_262_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
v___x_477_ = lean_box(0);
v_fst_350_ = v___x_477_;
v_snd_351_ = v___x_477_;
v___y_352_ = v_a_253_;
v___y_353_ = v_a_261_;
goto v___jp_349_;
}
v___jp_303_:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_310_, v___y_311_);
lean_dec_ref(v___y_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v_structs_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_312_);
v_structs_314_ = lean_ctor_get(v_a_313_, 0);
lean_inc_ref(v_structs_314_);
lean_dec(v_a_313_);
v___x_315_ = lean_array_get_size(v_structs_314_);
lean_dec_ref(v_structs_314_);
v___x_316_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7);
v___x_317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9);
v___x_318_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v___x_318_, 0, v___x_315_);
lean_ctor_set(v___x_318_, 1, v_type_252_);
lean_ctor_set(v___x_318_, 2, v_val_269_);
lean_ctor_set(v___x_318_, 3, v_val_285_);
lean_ctor_set(v___x_318_, 4, v_val_279_);
lean_ctor_set(v___x_318_, 5, v_a_295_);
lean_ctor_set(v___x_318_, 6, v_a_290_);
lean_ctor_set(v___x_318_, 7, v_a_292_);
lean_ctor_set(v___x_318_, 8, v___y_304_);
lean_ctor_set(v___x_318_, 9, v_fst_306_);
lean_ctor_set(v___x_318_, 10, v_fst_307_);
lean_ctor_set(v___x_318_, 11, v_fst_308_);
lean_ctor_set(v___x_318_, 12, v_a_302_);
lean_ctor_set(v___x_318_, 13, v___y_305_);
lean_ctor_set(v___x_318_, 14, v___x_316_);
lean_ctor_set(v___x_318_, 15, v___x_317_);
lean_ctor_set(v___x_318_, 16, v___x_317_);
lean_ctor_set(v___x_318_, 17, v___x_317_);
lean_ctor_set(v___x_318_, 18, v___x_316_);
lean_ctor_set(v___x_318_, 19, v___x_316_);
lean_ctor_set(v___x_318_, 20, v___x_316_);
lean_ctor_set(v___x_318_, 21, v___x_297_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*22, v_snd_309_);
v___f_319_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_319_, 0, v___x_318_);
v___x_320_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_321_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_320_, v___f_319_, v___y_310_);
lean_dec(v___y_310_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_331_; 
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v___x_321_, 0);
lean_dec(v_unused_332_);
v___x_323_ = v___x_321_;
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
else
{
lean_dec(v___x_321_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_315_);
v___x_326_ = v___x_287_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_315_);
v___x_326_ = v_reuseFailAlloc_330_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_326_);
v___x_328_ = v___x_323_;
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
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_del_object(v___x_287_);
v_a_333_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_321_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_321_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
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
lean_dec(v___y_310_);
lean_dec(v_fst_308_);
lean_dec(v_fst_307_);
lean_dec(v_fst_306_);
lean_dec(v___y_305_);
lean_dec(v___y_304_);
lean_dec(v_a_302_);
lean_dec(v_a_295_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_dec(v_val_269_);
lean_dec_ref(v_type_252_);
v_a_341_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_312_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_312_);
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
v___jp_349_:
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_box(0);
v___x_355_ = 0;
lean_inc_n(v_fst_350_, 2);
v___y_304_ = v_fst_350_;
v___y_305_ = v_snd_351_;
v_fst_306_ = v___x_354_;
v_fst_307_ = v_fst_350_;
v_fst_308_ = v_fst_350_;
v_snd_309_ = v___x_355_;
v___y_310_ = v___y_352_;
v___y_311_ = v___y_353_;
goto v___jp_303_;
}
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec_ref(v___x_298_);
lean_dec(v_a_295_);
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec_ref(v_a_275_);
lean_dec(v_val_279_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_478_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_301_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_301_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_a_292_);
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec(v_val_279_);
lean_dec_ref(v_a_275_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_486_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_294_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_294_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_a_290_);
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec_ref(v_a_275_);
lean_dec(v_val_279_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_494_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_291_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_291_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_del_object(v___x_287_);
lean_dec(v_val_285_);
lean_dec_ref(v_a_275_);
lean_dec(v_val_279_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_502_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_289_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_289_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_513_; 
lean_dec(v_a_281_);
lean_dec_ref(v_a_275_);
lean_dec(v_val_279_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v___x_511_ = lean_box(0);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_511_);
v___x_513_ = v___x_283_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v_val_279_);
lean_dec_ref(v_a_275_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_516_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_280_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_280_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_a_275_);
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v___x_524_ = lean_box(0);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_524_);
v___x_526_ = v___x_277_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_del_object(v___x_271_);
lean_dec(v_val_269_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_529_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_274_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_274_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_540_; 
lean_dec(v_a_265_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v___x_538_ = lean_box(0);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_538_);
v___x_540_ = v___x_267_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
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
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_type_252_);
v_a_543_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_264_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_264_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___boxed(lean_object* v_type_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(v_type_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_ks_568_; lean_object* v_vs_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_593_; 
v_ks_568_ = lean_ctor_get(v_x_564_, 0);
v_vs_569_ = lean_ctor_get(v_x_564_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_593_ == 0)
{
v___x_571_ = v_x_564_;
v_isShared_572_ = v_isSharedCheck_593_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_vs_569_);
lean_inc(v_ks_568_);
lean_dec(v_x_564_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_593_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = lean_array_get_size(v_ks_568_);
v___x_574_ = lean_nat_dec_lt(v_x_565_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
lean_dec(v_x_565_);
v___x_575_ = lean_array_push(v_ks_568_, v_x_566_);
v___x_576_ = lean_array_push(v_vs_569_, v_x_567_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v___x_576_);
lean_ctor_set(v___x_571_, 0, v___x_575_);
v___x_578_ = v___x_571_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
else
{
lean_object* v_k_x27_580_; uint8_t v___x_581_; 
v_k_x27_580_ = lean_array_fget_borrowed(v_ks_568_, v_x_565_);
v___x_581_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_566_, v_k_x27_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_583_; 
if (v_isShared_572_ == 0)
{
v___x_583_ = v___x_571_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_ks_568_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_vs_569_);
v___x_583_ = v_reuseFailAlloc_587_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_nat_add(v_x_565_, v___x_584_);
lean_dec(v_x_565_);
v_x_564_ = v___x_583_;
v_x_565_ = v___x_585_;
goto _start;
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = lean_array_fset(v_ks_568_, v_x_565_, v_x_566_);
v___x_589_ = lean_array_fset(v_vs_569_, v_x_565_, v_x_567_);
lean_dec(v_x_565_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v___x_589_);
lean_ctor_set(v___x_571_, 0, v___x_588_);
v___x_591_ = v___x_571_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_594_, lean_object* v_k_595_, lean_object* v_v_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_594_, v___x_597_, v_k_595_, v_v_596_);
return v___x_598_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; 
v___x_599_ = ((size_t)5ULL);
v___x_600_ = ((size_t)1ULL);
v___x_601_ = lean_usize_shift_left(v___x_600_, v___x_599_);
return v___x_601_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; 
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0);
v___x_604_ = lean_usize_sub(v___x_603_, v___x_602_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(lean_object* v_x_606_, size_t v_x_607_, size_t v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v_es_611_; size_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; lean_object* v_j_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_es_611_ = lean_ctor_get(v_x_606_, 0);
v___x_612_ = ((size_t)5ULL);
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1);
v___x_615_ = lean_usize_land(v_x_607_, v___x_614_);
v_j_616_ = lean_usize_to_nat(v___x_615_);
v___x_617_ = lean_array_get_size(v_es_611_);
v___x_618_ = lean_nat_dec_lt(v_j_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec(v_j_616_);
lean_dec(v_x_610_);
lean_dec_ref(v_x_609_);
return v_x_606_;
}
else
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_655_; 
lean_inc_ref(v_es_611_);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_606_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_x_606_, 0);
lean_dec(v_unused_656_);
v___x_620_ = v_x_606_;
v_isShared_621_ = v_isSharedCheck_655_;
goto v_resetjp_619_;
}
else
{
lean_dec(v_x_606_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_655_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_v_622_; lean_object* v___x_623_; lean_object* v_xs_x27_624_; lean_object* v___y_626_; 
v_v_622_ = lean_array_fget(v_es_611_, v_j_616_);
v___x_623_ = lean_box(0);
v_xs_x27_624_ = lean_array_fset(v_es_611_, v_j_616_, v___x_623_);
switch(lean_obj_tag(v_v_622_))
{
case 0:
{
lean_object* v_key_631_; lean_object* v_val_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_642_; 
v_key_631_ = lean_ctor_get(v_v_622_, 0);
v_val_632_ = lean_ctor_get(v_v_622_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_v_622_);
if (v_isSharedCheck_642_ == 0)
{
v___x_634_ = v_v_622_;
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_val_632_);
lean_inc(v_key_631_);
lean_dec(v_v_622_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; 
v___x_636_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_609_, v_key_631_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_del_object(v___x_634_);
v___x_637_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_631_, v_val_632_, v_x_609_, v_x_610_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
v___y_626_ = v___x_638_;
goto v___jp_625_;
}
else
{
lean_object* v___x_640_; 
lean_dec(v_val_632_);
lean_dec(v_key_631_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v_x_610_);
lean_ctor_set(v___x_634_, 0, v_x_609_);
v___x_640_ = v___x_634_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_x_609_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_x_610_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
v___y_626_ = v___x_640_;
goto v___jp_625_;
}
}
}
}
case 1:
{
lean_object* v_node_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_653_; 
v_node_643_ = lean_ctor_get(v_v_622_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_v_622_);
if (v_isSharedCheck_653_ == 0)
{
v___x_645_ = v_v_622_;
v_isShared_646_ = v_isSharedCheck_653_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_node_643_);
lean_dec(v_v_622_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_653_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_647_ = lean_usize_shift_right(v_x_607_, v___x_612_);
v___x_648_ = lean_usize_add(v_x_608_, v___x_613_);
v___x_649_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_node_643_, v___x_647_, v___x_648_, v_x_609_, v_x_610_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_649_);
v___x_651_ = v___x_645_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v___y_626_ = v___x_651_;
goto v___jp_625_;
}
}
}
default: 
{
lean_object* v___x_654_; 
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v_x_609_);
lean_ctor_set(v___x_654_, 1, v_x_610_);
v___y_626_ = v___x_654_;
goto v___jp_625_;
}
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_array_fset(v_xs_x27_624_, v_j_616_, v___y_626_);
lean_dec(v_j_616_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_627_);
v___x_629_ = v___x_620_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
else
{
lean_object* v_ks_657_; lean_object* v_vs_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_678_; 
v_ks_657_ = lean_ctor_get(v_x_606_, 0);
v_vs_658_ = lean_ctor_get(v_x_606_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_x_606_);
if (v_isSharedCheck_678_ == 0)
{
v___x_660_ = v_x_606_;
v_isShared_661_ = v_isSharedCheck_678_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_vs_658_);
lean_inc(v_ks_657_);
lean_dec(v_x_606_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_678_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_ks_657_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_vs_658_);
v___x_663_ = v_reuseFailAlloc_677_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v_newNode_664_; uint8_t v___y_666_; size_t v___x_672_; uint8_t v___x_673_; 
v_newNode_664_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(v___x_663_, v_x_609_, v_x_610_);
v___x_672_ = ((size_t)7ULL);
v___x_673_ = lean_usize_dec_le(v___x_672_, v_x_608_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_674_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_664_);
v___x_675_ = lean_unsigned_to_nat(4u);
v___x_676_ = lean_nat_dec_lt(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
v___y_666_ = v___x_676_;
goto v___jp_665_;
}
else
{
v___y_666_ = v___x_673_;
goto v___jp_665_;
}
v___jp_665_:
{
if (v___y_666_ == 0)
{
lean_object* v_ks_667_; lean_object* v_vs_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_ks_667_ = lean_ctor_get(v_newNode_664_, 0);
lean_inc_ref(v_ks_667_);
v_vs_668_ = lean_ctor_get(v_newNode_664_, 1);
lean_inc_ref(v_vs_668_);
lean_dec_ref(v_newNode_664_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2);
v___x_671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_x_608_, v_ks_667_, v_vs_668_, v___x_669_, v___x_670_);
lean_dec_ref(v_vs_668_);
lean_dec_ref(v_ks_667_);
return v___x_671_;
}
else
{
return v_newNode_664_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_679_, lean_object* v_keys_680_, lean_object* v_vals_681_, lean_object* v_i_682_, lean_object* v_entries_683_){
_start:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_array_get_size(v_keys_680_);
v___x_685_ = lean_nat_dec_lt(v_i_682_, v___x_684_);
if (v___x_685_ == 0)
{
lean_dec(v_i_682_);
return v_entries_683_;
}
else
{
lean_object* v_k_686_; lean_object* v_v_687_; uint64_t v___x_688_; size_t v_h_689_; size_t v___x_690_; lean_object* v___x_691_; size_t v___x_692_; size_t v___x_693_; size_t v___x_694_; size_t v_h_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_k_686_ = lean_array_fget_borrowed(v_keys_680_, v_i_682_);
v_v_687_ = lean_array_fget_borrowed(v_vals_681_, v_i_682_);
v___x_688_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_686_);
v_h_689_ = lean_uint64_to_usize(v___x_688_);
v___x_690_ = ((size_t)5ULL);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_sub(v_depth_679_, v___x_692_);
v___x_694_ = lean_usize_mul(v___x_690_, v___x_693_);
v_h_695_ = lean_usize_shift_right(v_h_689_, v___x_694_);
v___x_696_ = lean_nat_add(v_i_682_, v___x_691_);
lean_dec(v_i_682_);
lean_inc(v_v_687_);
lean_inc(v_k_686_);
v___x_697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_entries_683_, v_h_695_, v_depth_679_, v_k_686_, v_v_687_);
v_i_682_ = v___x_696_;
v_entries_683_ = v___x_697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_699_, lean_object* v_keys_700_, lean_object* v_vals_701_, lean_object* v_i_702_, lean_object* v_entries_703_){
_start:
{
size_t v_depth_boxed_704_; lean_object* v_res_705_; 
v_depth_boxed_704_ = lean_unbox_usize(v_depth_699_);
lean_dec(v_depth_699_);
v_res_705_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_704_, v_keys_700_, v_vals_701_, v_i_702_, v_entries_703_);
lean_dec_ref(v_vals_701_);
lean_dec_ref(v_keys_700_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_706_, lean_object* v_x_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
size_t v_x_5733__boxed_711_; size_t v_x_5734__boxed_712_; lean_object* v_res_713_; 
v_x_5733__boxed_711_ = lean_unbox_usize(v_x_707_);
lean_dec(v_x_707_);
v_x_5734__boxed_712_ = lean_unbox_usize(v_x_708_);
lean_dec(v_x_708_);
v_res_713_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_706_, v_x_5733__boxed_711_, v_x_5734__boxed_712_, v_x_709_, v_x_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
uint64_t v___x_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_717_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_715_);
v___x_718_ = lean_uint64_to_usize(v___x_717_);
v___x_719_ = ((size_t)1ULL);
v___x_720_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_714_, v___x_718_, v___x_719_, v_x_715_, v_x_716_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0(lean_object* v_type_721_, lean_object* v_a_722_, lean_object* v_s_723_){
_start:
{
lean_object* v_structs_724_; lean_object* v_typeIdOf_725_; lean_object* v_exprToStructId_726_; lean_object* v_termMap_727_; lean_object* v_termMapInv_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
v_structs_724_ = lean_ctor_get(v_s_723_, 0);
v_typeIdOf_725_ = lean_ctor_get(v_s_723_, 1);
v_exprToStructId_726_ = lean_ctor_get(v_s_723_, 2);
v_termMap_727_ = lean_ctor_get(v_s_723_, 3);
v_termMapInv_728_ = lean_ctor_get(v_s_723_, 4);
v_isSharedCheck_736_ = !lean_is_exclusive(v_s_723_);
if (v_isSharedCheck_736_ == 0)
{
v___x_730_ = v_s_723_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_termMapInv_728_);
lean_inc(v_termMap_727_);
lean_inc(v_exprToStructId_726_);
lean_inc(v_typeIdOf_725_);
lean_inc(v_structs_724_);
lean_dec(v_s_723_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(v_typeIdOf_725_, v_type_721_, v_a_722_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_structs_724_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_exprToStructId_726_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_termMap_727_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v_termMapInv_728_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_737_, lean_object* v_vals_738_, lean_object* v_i_739_, lean_object* v_k_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_keys_737_);
v___x_742_ = lean_nat_dec_lt(v_i_739_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v_i_739_);
v___x_743_ = lean_box(0);
return v___x_743_;
}
else
{
lean_object* v_k_x27_744_; uint8_t v___x_745_; 
v_k_x27_744_ = lean_array_fget_borrowed(v_keys_737_, v_i_739_);
v___x_745_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_740_, v_k_x27_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_i_739_, v___x_746_);
lean_dec(v_i_739_);
v_i_739_ = v___x_747_;
goto _start;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_array_fget_borrowed(v_vals_738_, v_i_739_);
lean_dec(v_i_739_);
lean_inc(v___x_749_);
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_751_, lean_object* v_vals_752_, lean_object* v_i_753_, lean_object* v_k_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_751_, v_vals_752_, v_i_753_, v_k_754_);
lean_dec_ref(v_k_754_);
lean_dec_ref(v_vals_752_);
lean_dec_ref(v_keys_751_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_756_, size_t v_x_757_, lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
lean_object* v_es_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_780_; 
v_es_759_ = lean_ctor_get(v_x_756_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_x_756_);
if (v_isSharedCheck_780_ == 0)
{
v___x_761_ = v_x_756_;
v_isShared_762_ = v_isSharedCheck_780_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_es_759_);
lean_dec(v_x_756_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_780_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v_j_767_; lean_object* v___x_768_; 
v___x_763_ = lean_box(2);
v___x_764_ = ((size_t)5ULL);
v___x_765_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1);
v___x_766_ = lean_usize_land(v_x_757_, v___x_765_);
v_j_767_ = lean_usize_to_nat(v___x_766_);
v___x_768_ = lean_array_get(v___x_763_, v_es_759_, v_j_767_);
lean_dec(v_j_767_);
lean_dec_ref(v_es_759_);
switch(lean_obj_tag(v___x_768_))
{
case 0:
{
lean_object* v_key_769_; lean_object* v_val_770_; uint8_t v___x_771_; 
v_key_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_key_769_);
v_val_770_ = lean_ctor_get(v___x_768_, 1);
lean_inc(v_val_770_);
lean_dec_ref(v___x_768_);
v___x_771_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_758_, v_key_769_);
lean_dec(v_key_769_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec(v_val_770_);
lean_del_object(v___x_761_);
v___x_772_ = lean_box(0);
return v___x_772_;
}
else
{
lean_object* v___x_774_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 1);
lean_ctor_set(v___x_761_, 0, v_val_770_);
v___x_774_ = v___x_761_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_val_770_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
case 1:
{
lean_object* v_node_776_; size_t v___x_777_; 
lean_del_object(v___x_761_);
v_node_776_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_node_776_);
lean_dec_ref(v___x_768_);
v___x_777_ = lean_usize_shift_right(v_x_757_, v___x_764_);
v_x_756_ = v_node_776_;
v_x_757_ = v___x_777_;
goto _start;
}
default: 
{
lean_object* v___x_779_; 
lean_del_object(v___x_761_);
v___x_779_ = lean_box(0);
return v___x_779_;
}
}
}
}
else
{
lean_object* v_ks_781_; lean_object* v_vs_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_ks_781_ = lean_ctor_get(v_x_756_, 0);
lean_inc_ref(v_ks_781_);
v_vs_782_ = lean_ctor_get(v_x_756_, 1);
lean_inc_ref(v_vs_782_);
lean_dec_ref(v_x_756_);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_781_, v_vs_782_, v___x_783_, v_x_758_);
lean_dec_ref(v_vs_782_);
lean_dec_ref(v_ks_781_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
size_t v_x_5951__boxed_788_; lean_object* v_res_789_; 
v_x_5951__boxed_788_ = lean_unbox_usize(v_x_786_);
lean_dec(v_x_786_);
v_res_789_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_785_, v_x_5951__boxed_788_, v_x_787_);
lean_dec_ref(v_x_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
uint64_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_791_);
v___x_793_ = lean_uint64_to_usize(v___x_792_);
v___x_794_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_790_, v___x_793_, v_x_791_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_x_795_, v_x_796_);
lean_dec_ref(v_x_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f(lean_object* v_type_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_801_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_861_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_861_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_861_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_861_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v_order_815_; 
v_order_815_ = lean_ctor_get_uint8(v_a_811_, sizeof(void*)*11 + 27);
lean_dec(v_a_811_);
if (v_order_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_818_; 
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_type_798_);
v___x_816_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
else
{
lean_object* v___x_820_; 
lean_del_object(v___x_813_);
v___x_820_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_799_, v_a_807_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_852_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_852_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_852_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_852_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_typeIdOf_825_; lean_object* v___x_826_; 
v_typeIdOf_825_ = lean_ctor_get(v_a_821_, 1);
lean_inc_ref(v_typeIdOf_825_);
lean_dec(v_a_821_);
v___x_826_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_typeIdOf_825_, v_type_798_);
if (lean_obj_tag(v___x_826_) == 1)
{
lean_object* v_val_827_; lean_object* v___x_829_; 
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_type_798_);
v_val_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_827_);
lean_dec_ref(v___x_826_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_val_827_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_val_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_object* v___x_831_; 
lean_dec(v___x_826_);
lean_del_object(v___x_823_);
lean_inc(v_a_799_);
lean_inc_ref(v_type_798_);
v___x_831_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(v_type_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___f_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref(v___x_831_);
lean_inc(v_a_832_);
v___f_833_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_833_, 0, v_type_798_);
lean_closure_set(v___f_833_, 1, v_a_832_);
v___x_834_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_835_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_834_, v___f_833_, v_a_799_);
lean_dec(v_a_799_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v___x_835_, 0);
lean_dec(v_unused_843_);
v___x_837_ = v___x_835_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_dec(v___x_835_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v_a_832_);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_832_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_a_832_);
v_a_844_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_835_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_835_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_dec(v_a_799_);
lean_dec_ref(v_type_798_);
return v___x_831_;
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_type_798_);
v_a_853_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_820_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_820_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_type_798_);
v_a_862_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_810_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_810_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___boxed(lean_object* v_type_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Meta_Grind_Order_getStructId_x3f(v_type_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(lean_object* v_00_u03b2_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_x_884_, v_x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(v_00_u03b2_887_, v_x_888_, v_x_889_);
lean_dec_ref(v_x_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1(lean_object* v_00_u03b2_891_, lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(v_x_892_, v_x_893_, v_x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_896_, lean_object* v_x_897_, size_t v_x_898_, lean_object* v_x_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_897_, v_x_898_, v_x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
size_t v_x_6191__boxed_905_; lean_object* v_res_906_; 
v_x_6191__boxed_905_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_res_906_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(v_00_u03b2_901_, v_x_902_, v_x_6191__boxed_905_, v_x_904_);
lean_dec_ref(v_x_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(lean_object* v_00_u03b2_907_, lean_object* v_x_908_, size_t v_x_909_, size_t v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_908_, v_x_909_, v_x_910_, v_x_911_, v_x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_914_, lean_object* v_x_915_, lean_object* v_x_916_, lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
size_t v_x_6202__boxed_920_; size_t v_x_6203__boxed_921_; lean_object* v_res_922_; 
v_x_6202__boxed_920_ = lean_unbox_usize(v_x_916_);
lean_dec(v_x_916_);
v_x_6203__boxed_921_ = lean_unbox_usize(v_x_917_);
lean_dec(v_x_917_);
v_res_922_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(v_00_u03b2_914_, v_x_915_, v_x_6202__boxed_920_, v_x_6203__boxed_921_, v_x_918_, v_x_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_923_, lean_object* v_keys_924_, lean_object* v_vals_925_, lean_object* v_heq_926_, lean_object* v_i_927_, lean_object* v_k_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_924_, v_vals_925_, v_i_927_, v_k_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_heq_933_, lean_object* v_i_934_, lean_object* v_k_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_930_, v_keys_931_, v_vals_932_, v_heq_933_, v_i_934_, v_k_935_);
lean_dec_ref(v_k_935_);
lean_dec_ref(v_vals_932_);
lean_dec_ref(v_keys_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_937_, lean_object* v_n_938_, lean_object* v_k_939_, lean_object* v_v_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(v_n_938_, v_k_939_, v_v_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_942_, size_t v_depth_943_, lean_object* v_keys_944_, lean_object* v_vals_945_, lean_object* v_heq_946_, lean_object* v_i_947_, lean_object* v_entries_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_943_, v_keys_944_, v_vals_945_, v_i_947_, v_entries_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_950_, lean_object* v_depth_951_, lean_object* v_keys_952_, lean_object* v_vals_953_, lean_object* v_heq_954_, lean_object* v_i_955_, lean_object* v_entries_956_){
_start:
{
size_t v_depth_boxed_957_; lean_object* v_res_958_; 
v_depth_boxed_957_ = lean_unbox_usize(v_depth_951_);
lean_dec(v_depth_951_);
v_res_958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_950_, v_depth_boxed_957_, v_keys_952_, v_vals_953_, v_heq_954_, v_i_955_, v_entries_956_);
lean_dec_ref(v_vals_953_);
lean_dec_ref(v_keys_952_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_960_, v_x_961_, v_x_962_, v_x_963_);
return v___x_964_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Order_StructId(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
}
#ifdef __cplusplus
}
#endif
