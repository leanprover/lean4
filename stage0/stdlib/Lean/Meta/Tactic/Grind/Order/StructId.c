// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.StructId
// Imports: public import Lean.Meta.Tactic.Grind.Order.Types import Lean.Meta.Tactic.Grind.OrderInsts import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM import Lean.Meta.DecLevel import Lean.OrderLevel
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
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Order_orderExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_Sym_canon(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v___x_9_, 1);
v___x_11_ = l_Lean_Meta_Sym_shareCommon(v_a_10_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
return v___x_11_;
}
else
{
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg___boxed(lean_object* v_e_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v_e_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
lean_dec(v_a_18_);
lean_dec_ref(v_a_17_);
lean_dec(v_a_16_);
lean_dec_ref(v_a_15_);
lean_dec(v_a_14_);
lean_dec_ref(v_a_13_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(lean_object* v_e_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v_e_21_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___boxed(lean_object* v_e_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(v_e_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec(v_a_35_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___redArg(lean_object* v_fn_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v_fn_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___redArg___boxed(lean_object* v_fn_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___redArg(v_fn_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(lean_object* v_fn_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v_fn_65_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___boxed(lean_object* v_fn_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(v_fn_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(lean_object* v_declName_91_, lean_object* v_u_92_, lean_object* v_type_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = lean_box(0);
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v_u_92_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = l_Lean_mkConst(v_declName_91_, v___x_101_);
v___x_103_ = l_Lean_Expr_app___override(v___x_102_, v_type_93_);
v___x_104_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_103_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg___boxed(lean_object* v_declName_105_, lean_object* v_u_106_, lean_object* v_type_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v_declName_105_, v_u_106_, v_type_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f(lean_object* v_declName_115_, lean_object* v_u_116_, lean_object* v_type_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v_declName_115_, v_u_116_, v_type_117_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___boxed(lean_object* v_declName_130_, lean_object* v_u_131_, lean_object* v_type_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f(v_declName_130_, v_u_131_, v_type_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec(v_a_133_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(lean_object* v_u_152_, lean_object* v_00_u03b1_153_, lean_object* v_semiringInst_154_, lean_object* v_leInst_155_, lean_object* v_ltInst_156_, lean_object* v_isPreorderInst_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_e_168_; lean_object* v___x_169_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3));
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_166_, 0, v_u_152_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_Lean_mkConst(v___x_164_, v___x_166_);
v_e_168_ = l_Lean_mkApp5(v___x_167_, v_00_u03b1_153_, v_semiringInst_154_, v_leInst_155_, v_ltInst_156_, v_isPreorderInst_157_);
v___x_169_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_168_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_170_, lean_object* v_00_u03b1_171_, lean_object* v_semiringInst_172_, lean_object* v_leInst_173_, lean_object* v_ltInst_174_, lean_object* v_isPreorderInst_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_u_170_, v_00_u03b1_171_, v_semiringInst_172_, v_leInst_173_, v_ltInst_174_, v_isPreorderInst_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(lean_object* v_u_183_, lean_object* v_00_u03b1_184_, lean_object* v_semiringInst_185_, lean_object* v_leInst_186_, lean_object* v_ltInst_187_, lean_object* v_isPreorderInst_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_u_183_, v_00_u03b1_184_, v_semiringInst_185_, v_leInst_186_, v_ltInst_187_, v_isPreorderInst_188_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_201_ = _args[0];
lean_object* v_00_u03b1_202_ = _args[1];
lean_object* v_semiringInst_203_ = _args[2];
lean_object* v_leInst_204_ = _args[3];
lean_object* v_ltInst_205_ = _args[4];
lean_object* v_isPreorderInst_206_ = _args[5];
lean_object* v_a_207_ = _args[6];
lean_object* v_a_208_ = _args[7];
lean_object* v_a_209_ = _args[8];
lean_object* v_a_210_ = _args[9];
lean_object* v_a_211_ = _args[10];
lean_object* v_a_212_ = _args[11];
lean_object* v_a_213_ = _args[12];
lean_object* v_a_214_ = _args[13];
lean_object* v_a_215_ = _args[14];
lean_object* v_a_216_ = _args[15];
lean_object* v_a_217_ = _args[16];
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(v_u_201_, v_00_u03b1_202_, v_semiringInst_203_, v_leInst_204_, v_ltInst_205_, v_isPreorderInst_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec(v_a_207_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f_spec__0(lean_object* v_msg_219_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = l_Lean_instInhabitedExpr;
v___x_221_ = lean_panic_fn_borrowed(v___x_220_, v_msg_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0(lean_object* v___x_222_, lean_object* v_s_223_){
_start:
{
lean_object* v_structs_224_; lean_object* v_typeIdOf_225_; lean_object* v_exprToStructId_226_; lean_object* v_termMap_227_; lean_object* v_termMapInv_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_236_; 
v_structs_224_ = lean_ctor_get(v_s_223_, 0);
v_typeIdOf_225_ = lean_ctor_get(v_s_223_, 1);
v_exprToStructId_226_ = lean_ctor_get(v_s_223_, 2);
v_termMap_227_ = lean_ctor_get(v_s_223_, 3);
v_termMapInv_228_ = lean_ctor_get(v_s_223_, 4);
v_isSharedCheck_236_ = !lean_is_exclusive(v_s_223_);
if (v_isSharedCheck_236_ == 0)
{
v___x_230_ = v_s_223_;
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_termMapInv_228_);
lean_inc(v_termMap_227_);
lean_inc(v_exprToStructId_226_);
lean_inc(v_typeIdOf_225_);
lean_inc(v_structs_224_);
lean_dec(v_s_223_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_array_push(v_structs_224_, v___x_222_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_232_);
v___x_234_ = v___x_230_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_typeIdOf_225_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_exprToStructId_226_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_termMap_227_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_termMapInv_228_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(lean_object* v_____do__lift_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_toRing_250_; lean_object* v___x_251_; 
v_toRing_250_ = lean_ctor_get(v_____do__lift_237_, 0);
lean_inc_ref(v_toRing_250_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v_toRing_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1___boxed(lean_object* v_____do__lift_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_____do__lift_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec_ref(v_____do__lift_252_);
return v_res_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_unsigned_to_nat(32u);
v___x_267_ = lean_mk_empty_array_with_capacity(v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1(void){
_start:
{
size_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_269_ = ((size_t)5ULL);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_unsigned_to_nat(32u);
v___x_272_ = lean_mk_empty_array_with_capacity(v___x_271_);
v___x_273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0);
v___x_274_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_270_);
lean_ctor_set(v___x_274_, 3, v___x_270_);
lean_ctor_set_usize(v___x_274_, 4, v___x_269_);
return v___x_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_275_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(lean_object* v_type_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v_fst_314_; lean_object* v_fst_315_; lean_object* v_fst_316_; uint8_t v_snd_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___x_370_; 
v___x_370_ = l_Lean_leCarrierIsSort(v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; uint8_t v___x_372_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; uint8_t v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v_val_441_; uint8_t v___x_667_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = 1;
v___x_667_ = lean_unbox(v_a_371_);
lean_dec(v_a_371_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_inc_ref(v_type_292_);
v___x_668_ = l_Lean_Meta_getDecLevel_x3f(v_type_292_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_678_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_678_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_678_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_678_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
if (lean_obj_tag(v_a_669_) == 1)
{
lean_object* v_val_673_; 
lean_del_object(v___x_671_);
v_val_673_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v_a_669_, 1);
v_val_441_ = v_val_673_;
goto v___jp_440_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_676_; 
lean_dec(v_a_669_);
lean_dec_ref(v_type_292_);
v___x_674_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_674_);
v___x_676_ = v___x_671_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_type_292_);
v_a_679_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_668_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_668_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v___x_687_; 
lean_inc_ref(v_type_292_);
v___x_687_ = l_Lean_Meta_getLevel(v_type_292_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = l_Lean_Meta_normalizeLevel(v_a_688_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v_val_441_ = v_a_690_;
goto v___jp_440_;
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v_type_292_);
v_a_691_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_689_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_type_292_);
v_a_699_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_687_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_687_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
v___jp_373_:
{
lean_object* v___x_394_; 
lean_inc_ref(v___y_391_);
lean_inc_ref(v___y_384_);
lean_inc_ref(v_type_292_);
v___x_394_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v___y_383_, v_type_292_, v___y_377_, v___y_384_, v___y_393_, v___y_391_, v___y_388_, v___y_389_, v___y_378_, v___y_375_, v___y_387_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
if (lean_obj_tag(v_a_395_) == 1)
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v___y_374_);
v___y_305_ = v___y_384_;
v___y_306_ = v___y_386_;
v___y_307_ = v___y_385_;
v___y_308_ = v___y_376_;
v___y_309_ = v___y_380_;
v___y_310_ = v___y_390_;
v___y_311_ = v___y_391_;
v___y_312_ = v___y_381_;
v___y_313_ = v___y_382_;
v_fst_314_ = v___y_392_;
v_fst_315_ = v___x_396_;
v_fst_316_ = v_a_395_;
v_snd_317_ = v___x_372_;
v___y_318_ = v___y_379_;
v___y_319_ = v___y_375_;
goto v___jp_304_;
}
else
{
lean_object* v___x_397_; 
lean_dec(v_a_395_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_374_);
v___x_397_ = lean_box(0);
v___y_305_ = v___y_384_;
v___y_306_ = v___y_386_;
v___y_307_ = v___y_385_;
v___y_308_ = v___y_376_;
v___y_309_ = v___y_380_;
v___y_310_ = v___y_390_;
v___y_311_ = v___y_391_;
v___y_312_ = v___y_381_;
v___y_313_ = v___y_382_;
v_fst_314_ = v___x_397_;
v_fst_315_ = v___x_397_;
v_fst_316_ = v___x_397_;
v_snd_317_ = v___x_372_;
v___y_318_ = v___y_379_;
v___y_319_ = v___y_375_;
goto v___jp_304_;
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_374_);
lean_dec_ref(v_type_292_);
v_a_398_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_394_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_394_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
v___jp_406_:
{
lean_object* v___x_428_; 
lean_inc_ref(v___y_425_);
lean_inc_ref(v___y_416_);
lean_inc_ref(v_type_292_);
v___x_428_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v___y_415_, v_type_292_, v___y_420_, v___y_416_, v___y_427_, v___y_425_, v___y_421_, v___y_422_, v___y_410_, v___y_408_, v___y_419_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
if (lean_obj_tag(v_a_429_) == 1)
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v___y_423_);
v___y_305_ = v___y_416_;
v___y_306_ = v___y_418_;
v___y_307_ = v___y_417_;
v___y_308_ = v___y_409_;
v___y_309_ = v___y_412_;
v___y_310_ = v___y_424_;
v___y_311_ = v___y_425_;
v___y_312_ = v___y_413_;
v___y_313_ = v___y_414_;
v_fst_314_ = v___y_426_;
v_fst_315_ = v___x_430_;
v_fst_316_ = v_a_429_;
v_snd_317_ = v___y_407_;
v___y_318_ = v___y_411_;
v___y_319_ = v___y_408_;
goto v___jp_304_;
}
else
{
lean_object* v___x_431_; 
lean_dec(v_a_429_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_423_);
v___x_431_ = lean_box(0);
v___y_305_ = v___y_416_;
v___y_306_ = v___y_418_;
v___y_307_ = v___y_417_;
v___y_308_ = v___y_409_;
v___y_309_ = v___y_412_;
v___y_310_ = v___y_424_;
v___y_311_ = v___y_425_;
v___y_312_ = v___y_413_;
v___y_313_ = v___y_414_;
v_fst_314_ = v___x_431_;
v_fst_315_ = v___x_431_;
v_fst_316_ = v___x_431_;
v_snd_317_ = v___x_372_;
v___y_318_ = v___y_411_;
v___y_319_ = v___y_408_;
goto v___jp_304_;
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec_ref(v_type_292_);
v_a_432_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_428_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_428_);
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
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5));
lean_inc_ref(v_type_292_);
lean_inc(v_val_441_);
v___x_443_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v___x_442_, v_val_441_, v_type_292_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_658_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_658_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_658_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_658_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
if (lean_obj_tag(v_a_444_) == 1)
{
lean_object* v_val_448_; lean_object* v___x_449_; 
lean_del_object(v___x_446_);
v_val_448_ = lean_ctor_get(v_a_444_, 0);
lean_inc(v_val_448_);
lean_inc_ref(v_a_444_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_441_);
v___x_449_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_441_, v_type_292_, v_a_444_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_645_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_645_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_645_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_645_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
if (lean_obj_tag(v_a_450_) == 1)
{
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_640_; 
lean_del_object(v___x_452_);
v_val_454_ = lean_ctor_get(v_a_450_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_640_ == 0)
{
v___x_456_ = v_a_450_;
v_isShared_457_ = v_isSharedCheck_640_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v_a_450_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_640_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; 
lean_inc_ref(v_a_444_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_441_);
v___x_458_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_val_441_, v_type_292_, v_a_444_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
lean_inc_ref(v_a_444_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_441_);
v___x_460_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_val_441_, v_type_292_, v_a_444_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7));
lean_inc_ref(v_type_292_);
lean_inc(v_val_441_);
v___x_463_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v___x_462_, v_val_441_, v_type_292_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9));
v___x_466_ = lean_box(0);
lean_inc(v_val_441_);
v___x_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_467_, 0, v_val_441_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
lean_inc_ref(v___x_467_);
v___x_468_ = l_Lean_mkConst(v___x_465_, v___x_467_);
lean_inc(v_val_448_);
lean_inc_ref(v_type_292_);
v___x_469_ = l_Lean_mkAppB(v___x_468_, v_type_292_, v_val_448_);
v___x_470_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v___x_469_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_470_) == 0)
{
if (lean_obj_tag(v_a_464_) == 1)
{
lean_object* v_a_471_; lean_object* v_val_472_; lean_object* v___x_473_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v_val_472_ = lean_ctor_get(v_a_464_, 0);
lean_inc_ref(v_a_464_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_441_);
v___x_473_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_val_441_, v_type_292_, v_a_464_, v_a_444_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
if (lean_obj_tag(v_a_474_) == 0)
{
lean_dec_ref_known(v___x_467_, 2);
lean_del_object(v___x_456_);
v___y_357_ = v_val_448_;
v___y_358_ = v_val_441_;
v___y_359_ = v_a_459_;
v___y_360_ = v_a_461_;
v___y_361_ = v_a_464_;
v___y_362_ = v_val_454_;
v___y_363_ = v_a_471_;
v_fst_364_ = v_a_474_;
v_snd_365_ = v_a_474_;
v___y_366_ = v_a_293_;
v___y_367_ = v_a_301_;
goto v___jp_356_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11));
v___x_476_ = l_Lean_mkConst(v___x_475_, v___x_467_);
lean_inc(v_val_472_);
lean_inc_ref(v_type_292_);
v___x_477_ = l_Lean_mkAppB(v___x_476_, v_type_292_, v_val_472_);
v___x_478_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v___x_477_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
lean_inc_ref(v_type_292_);
v___x_480_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_a_479_);
v___x_483_ = v___x_456_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_479_);
v___x_483_ = v_reuseFailAlloc_589_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
uint8_t v___x_484_; 
v___x_484_ = 0;
if (lean_obj_tag(v_a_481_) == 1)
{
lean_object* v_val_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_val_485_ = lean_ctor_get(v_a_481_, 0);
lean_inc(v_val_485_);
v___x_486_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_486_, 0, v_val_485_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*1, v___x_484_);
v___x_487_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_486_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v_a_490_; lean_object* v___x_491_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_a_488_, v___x_486_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_488_);
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref(v___x_489_);
v___x_491_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_486_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; lean_object* v_a_494_; lean_object* v___x_495_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_a_492_, v___x_486_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec_ref_known(v___x_486_, 1);
lean_dec(v_a_492_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref(v___x_493_);
v___x_495_ = l_Lean_leCarrierIsSort(v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; uint8_t v___x_497_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = lean_unbox(v_a_496_);
lean_dec(v_a_496_);
if (v___x_497_ == 0)
{
lean_object* v_ringInst_498_; lean_object* v_semiringInst_499_; 
lean_inc(v_val_472_);
v_ringInst_498_ = lean_ctor_get(v_a_490_, 3);
lean_inc_ref(v_ringInst_498_);
lean_dec(v_a_490_);
v_semiringInst_499_ = lean_ctor_get(v_a_494_, 4);
lean_inc_ref(v_semiringInst_499_);
lean_dec(v_a_494_);
lean_inc(v_val_441_);
v___y_374_ = v_ringInst_498_;
v___y_375_ = v_a_301_;
v___y_376_ = v_a_461_;
v___y_377_ = v_semiringInst_499_;
v___y_378_ = v_a_300_;
v___y_379_ = v_a_293_;
v___y_380_ = v_a_464_;
v___y_381_ = v_a_474_;
v___y_382_ = v_a_471_;
v___y_383_ = v_val_441_;
v___y_384_ = v_val_448_;
v___y_385_ = v_val_441_;
v___y_386_ = v_a_459_;
v___y_387_ = v_a_302_;
v___y_388_ = v_a_298_;
v___y_389_ = v_a_299_;
v___y_390_ = v___x_483_;
v___y_391_ = v_val_454_;
v___y_392_ = v_a_481_;
v___y_393_ = v_val_472_;
goto v___jp_373_;
}
else
{
lean_object* v_ringInst_500_; lean_object* v_semiringInst_501_; lean_object* v___x_502_; 
v_ringInst_500_ = lean_ctor_get(v_a_490_, 3);
lean_inc_ref(v_ringInst_500_);
lean_dec(v_a_490_);
v_semiringInst_501_ = lean_ctor_get(v_a_494_, 4);
lean_inc_ref(v_semiringInst_501_);
lean_dec(v_a_494_);
lean_inc(v_val_441_);
v___x_502_ = l_Lean_Meta_decLevel_x3f(v_val_441_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
if (lean_obj_tag(v_a_503_) == 1)
{
lean_object* v_val_504_; 
lean_inc(v_val_472_);
v_val_504_ = lean_ctor_get(v_a_503_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v_a_503_, 1);
v___y_374_ = v_ringInst_500_;
v___y_375_ = v_a_301_;
v___y_376_ = v_a_461_;
v___y_377_ = v_semiringInst_501_;
v___y_378_ = v_a_300_;
v___y_379_ = v_a_293_;
v___y_380_ = v_a_464_;
v___y_381_ = v_a_474_;
v___y_382_ = v_a_471_;
v___y_383_ = v_val_504_;
v___y_384_ = v_val_448_;
v___y_385_ = v_val_441_;
v___y_386_ = v_a_459_;
v___y_387_ = v_a_302_;
v___y_388_ = v_a_298_;
v___y_389_ = v_a_299_;
v___y_390_ = v___x_483_;
v___y_391_ = v_val_454_;
v___y_392_ = v_a_481_;
v___y_393_ = v_val_472_;
goto v___jp_373_;
}
else
{
lean_object* v___x_505_; 
lean_dec(v_a_503_);
lean_dec_ref(v_semiringInst_501_);
lean_dec_ref(v_ringInst_500_);
lean_dec_ref_known(v_a_481_, 1);
v___x_505_ = lean_box(0);
v___y_305_ = v_val_448_;
v___y_306_ = v_a_459_;
v___y_307_ = v_val_441_;
v___y_308_ = v_a_461_;
v___y_309_ = v_a_464_;
v___y_310_ = v___x_483_;
v___y_311_ = v_val_454_;
v___y_312_ = v_a_474_;
v___y_313_ = v_a_471_;
v_fst_314_ = v___x_505_;
v_fst_315_ = v___x_505_;
v_fst_316_ = v___x_505_;
v_snd_317_ = v___x_484_;
v___y_318_ = v_a_293_;
v___y_319_ = v_a_301_;
goto v___jp_304_;
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref(v_semiringInst_501_);
lean_dec_ref(v_ringInst_500_);
lean_dec_ref_known(v_a_481_, 1);
lean_dec_ref(v___x_483_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_471_);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_506_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_502_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_502_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_a_494_);
lean_dec(v_a_490_);
lean_dec_ref_known(v_a_481_, 1);
lean_dec_ref(v___x_483_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_471_);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_514_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_495_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_495_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_a_490_);
lean_dec_ref_known(v___x_486_, 1);
lean_dec_ref_known(v_a_481_, 1);
lean_dec_ref(v___x_483_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_471_);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_522_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_491_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_491_);
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
lean_dec_ref_known(v___x_486_, 1);
lean_dec_ref_known(v_a_481_, 1);
lean_dec_ref(v___x_483_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec(v_a_471_);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_530_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_487_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_487_);
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
else
{
lean_object* v___x_538_; 
lean_dec(v_a_481_);
lean_inc_ref(v_type_292_);
v___x_538_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
if (lean_obj_tag(v_a_539_) == 1)
{
lean_object* v_val_540_; lean_object* v___x_541_; 
v_val_540_ = lean_ctor_get(v_a_539_, 0);
v___x_541_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_val_540_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v___x_543_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_val_540_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
v___x_545_ = l_Lean_leCarrierIsSort(v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; uint8_t v___x_547_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = lean_unbox(v_a_546_);
lean_dec(v_a_546_);
if (v___x_547_ == 0)
{
lean_object* v_semiringInst_548_; lean_object* v_ringInst_549_; 
lean_inc(v_val_472_);
v_semiringInst_548_ = lean_ctor_get(v_a_542_, 4);
lean_inc_ref(v_semiringInst_548_);
lean_dec(v_a_542_);
v_ringInst_549_ = lean_ctor_get(v_a_544_, 3);
lean_inc_ref(v_ringInst_549_);
lean_dec(v_a_544_);
lean_inc(v_val_441_);
v___y_407_ = v___x_484_;
v___y_408_ = v_a_301_;
v___y_409_ = v_a_461_;
v___y_410_ = v_a_300_;
v___y_411_ = v_a_293_;
v___y_412_ = v_a_464_;
v___y_413_ = v_a_474_;
v___y_414_ = v_a_471_;
v___y_415_ = v_val_441_;
v___y_416_ = v_val_448_;
v___y_417_ = v_val_441_;
v___y_418_ = v_a_459_;
v___y_419_ = v_a_302_;
v___y_420_ = v_semiringInst_548_;
v___y_421_ = v_a_298_;
v___y_422_ = v_a_299_;
v___y_423_ = v_ringInst_549_;
v___y_424_ = v___x_483_;
v___y_425_ = v_val_454_;
v___y_426_ = v_a_539_;
v___y_427_ = v_val_472_;
goto v___jp_406_;
}
else
{
lean_object* v_semiringInst_550_; lean_object* v_ringInst_551_; lean_object* v___x_552_; 
v_semiringInst_550_ = lean_ctor_get(v_a_542_, 4);
lean_inc_ref(v_semiringInst_550_);
lean_dec(v_a_542_);
v_ringInst_551_ = lean_ctor_get(v_a_544_, 3);
lean_inc_ref(v_ringInst_551_);
lean_dec(v_a_544_);
lean_inc(v_val_441_);
v___x_552_ = l_Lean_Meta_decLevel_x3f(v_val_441_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
if (lean_obj_tag(v_a_553_) == 1)
{
lean_object* v_val_554_; 
lean_inc(v_val_472_);
v_val_554_ = lean_ctor_get(v_a_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v_a_553_, 1);
v___y_407_ = v___x_484_;
v___y_408_ = v_a_301_;
v___y_409_ = v_a_461_;
v___y_410_ = v_a_300_;
v___y_411_ = v_a_293_;
v___y_412_ = v_a_464_;
v___y_413_ = v_a_474_;
v___y_414_ = v_a_471_;
v___y_415_ = v_val_554_;
v___y_416_ = v_val_448_;
v___y_417_ = v_val_441_;
v___y_418_ = v_a_459_;
v___y_419_ = v_a_302_;
v___y_420_ = v_semiringInst_550_;
v___y_421_ = v_a_298_;
v___y_422_ = v_a_299_;
v___y_423_ = v_ringInst_551_;
v___y_424_ = v___x_483_;
v___y_425_ = v_val_454_;
v___y_426_ = v_a_539_;
v___y_427_ = v_val_472_;
goto v___jp_406_;
}
else
{
lean_object* v___x_555_; 
lean_dec(v_a_553_);
lean_dec_ref(v_ringInst_551_);
lean_dec_ref(v_semiringInst_550_);
lean_dec_ref_known(v_a_539_, 1);
v___x_555_ = lean_box(0);
v___y_305_ = v_val_448_;
v___y_306_ = v_a_459_;
v___y_307_ = v_val_441_;
v___y_308_ = v_a_461_;
v___y_309_ = v_a_464_;
v___y_310_ = v___x_483_;
v___y_311_ = v_val_454_;
v___y_312_ = v_a_474_;
v___y_313_ = v_a_471_;
v_fst_314_ = v___x_555_;
v_fst_315_ = v___x_555_;
v_fst_316_ = v___x_555_;
v_snd_317_ = v___x_484_;
v___y_318_ = v_a_293_;
v___y_319_ = v_a_301_;
goto v___jp_304_;
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v_ringInst_551_);
lean_dec_ref(v_semiringInst_550_);
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v___x_483_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_471_);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_556_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_552_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_552_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_a_544_);
lean_dec(v_a_542_);
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v___x_483_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_471_);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_564_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_545_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_545_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec(v_a_542_);
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v___x_483_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_471_);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_572_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_543_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_543_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref_known(v_a_539_, 1);
lean_dec_ref(v___x_483_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_471_);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_580_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_541_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_541_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v___x_588_; 
lean_dec(v_a_539_);
v___x_588_ = lean_box(0);
v___y_305_ = v_val_448_;
v___y_306_ = v_a_459_;
v___y_307_ = v_val_441_;
v___y_308_ = v_a_461_;
v___y_309_ = v_a_464_;
v___y_310_ = v___x_483_;
v___y_311_ = v_val_454_;
v___y_312_ = v_a_474_;
v___y_313_ = v_a_471_;
v_fst_314_ = v___x_588_;
v_fst_315_ = v___x_588_;
v_fst_316_ = v___x_588_;
v_snd_317_ = v___x_484_;
v___y_318_ = v_a_293_;
v___y_319_ = v_a_301_;
goto v___jp_304_;
}
}
else
{
lean_dec_ref(v___x_483_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec(v_a_471_);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
return v___x_538_;
}
}
}
}
else
{
lean_dec(v_a_479_);
lean_dec_ref_known(v_a_474_, 1);
lean_dec(v_a_471_);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_del_object(v___x_456_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
return v___x_480_;
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref_known(v_a_474_, 1);
lean_dec(v_a_471_);
lean_dec_ref_known(v_a_464_, 1);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_del_object(v___x_456_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_590_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_478_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_478_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_a_471_);
lean_dec_ref_known(v_a_464_, 1);
lean_dec_ref_known(v___x_467_, 2);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_del_object(v___x_456_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_598_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_473_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_473_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_607_; 
lean_dec_ref_known(v___x_467_, 2);
lean_del_object(v___x_456_);
lean_dec_ref_known(v_a_444_, 1);
v_a_606_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_470_, 1);
v___x_607_ = lean_box(0);
v___y_357_ = v_val_448_;
v___y_358_ = v_val_441_;
v___y_359_ = v_a_459_;
v___y_360_ = v_a_461_;
v___y_361_ = v_a_464_;
v___y_362_ = v_val_454_;
v___y_363_ = v_a_606_;
v_fst_364_ = v___x_607_;
v_snd_365_ = v___x_607_;
v___y_366_ = v_a_293_;
v___y_367_ = v_a_301_;
goto v___jp_356_;
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref_known(v___x_467_, 2);
lean_dec(v_a_464_);
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_del_object(v___x_456_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec_ref_known(v_a_444_, 1);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_608_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_470_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_470_);
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
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_461_);
lean_dec(v_a_459_);
lean_del_object(v___x_456_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec_ref_known(v_a_444_, 1);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_616_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_463_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_463_);
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
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_a_459_);
lean_del_object(v___x_456_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec_ref_known(v_a_444_, 1);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_624_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_460_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_460_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
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
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_del_object(v___x_456_);
lean_dec(v_val_454_);
lean_dec(v_val_448_);
lean_dec_ref_known(v_a_444_, 1);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_632_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_458_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_458_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
else
{
lean_object* v___x_641_; lean_object* v___x_643_; 
lean_dec(v_a_450_);
lean_dec_ref_known(v_a_444_, 1);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v___x_641_ = lean_box(0);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_641_);
v___x_643_ = v___x_452_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref_known(v_a_444_, 1);
lean_dec(v_val_448_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_646_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_449_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_449_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_656_; 
lean_dec(v_a_444_);
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v___x_654_ = lean_box(0);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_654_);
v___x_656_ = v___x_446_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec(v_val_441_);
lean_dec_ref(v_type_292_);
v_a_659_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_443_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_443_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v_type_292_);
v_a_707_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_370_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_370_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
v___jp_304_:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v_structs_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v_structs_322_ = lean_ctor_get(v_a_321_, 0);
lean_inc_ref(v_structs_322_);
lean_dec(v_a_321_);
v___x_323_ = lean_array_get_size(v_structs_322_);
lean_dec_ref(v_structs_322_);
v___x_324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1);
v___x_325_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3);
v___x_326_ = lean_box(0);
v___x_327_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v___x_327_, 0, v___x_323_);
lean_ctor_set(v___x_327_, 1, v_type_292_);
lean_ctor_set(v___x_327_, 2, v___y_307_);
lean_ctor_set(v___x_327_, 3, v___y_311_);
lean_ctor_set(v___x_327_, 4, v___y_305_);
lean_ctor_set(v___x_327_, 5, v___y_309_);
lean_ctor_set(v___x_327_, 6, v___y_306_);
lean_ctor_set(v___x_327_, 7, v___y_308_);
lean_ctor_set(v___x_327_, 8, v___y_312_);
lean_ctor_set(v___x_327_, 9, v_fst_314_);
lean_ctor_set(v___x_327_, 10, v_fst_315_);
lean_ctor_set(v___x_327_, 11, v_fst_316_);
lean_ctor_set(v___x_327_, 12, v___y_313_);
lean_ctor_set(v___x_327_, 13, v___y_310_);
lean_ctor_set(v___x_327_, 14, v___x_324_);
lean_ctor_set(v___x_327_, 15, v___x_325_);
lean_ctor_set(v___x_327_, 16, v___x_325_);
lean_ctor_set(v___x_327_, 17, v___x_325_);
lean_ctor_set(v___x_327_, 18, v___x_324_);
lean_ctor_set(v___x_327_, 19, v___x_324_);
lean_ctor_set(v___x_327_, 20, v___x_324_);
lean_ctor_set(v___x_327_, 21, v___x_326_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*22, v_snd_317_);
v___f_328_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_328_, 0, v___x_327_);
v___x_329_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_330_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_329_, v___f_328_, v___y_318_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_338_; 
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; 
v_unused_339_ = lean_ctor_get(v___x_330_, 0);
lean_dec(v_unused_339_);
v___x_332_ = v___x_330_;
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
else
{
lean_dec(v___x_330_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_323_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_334_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_a_340_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_330_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_330_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_fst_316_);
lean_dec(v_fst_315_);
lean_dec(v_fst_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec(v___y_309_);
lean_dec(v___y_308_);
lean_dec(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec_ref(v_type_292_);
v_a_348_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_320_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_320_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
v___jp_356_:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_box(0);
v___x_369_ = 0;
lean_inc_n(v_fst_364_, 2);
v___y_305_ = v___y_357_;
v___y_306_ = v___y_359_;
v___y_307_ = v___y_358_;
v___y_308_ = v___y_360_;
v___y_309_ = v___y_361_;
v___y_310_ = v_snd_365_;
v___y_311_ = v___y_362_;
v___y_312_ = v_fst_364_;
v___y_313_ = v___y_363_;
v_fst_314_ = v___x_368_;
v_fst_315_ = v_fst_364_;
v_fst_316_ = v_fst_364_;
v_snd_317_ = v___x_369_;
v___y_318_ = v___y_366_;
v___y_319_ = v___y_367_;
goto v___jp_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___boxed(lean_object* v_type_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(v_type_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec(v_a_716_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
lean_object* v_ks_732_; lean_object* v_vs_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_759_; 
v_ks_732_ = lean_ctor_get(v_x_728_, 0);
v_vs_733_ = lean_ctor_get(v_x_728_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_x_728_);
if (v_isSharedCheck_759_ == 0)
{
v___x_735_ = v_x_728_;
v_isShared_736_ = v_isSharedCheck_759_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_vs_733_);
lean_inc(v_ks_732_);
lean_dec(v_x_728_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_759_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_array_get_size(v_ks_732_);
v___x_738_ = lean_nat_dec_lt(v_x_729_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
lean_dec(v_x_729_);
v___x_739_ = lean_array_push(v_ks_732_, v_x_730_);
v___x_740_ = lean_array_push(v_vs_733_, v_x_731_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_740_);
lean_ctor_set(v___x_735_, 0, v___x_739_);
v___x_742_ = v___x_735_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
lean_object* v_k_x27_744_; size_t v___x_745_; size_t v___x_746_; uint8_t v___x_747_; 
v_k_x27_744_ = lean_array_fget_borrowed(v_ks_732_, v_x_729_);
v___x_745_ = lean_ptr_addr(v_x_730_);
v___x_746_ = lean_ptr_addr(v_k_x27_744_);
v___x_747_ = lean_usize_dec_eq(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_749_; 
if (v_isShared_736_ == 0)
{
v___x_749_ = v___x_735_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_ks_732_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_vs_733_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = lean_nat_add(v_x_729_, v___x_750_);
lean_dec(v_x_729_);
v_x_728_ = v___x_749_;
v_x_729_ = v___x_751_;
goto _start;
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = lean_array_fset(v_ks_732_, v_x_729_, v_x_730_);
v___x_755_ = lean_array_fset(v_vs_733_, v_x_729_, v_x_731_);
lean_dec(v_x_729_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_755_);
lean_ctor_set(v___x_735_, 0, v___x_754_);
v___x_757_ = v___x_735_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_755_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_760_, lean_object* v_k_761_, lean_object* v_v_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_760_, v___x_763_, v_k_761_, v_v_762_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(lean_object* v_x_766_, size_t v_x_767_, size_t v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v_es_771_; size_t v___x_772_; size_t v___x_773_; lean_object* v_j_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_es_771_ = lean_ctor_get(v_x_766_, 0);
v___x_772_ = ((size_t)31ULL);
v___x_773_ = lean_usize_land(v_x_767_, v___x_772_);
v_j_774_ = lean_usize_to_nat(v___x_773_);
v___x_775_ = lean_array_get_size(v_es_771_);
v___x_776_ = lean_nat_dec_lt(v_j_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v_j_774_);
lean_dec(v_x_770_);
lean_dec_ref(v_x_769_);
return v_x_766_;
}
else
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_817_; 
lean_inc_ref(v_es_771_);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_x_766_, 0);
lean_dec(v_unused_818_);
v___x_778_ = v_x_766_;
v_isShared_779_ = v_isSharedCheck_817_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_x_766_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_817_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_v_780_; lean_object* v___x_781_; lean_object* v_xs_x27_782_; lean_object* v___y_784_; 
v_v_780_ = lean_array_fget(v_es_771_, v_j_774_);
v___x_781_ = lean_box(0);
v_xs_x27_782_ = lean_array_fset(v_es_771_, v_j_774_, v___x_781_);
switch(lean_obj_tag(v_v_780_))
{
case 0:
{
lean_object* v_key_789_; lean_object* v_val_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_802_; 
v_key_789_ = lean_ctor_get(v_v_780_, 0);
v_val_790_ = lean_ctor_get(v_v_780_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_v_780_);
if (v_isSharedCheck_802_ == 0)
{
v___x_792_ = v_v_780_;
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_val_790_);
lean_inc(v_key_789_);
lean_dec(v_v_780_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
size_t v___x_794_; size_t v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_ptr_addr(v_x_769_);
v___x_795_ = lean_ptr_addr(v_key_789_);
v___x_796_ = lean_usize_dec_eq(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_del_object(v___x_792_);
v___x_797_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_789_, v_val_790_, v_x_769_, v_x_770_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___y_784_ = v___x_798_;
goto v___jp_783_;
}
else
{
lean_object* v___x_800_; 
lean_dec(v_val_790_);
lean_dec(v_key_789_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v_x_770_);
lean_ctor_set(v___x_792_, 0, v_x_769_);
v___x_800_ = v___x_792_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_x_769_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_x_770_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v___y_784_ = v___x_800_;
goto v___jp_783_;
}
}
}
}
case 1:
{
lean_object* v_node_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_815_; 
v_node_803_ = lean_ctor_get(v_v_780_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_v_780_);
if (v_isSharedCheck_815_ == 0)
{
v___x_805_ = v_v_780_;
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_node_803_);
lean_dec(v_v_780_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_807_ = ((size_t)5ULL);
v___x_808_ = lean_usize_shift_right(v_x_767_, v___x_807_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_add(v_x_768_, v___x_809_);
v___x_811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_node_803_, v___x_808_, v___x_810_, v_x_769_, v_x_770_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_811_);
v___x_813_ = v___x_805_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
v___y_784_ = v___x_813_;
goto v___jp_783_;
}
}
}
default: 
{
lean_object* v___x_816_; 
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_x_769_);
lean_ctor_set(v___x_816_, 1, v_x_770_);
v___y_784_ = v___x_816_;
goto v___jp_783_;
}
}
v___jp_783_:
{
lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_785_ = lean_array_fset(v_xs_x27_782_, v_j_774_, v___y_784_);
lean_dec(v_j_774_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_785_);
v___x_787_ = v___x_778_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
else
{
lean_object* v_ks_819_; lean_object* v_vs_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_840_; 
v_ks_819_ = lean_ctor_get(v_x_766_, 0);
v_vs_820_ = lean_ctor_get(v_x_766_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_840_ == 0)
{
v___x_822_ = v_x_766_;
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_vs_820_);
lean_inc(v_ks_819_);
lean_dec(v_x_766_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_840_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_ks_819_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_vs_820_);
v___x_825_ = v_reuseFailAlloc_839_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v_newNode_826_; uint8_t v___y_828_; size_t v___x_834_; uint8_t v___x_835_; 
v_newNode_826_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(v___x_825_, v_x_769_, v_x_770_);
v___x_834_ = ((size_t)7ULL);
v___x_835_ = lean_usize_dec_le(v___x_834_, v_x_768_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_836_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_826_);
v___x_837_ = lean_unsigned_to_nat(4u);
v___x_838_ = lean_nat_dec_lt(v___x_836_, v___x_837_);
lean_dec(v___x_836_);
v___y_828_ = v___x_838_;
goto v___jp_827_;
}
else
{
v___y_828_ = v___x_835_;
goto v___jp_827_;
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_object* v_ks_829_; lean_object* v_vs_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_ks_829_ = lean_ctor_get(v_newNode_826_, 0);
lean_inc_ref(v_ks_829_);
v_vs_830_ = lean_ctor_get(v_newNode_826_, 1);
lean_inc_ref(v_vs_830_);
lean_dec_ref(v_newNode_826_);
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0);
v___x_833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_x_768_, v_ks_829_, v_vs_830_, v___x_831_, v___x_832_);
lean_dec_ref(v_vs_830_);
lean_dec_ref(v_ks_829_);
return v___x_833_;
}
else
{
return v_newNode_826_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_841_, lean_object* v_keys_842_, lean_object* v_vals_843_, lean_object* v_i_844_, lean_object* v_entries_845_){
_start:
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_array_get_size(v_keys_842_);
v___x_847_ = lean_nat_dec_lt(v_i_844_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_i_844_);
return v_entries_845_;
}
else
{
lean_object* v_k_848_; lean_object* v_v_849_; size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; uint64_t v___x_853_; size_t v_h_854_; size_t v___x_855_; lean_object* v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v_h_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_k_848_ = lean_array_fget_borrowed(v_keys_842_, v_i_844_);
v_v_849_ = lean_array_fget_borrowed(v_vals_843_, v_i_844_);
v___x_850_ = lean_ptr_addr(v_k_848_);
v___x_851_ = ((size_t)3ULL);
v___x_852_ = lean_usize_shift_right(v___x_850_, v___x_851_);
v___x_853_ = lean_usize_to_uint64(v___x_852_);
v_h_854_ = lean_uint64_to_usize(v___x_853_);
v___x_855_ = ((size_t)5ULL);
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_sub(v_depth_841_, v___x_857_);
v___x_859_ = lean_usize_mul(v___x_855_, v___x_858_);
v_h_860_ = lean_usize_shift_right(v_h_854_, v___x_859_);
v___x_861_ = lean_nat_add(v_i_844_, v___x_856_);
lean_dec(v_i_844_);
lean_inc(v_v_849_);
lean_inc(v_k_848_);
v___x_862_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_entries_845_, v_h_860_, v_depth_841_, v_k_848_, v_v_849_);
v_i_844_ = v___x_861_;
v_entries_845_ = v___x_862_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_864_, lean_object* v_keys_865_, lean_object* v_vals_866_, lean_object* v_i_867_, lean_object* v_entries_868_){
_start:
{
size_t v_depth_boxed_869_; lean_object* v_res_870_; 
v_depth_boxed_869_ = lean_unbox_usize(v_depth_864_);
lean_dec(v_depth_864_);
v_res_870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_869_, v_keys_865_, v_vals_866_, v_i_867_, v_entries_868_);
lean_dec_ref(v_vals_866_);
lean_dec_ref(v_keys_865_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
size_t v_x_5584__boxed_876_; size_t v_x_5585__boxed_877_; lean_object* v_res_878_; 
v_x_5584__boxed_876_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_x_5585__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_871_, v_x_5584__boxed_876_, v_x_5585__boxed_877_, v_x_874_, v_x_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
size_t v___x_882_; size_t v___x_883_; size_t v___x_884_; uint64_t v___x_885_; size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; 
v___x_882_ = lean_ptr_addr(v_x_880_);
v___x_883_ = ((size_t)3ULL);
v___x_884_ = lean_usize_shift_right(v___x_882_, v___x_883_);
v___x_885_ = lean_usize_to_uint64(v___x_884_);
v___x_886_ = lean_uint64_to_usize(v___x_885_);
v___x_887_ = ((size_t)1ULL);
v___x_888_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_879_, v___x_886_, v___x_887_, v_x_880_, v_x_881_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0(lean_object* v_type_889_, lean_object* v_a_890_, lean_object* v_s_891_){
_start:
{
lean_object* v_structs_892_; lean_object* v_typeIdOf_893_; lean_object* v_exprToStructId_894_; lean_object* v_termMap_895_; lean_object* v_termMapInv_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_904_; 
v_structs_892_ = lean_ctor_get(v_s_891_, 0);
v_typeIdOf_893_ = lean_ctor_get(v_s_891_, 1);
v_exprToStructId_894_ = lean_ctor_get(v_s_891_, 2);
v_termMap_895_ = lean_ctor_get(v_s_891_, 3);
v_termMapInv_896_ = lean_ctor_get(v_s_891_, 4);
v_isSharedCheck_904_ = !lean_is_exclusive(v_s_891_);
if (v_isSharedCheck_904_ == 0)
{
v___x_898_ = v_s_891_;
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_termMapInv_896_);
lean_inc(v_termMap_895_);
lean_inc(v_exprToStructId_894_);
lean_inc(v_typeIdOf_893_);
lean_inc(v_structs_892_);
lean_dec(v_s_891_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(v_typeIdOf_893_, v_type_889_, v_a_890_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_900_);
v___x_902_ = v___x_898_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_structs_892_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_exprToStructId_894_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_termMap_895_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v_termMapInv_896_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_905_, lean_object* v_vals_906_, lean_object* v_i_907_, lean_object* v_k_908_){
_start:
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = lean_array_get_size(v_keys_905_);
v___x_910_ = lean_nat_dec_lt(v_i_907_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
lean_dec(v_i_907_);
v___x_911_ = lean_box(0);
return v___x_911_;
}
else
{
lean_object* v_k_x27_912_; size_t v___x_913_; size_t v___x_914_; uint8_t v___x_915_; 
v_k_x27_912_ = lean_array_fget_borrowed(v_keys_905_, v_i_907_);
v___x_913_ = lean_ptr_addr(v_k_908_);
v___x_914_ = lean_ptr_addr(v_k_x27_912_);
v___x_915_ = lean_usize_dec_eq(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_add(v_i_907_, v___x_916_);
lean_dec(v_i_907_);
v_i_907_ = v___x_917_;
goto _start;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_array_fget_borrowed(v_vals_906_, v_i_907_);
lean_dec(v_i_907_);
lean_inc(v___x_919_);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_921_, lean_object* v_vals_922_, lean_object* v_i_923_, lean_object* v_k_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_921_, v_vals_922_, v_i_923_, v_k_924_);
lean_dec_ref(v_k_924_);
lean_dec_ref(v_vals_922_);
lean_dec_ref(v_keys_921_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_926_, size_t v_x_927_, lean_object* v_x_928_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
lean_object* v_es_929_; lean_object* v___x_930_; size_t v___x_931_; size_t v___x_932_; lean_object* v_j_933_; lean_object* v___x_934_; 
v_es_929_ = lean_ctor_get(v_x_926_, 0);
v___x_930_ = lean_box(2);
v___x_931_ = ((size_t)31ULL);
v___x_932_ = lean_usize_land(v_x_927_, v___x_931_);
v_j_933_ = lean_usize_to_nat(v___x_932_);
v___x_934_ = lean_array_get_borrowed(v___x_930_, v_es_929_, v_j_933_);
lean_dec(v_j_933_);
switch(lean_obj_tag(v___x_934_))
{
case 0:
{
lean_object* v_key_935_; lean_object* v_val_936_; size_t v___x_937_; size_t v___x_938_; uint8_t v___x_939_; 
v_key_935_ = lean_ctor_get(v___x_934_, 0);
v_val_936_ = lean_ctor_get(v___x_934_, 1);
v___x_937_ = lean_ptr_addr(v_x_928_);
v___x_938_ = lean_ptr_addr(v_key_935_);
v___x_939_ = lean_usize_dec_eq(v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_box(0);
return v___x_940_;
}
else
{
lean_object* v___x_941_; 
lean_inc(v_val_936_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_val_936_);
return v___x_941_;
}
}
case 1:
{
lean_object* v_node_942_; size_t v___x_943_; size_t v___x_944_; 
v_node_942_ = lean_ctor_get(v___x_934_, 0);
v___x_943_ = ((size_t)5ULL);
v___x_944_ = lean_usize_shift_right(v_x_927_, v___x_943_);
v_x_926_ = v_node_942_;
v_x_927_ = v___x_944_;
goto _start;
}
default: 
{
lean_object* v___x_946_; 
v___x_946_ = lean_box(0);
return v___x_946_;
}
}
}
else
{
lean_object* v_ks_947_; lean_object* v_vs_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_ks_947_ = lean_ctor_get(v_x_926_, 0);
v_vs_948_ = lean_ctor_get(v_x_926_, 1);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_947_, v_vs_948_, v___x_949_, v_x_928_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
size_t v_x_5807__boxed_954_; lean_object* v_res_955_; 
v_x_5807__boxed_954_ = lean_unbox_usize(v_x_952_);
lean_dec(v_x_952_);
v_res_955_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_951_, v_x_5807__boxed_954_, v_x_953_);
lean_dec_ref(v_x_953_);
lean_dec_ref(v_x_951_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
size_t v___x_958_; size_t v___x_959_; size_t v___x_960_; uint64_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; 
v___x_958_ = lean_ptr_addr(v_x_957_);
v___x_959_ = ((size_t)3ULL);
v___x_960_ = lean_usize_shift_right(v___x_958_, v___x_959_);
v___x_961_ = lean_usize_to_uint64(v___x_960_);
v___x_962_ = lean_uint64_to_usize(v___x_961_);
v___x_963_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_956_, v___x_962_, v_x_957_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_x_964_, v_x_965_);
lean_dec_ref(v_x_965_);
lean_dec_ref(v_x_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f(lean_object* v_type_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_970_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1030_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_1030_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1030_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v_order_984_; 
v_order_984_ = lean_ctor_get_uint8(v_a_980_, sizeof(void*)*14 + 27);
lean_dec(v_a_980_);
if (v_order_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_987_; 
lean_dec_ref(v_type_967_);
v___x_985_ = lean_box(0);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_985_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
lean_object* v___x_989_; 
lean_del_object(v___x_982_);
v___x_989_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_968_, v_a_976_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1021_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1021_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1021_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v_typeIdOf_994_; lean_object* v___x_995_; 
v_typeIdOf_994_ = lean_ctor_get(v_a_990_, 1);
lean_inc_ref(v_typeIdOf_994_);
lean_dec(v_a_990_);
v___x_995_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_typeIdOf_994_, v_type_967_);
lean_dec_ref(v_typeIdOf_994_);
if (lean_obj_tag(v___x_995_) == 1)
{
lean_object* v_val_996_; lean_object* v___x_998_; 
lean_dec_ref(v_type_967_);
v_val_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v___x_995_, 1);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v_val_996_);
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_val_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
else
{
lean_object* v___x_1000_; 
lean_dec(v___x_995_);
lean_del_object(v___x_992_);
lean_inc_ref(v_type_967_);
v___x_1000_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(v_type_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc_n(v_a_1001_, 2);
lean_dec_ref_known(v___x_1000_, 1);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1002_, 0, v_type_967_);
lean_closure_set(v___f_1002_, 1, v_a_1001_);
v___x_1003_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_1004_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1003_, v___f_1002_, v_a_968_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v___x_1004_, 0);
lean_dec(v_unused_1012_);
v___x_1006_ = v___x_1004_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_dec(v___x_1004_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_a_1001_);
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1001_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v_a_1001_);
v_a_1013_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1004_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1004_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_dec_ref(v_type_967_);
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_type_967_);
v_a_1022_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_989_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_989_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_type_967_);
v_a_1031_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_979_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_979_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___boxed(lean_object* v_type_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Meta_Grind_Order_getStructId_x3f(v_type_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec(v_a_1040_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(lean_object* v_00_u03b2_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_x_1053_, v_x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(v_00_u03b2_1056_, v_x_1057_, v_x_1058_);
lean_dec_ref(v_x_1058_);
lean_dec_ref(v_x_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1(lean_object* v_00_u03b2_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(v_x_1061_, v_x_1062_, v_x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1065_, lean_object* v_x_1066_, size_t v_x_1067_, lean_object* v_x_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_1066_, v_x_1067_, v_x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
size_t v_x_6013__boxed_1074_; lean_object* v_res_1075_; 
v_x_6013__boxed_1074_ = lean_unbox_usize(v_x_1072_);
lean_dec(v_x_1072_);
v_res_1075_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(v_00_u03b2_1070_, v_x_1071_, v_x_6013__boxed_1074_, v_x_1073_);
lean_dec_ref(v_x_1073_);
lean_dec_ref(v_x_1071_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(lean_object* v_00_u03b2_1076_, lean_object* v_x_1077_, size_t v_x_1078_, size_t v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_1077_, v_x_1078_, v_x_1079_, v_x_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
size_t v_x_6024__boxed_1089_; size_t v_x_6025__boxed_1090_; lean_object* v_res_1091_; 
v_x_6024__boxed_1089_ = lean_unbox_usize(v_x_1085_);
lean_dec(v_x_1085_);
v_x_6025__boxed_1090_ = lean_unbox_usize(v_x_1086_);
lean_dec(v_x_1086_);
v_res_1091_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(v_00_u03b2_1083_, v_x_1084_, v_x_6024__boxed_1089_, v_x_6025__boxed_1090_, v_x_1087_, v_x_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1092_, lean_object* v_keys_1093_, lean_object* v_vals_1094_, lean_object* v_heq_1095_, lean_object* v_i_1096_, lean_object* v_k_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1093_, v_vals_1094_, v_i_1096_, v_k_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1099_, lean_object* v_keys_1100_, lean_object* v_vals_1101_, lean_object* v_heq_1102_, lean_object* v_i_1103_, lean_object* v_k_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1099_, v_keys_1100_, v_vals_1101_, v_heq_1102_, v_i_1103_, v_k_1104_);
lean_dec_ref(v_k_1104_);
lean_dec_ref(v_vals_1101_);
lean_dec_ref(v_keys_1100_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1106_, lean_object* v_n_1107_, lean_object* v_k_1108_, lean_object* v_v_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(v_n_1107_, v_k_1108_, v_v_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1111_, size_t v_depth_1112_, lean_object* v_keys_1113_, lean_object* v_vals_1114_, lean_object* v_heq_1115_, lean_object* v_i_1116_, lean_object* v_entries_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1112_, v_keys_1113_, v_vals_1114_, v_i_1116_, v_entries_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1119_, lean_object* v_depth_1120_, lean_object* v_keys_1121_, lean_object* v_vals_1122_, lean_object* v_heq_1123_, lean_object* v_i_1124_, lean_object* v_entries_1125_){
_start:
{
size_t v_depth_boxed_1126_; lean_object* v_res_1127_; 
v_depth_boxed_1126_ = lean_unbox_usize(v_depth_1120_);
lean_dec(v_depth_1120_);
v_res_1127_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1119_, v_depth_boxed_1126_, v_keys_1121_, v_vals_1122_, v_heq_1123_, v_i_1124_, v_entries_1125_);
lean_dec_ref(v_vals_1122_);
lean_dec_ref(v_keys_1121_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1129_, v_x_1130_, v_x_1131_, v_x_1132_);
return v___x_1133_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OrderLevel(builtin);
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
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
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
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_OrderLevel(builtin);
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
