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
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Order_orderExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_unsigned_to_nat(32u);
v___x_277_ = lean_mk_empty_array_with_capacity(v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7(void){
_start:
{
size_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_279_ = ((size_t)5ULL);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_unsigned_to_nat(32u);
v___x_282_ = lean_mk_empty_array_with_capacity(v___x_281_);
v___x_283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6);
v___x_284_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_282_);
lean_ctor_set(v___x_284_, 2, v___x_280_);
lean_ctor_set(v___x_284_, 3, v___x_280_);
lean_ctor_set_usize(v___x_284_, 4, v___x_279_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(lean_object* v_type_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; 
lean_inc_ref(v_type_292_);
v___x_304_ = l_Lean_Meta_getDecLevel_x3f(v_type_292_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_582_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_582_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_582_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_582_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
if (lean_obj_tag(v_a_305_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_577_; 
lean_del_object(v___x_307_);
v_val_309_ = lean_ctor_get(v_a_305_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_a_305_);
if (v_isSharedCheck_577_ == 0)
{
v___x_311_ = v_a_305_;
v_isShared_312_ = v_isSharedCheck_577_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v_a_305_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_577_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v_type_292_);
lean_inc(v_val_309_);
v___x_314_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v___x_313_, v_val_309_, v_type_292_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_568_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_568_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_568_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_568_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
if (lean_obj_tag(v_a_315_) == 1)
{
lean_object* v_val_319_; lean_object* v___x_320_; 
lean_del_object(v___x_317_);
v_val_319_ = lean_ctor_get(v_a_315_, 0);
lean_inc(v_val_319_);
lean_inc_ref(v_a_315_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_309_);
v___x_320_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_309_, v_type_292_, v_a_315_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_555_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_555_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_555_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_555_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
if (lean_obj_tag(v_a_321_) == 1)
{
lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_550_; 
lean_del_object(v___x_323_);
v_val_325_ = lean_ctor_get(v_a_321_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_321_);
if (v_isSharedCheck_550_ == 0)
{
v___x_327_ = v_a_321_;
v_isShared_328_ = v_isSharedCheck_550_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_dec(v_a_321_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_550_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; 
lean_inc_ref(v_a_315_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_309_);
v___x_329_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_val_309_, v_type_292_, v_a_315_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_331_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
lean_inc_ref(v_a_315_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_309_);
v___x_331_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_val_309_, v_type_292_, v_a_315_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3));
lean_inc_ref(v_type_292_);
lean_inc(v_val_309_);
v___x_334_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v___x_333_, v_val_309_, v_type_292_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5));
v___x_337_ = lean_box(0);
lean_inc(v_val_309_);
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v_val_309_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_inc_ref(v___x_338_);
v___x_339_ = l_Lean_mkConst(v___x_336_, v___x_338_);
lean_inc(v_val_319_);
lean_inc_ref(v_type_292_);
v___x_340_ = l_Lean_mkAppB(v___x_339_, v_type_292_, v_val_319_);
v___x_341_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v___x_340_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v_fst_346_; lean_object* v_fst_347_; lean_object* v_fst_348_; uint8_t v_snd_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v_fst_390_; lean_object* v_snd_391_; lean_object* v___y_392_; lean_object* v___y_393_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
if (lean_obj_tag(v_a_335_) == 1)
{
lean_object* v_val_396_; lean_object* v___x_397_; 
v_val_396_ = lean_ctor_get(v_a_335_, 0);
lean_inc_ref(v_a_335_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_309_);
v___x_397_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_val_309_, v_type_292_, v_a_335_, v_a_315_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
if (lean_obj_tag(v_a_398_) == 0)
{
lean_dec_ref_known(v___x_338_, 2);
lean_del_object(v___x_311_);
v_fst_390_ = v_a_398_;
v_snd_391_ = v_a_398_;
v___y_392_ = v_a_293_;
v___y_393_ = v_a_301_;
goto v___jp_389_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11));
v___x_400_ = l_Lean_mkConst(v___x_399_, v___x_338_);
lean_inc(v_val_396_);
lean_inc_ref(v_type_292_);
v___x_401_ = l_Lean_mkAppB(v___x_400_, v_type_292_, v_val_396_);
v___x_402_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v___x_401_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
lean_inc_ref(v_type_292_);
v___x_404_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_407_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v_a_403_);
v___x_407_ = v___x_311_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_403_);
v___x_407_ = v_reuseFailAlloc_500_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
uint8_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 0;
v___x_409_ = 1;
if (lean_obj_tag(v_a_405_) == 1)
{
lean_object* v_val_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_val_410_ = lean_ctor_get(v_a_405_, 0);
lean_inc(v_val_410_);
v___x_411_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_411_, 0, v_val_410_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*1, v___x_408_);
v___x_412_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_411_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v___x_416_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_a_413_, v___x_411_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_413_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v___x_414_);
v___x_416_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_411_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_418_; lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_439_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_a_417_, v___x_411_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec_ref_known(v___x_411_, 1);
lean_dec(v_a_417_);
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_439_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_439_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_439_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v_ringInst_423_; lean_object* v_semiringInst_424_; lean_object* v___x_425_; 
v_ringInst_423_ = lean_ctor_get(v_a_415_, 3);
lean_inc_ref(v_ringInst_423_);
lean_dec(v_a_415_);
v_semiringInst_424_ = lean_ctor_get(v_a_419_, 4);
lean_inc_ref(v_semiringInst_424_);
lean_dec(v_a_419_);
lean_inc(v_val_325_);
lean_inc(v_val_396_);
lean_inc(v_val_319_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_309_);
v___x_425_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_val_309_, v_type_292_, v_semiringInst_424_, v_val_319_, v_val_396_, v_val_325_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
if (lean_obj_tag(v_a_426_) == 1)
{
lean_object* v___x_428_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 1);
lean_ctor_set(v___x_421_, 0, v_ringInst_423_);
v___x_428_ = v___x_421_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_ringInst_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
v___y_344_ = v___x_407_;
v___y_345_ = v_a_398_;
v_fst_346_ = v_a_405_;
v_fst_347_ = v___x_428_;
v_fst_348_ = v_a_426_;
v_snd_349_ = v___x_409_;
v___y_350_ = v_a_293_;
v___y_351_ = v_a_301_;
goto v___jp_343_;
}
}
else
{
lean_object* v___x_430_; 
lean_dec(v_a_426_);
lean_dec_ref(v_ringInst_423_);
lean_del_object(v___x_421_);
lean_dec_ref_known(v_a_405_, 1);
v___x_430_ = lean_box(0);
v___y_344_ = v___x_407_;
v___y_345_ = v_a_398_;
v_fst_346_ = v___x_430_;
v_fst_347_ = v___x_430_;
v_fst_348_ = v___x_430_;
v_snd_349_ = v___x_409_;
v___y_350_ = v_a_293_;
v___y_351_ = v_a_301_;
goto v___jp_343_;
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec_ref(v_ringInst_423_);
lean_del_object(v___x_421_);
lean_dec_ref_known(v_a_405_, 1);
lean_dec_ref(v___x_407_);
lean_dec_ref_known(v_a_398_, 1);
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_431_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_425_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_425_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_a_415_);
lean_dec_ref_known(v___x_411_, 1);
lean_dec_ref_known(v_a_405_, 1);
lean_dec_ref(v___x_407_);
lean_dec_ref_known(v_a_398_, 1);
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_440_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_416_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_416_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
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
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref_known(v___x_411_, 1);
lean_dec_ref_known(v_a_405_, 1);
lean_dec_ref(v___x_407_);
lean_dec_ref_known(v_a_398_, 1);
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_448_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_412_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_412_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
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
lean_object* v___x_456_; 
lean_dec(v_a_405_);
lean_inc_ref(v_type_292_);
v___x_456_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_499_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_499_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_499_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_499_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
if (lean_obj_tag(v_a_457_) == 1)
{
lean_object* v_val_461_; lean_object* v___x_462_; 
v_val_461_ = lean_ctor_get(v_a_457_, 0);
v___x_462_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_val_461_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_val_461_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v_semiringInst_466_; lean_object* v_ringInst_467_; lean_object* v___x_468_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v_semiringInst_466_ = lean_ctor_get(v_a_463_, 4);
lean_inc_ref(v_semiringInst_466_);
lean_dec(v_a_463_);
v_ringInst_467_ = lean_ctor_get(v_a_465_, 3);
lean_inc_ref(v_ringInst_467_);
lean_dec(v_a_465_);
lean_inc(v_val_325_);
lean_inc(v_val_396_);
lean_inc(v_val_319_);
lean_inc_ref(v_type_292_);
lean_inc(v_val_309_);
v___x_468_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_val_309_, v_type_292_, v_semiringInst_466_, v_val_319_, v_val_396_, v_val_325_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
if (lean_obj_tag(v_a_469_) == 1)
{
lean_object* v___x_471_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 1);
lean_ctor_set(v___x_459_, 0, v_ringInst_467_);
v___x_471_ = v___x_459_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_ringInst_467_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
v___y_344_ = v___x_407_;
v___y_345_ = v_a_398_;
v_fst_346_ = v_a_457_;
v_fst_347_ = v___x_471_;
v_fst_348_ = v_a_469_;
v_snd_349_ = v___x_408_;
v___y_350_ = v_a_293_;
v___y_351_ = v_a_301_;
goto v___jp_343_;
}
}
else
{
lean_object* v___x_473_; 
lean_dec(v_a_469_);
lean_dec_ref(v_ringInst_467_);
lean_dec_ref_known(v_a_457_, 1);
lean_del_object(v___x_459_);
v___x_473_ = lean_box(0);
v___y_344_ = v___x_407_;
v___y_345_ = v_a_398_;
v_fst_346_ = v___x_473_;
v_fst_347_ = v___x_473_;
v_fst_348_ = v___x_473_;
v_snd_349_ = v___x_409_;
v___y_350_ = v_a_293_;
v___y_351_ = v_a_301_;
goto v___jp_343_;
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v_ringInst_467_);
lean_dec_ref_known(v_a_457_, 1);
lean_del_object(v___x_459_);
lean_dec_ref(v___x_407_);
lean_dec_ref_known(v_a_398_, 1);
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_474_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_468_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_468_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v_a_463_);
lean_dec_ref_known(v_a_457_, 1);
lean_del_object(v___x_459_);
lean_dec_ref(v___x_407_);
lean_dec_ref_known(v_a_398_, 1);
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_482_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_464_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_464_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec_ref_known(v_a_457_, 1);
lean_del_object(v___x_459_);
lean_dec_ref(v___x_407_);
lean_dec_ref_known(v_a_398_, 1);
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_490_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_462_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_462_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v___x_498_; 
lean_del_object(v___x_459_);
lean_dec(v_a_457_);
v___x_498_ = lean_box(0);
v___y_344_ = v___x_407_;
v___y_345_ = v_a_398_;
v_fst_346_ = v___x_498_;
v_fst_347_ = v___x_498_;
v_fst_348_ = v___x_498_;
v_snd_349_ = v___x_408_;
v___y_350_ = v_a_293_;
v___y_351_ = v_a_301_;
goto v___jp_343_;
}
}
}
else
{
lean_dec_ref(v___x_407_);
lean_dec_ref_known(v_a_398_, 1);
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
return v___x_456_;
}
}
}
}
else
{
lean_dec(v_a_403_);
lean_dec_ref_known(v_a_398_, 1);
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
return v___x_404_;
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref_known(v_a_398_, 1);
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_501_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_402_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_402_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref_known(v_a_335_, 1);
lean_dec(v_a_342_);
lean_dec_ref_known(v___x_338_, 2);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_509_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_397_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_397_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v___x_517_; 
lean_dec_ref_known(v___x_338_, 2);
lean_dec_ref_known(v_a_315_, 1);
lean_del_object(v___x_311_);
v___x_517_ = lean_box(0);
v_fst_390_ = v___x_517_;
v_snd_391_ = v___x_517_;
v___y_392_ = v_a_293_;
v___y_393_ = v_a_301_;
goto v___jp_389_;
}
v___jp_343_:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_350_, v___y_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v_structs_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
v_structs_354_ = lean_ctor_get(v_a_353_, 0);
lean_inc_ref(v_structs_354_);
lean_dec(v_a_353_);
v___x_355_ = lean_array_get_size(v_structs_354_);
lean_dec_ref(v_structs_354_);
v___x_356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7);
v___x_357_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9);
v___x_358_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v___x_358_, 0, v___x_355_);
lean_ctor_set(v___x_358_, 1, v_type_292_);
lean_ctor_set(v___x_358_, 2, v_val_309_);
lean_ctor_set(v___x_358_, 3, v_val_325_);
lean_ctor_set(v___x_358_, 4, v_val_319_);
lean_ctor_set(v___x_358_, 5, v_a_335_);
lean_ctor_set(v___x_358_, 6, v_a_330_);
lean_ctor_set(v___x_358_, 7, v_a_332_);
lean_ctor_set(v___x_358_, 8, v___y_345_);
lean_ctor_set(v___x_358_, 9, v_fst_346_);
lean_ctor_set(v___x_358_, 10, v_fst_347_);
lean_ctor_set(v___x_358_, 11, v_fst_348_);
lean_ctor_set(v___x_358_, 12, v_a_342_);
lean_ctor_set(v___x_358_, 13, v___y_344_);
lean_ctor_set(v___x_358_, 14, v___x_356_);
lean_ctor_set(v___x_358_, 15, v___x_357_);
lean_ctor_set(v___x_358_, 16, v___x_357_);
lean_ctor_set(v___x_358_, 17, v___x_357_);
lean_ctor_set(v___x_358_, 18, v___x_356_);
lean_ctor_set(v___x_358_, 19, v___x_356_);
lean_ctor_set(v___x_358_, 20, v___x_356_);
lean_ctor_set(v___x_358_, 21, v___x_337_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*22, v_snd_349_);
v___f_359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_359_, 0, v___x_358_);
v___x_360_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_361_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_360_, v___f_359_, v___y_350_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_361_, 0);
lean_dec(v_unused_372_);
v___x_363_ = v___x_361_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_dec(v___x_361_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_355_);
v___x_366_ = v___x_327_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_355_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_del_object(v___x_327_);
v_a_373_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_361_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_361_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_fst_348_);
lean_dec(v_fst_347_);
lean_dec(v_fst_346_);
lean_dec(v___y_345_);
lean_dec(v___y_344_);
lean_dec(v_a_342_);
lean_dec(v_a_335_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_381_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_352_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_352_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
v___jp_389_:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_box(0);
v___x_395_ = 0;
lean_inc_n(v_fst_390_, 2);
v___y_344_ = v_snd_391_;
v___y_345_ = v_fst_390_;
v_fst_346_ = v___x_394_;
v_fst_347_ = v_fst_390_;
v_fst_348_ = v_fst_390_;
v_snd_349_ = v___x_395_;
v___y_350_ = v___y_392_;
v___y_351_ = v___y_393_;
goto v___jp_343_;
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref_known(v___x_338_, 2);
lean_dec(v_a_335_);
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec_ref_known(v_a_315_, 1);
lean_dec(v_val_319_);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_518_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_341_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_341_);
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
lean_dec(v_a_332_);
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec_ref_known(v_a_315_, 1);
lean_dec(v_val_319_);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_526_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_334_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_334_);
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
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_a_330_);
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec_ref_known(v_a_315_, 1);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_534_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_331_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_331_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_319_);
lean_dec_ref_known(v_a_315_, 1);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_542_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_329_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_329_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec(v_a_321_);
lean_dec(v_val_319_);
lean_dec_ref_known(v_a_315_, 1);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v___x_551_ = lean_box(0);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_551_);
v___x_553_ = v___x_323_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_val_319_);
lean_dec_ref_known(v_a_315_, 1);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_556_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_320_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_320_);
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
else
{
lean_object* v___x_564_; lean_object* v___x_566_; 
lean_dec(v_a_315_);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v___x_564_ = lean_box(0);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_564_);
v___x_566_ = v___x_317_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_type_292_);
v_a_569_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_314_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_314_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_580_; 
lean_dec(v_a_305_);
lean_dec_ref(v_type_292_);
v___x_578_ = lean_box(0);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_578_);
v___x_580_ = v___x_307_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v_type_292_);
v_a_583_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_304_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_304_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___boxed(lean_object* v_type_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(v_type_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec(v_a_592_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_x_607_){
_start:
{
lean_object* v_ks_608_; lean_object* v_vs_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_633_; 
v_ks_608_ = lean_ctor_get(v_x_604_, 0);
v_vs_609_ = lean_ctor_get(v_x_604_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_604_);
if (v_isSharedCheck_633_ == 0)
{
v___x_611_ = v_x_604_;
v_isShared_612_ = v_isSharedCheck_633_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_vs_609_);
lean_inc(v_ks_608_);
lean_dec(v_x_604_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_633_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_array_get_size(v_ks_608_);
v___x_614_ = lean_nat_dec_lt(v_x_605_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
lean_dec(v_x_605_);
v___x_615_ = lean_array_push(v_ks_608_, v_x_606_);
v___x_616_ = lean_array_push(v_vs_609_, v_x_607_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v___x_616_);
lean_ctor_set(v___x_611_, 0, v___x_615_);
v___x_618_ = v___x_611_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v_k_x27_620_; uint8_t v___x_621_; 
v_k_x27_620_ = lean_array_fget_borrowed(v_ks_608_, v_x_605_);
v___x_621_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_606_, v_k_x27_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_623_; 
if (v_isShared_612_ == 0)
{
v___x_623_ = v___x_611_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_ks_608_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_vs_609_);
v___x_623_ = v_reuseFailAlloc_627_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v_x_605_, v___x_624_);
lean_dec(v_x_605_);
v_x_604_ = v___x_623_;
v_x_605_ = v___x_625_;
goto _start;
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_array_fset(v_ks_608_, v_x_605_, v_x_606_);
v___x_629_ = lean_array_fset(v_vs_609_, v_x_605_, v_x_607_);
lean_dec(v_x_605_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v___x_629_);
lean_ctor_set(v___x_611_, 0, v___x_628_);
v___x_631_ = v___x_611_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_634_, lean_object* v_k_635_, lean_object* v_v_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_634_, v___x_637_, v_k_635_, v_v_636_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(lean_object* v_x_640_, size_t v_x_641_, size_t v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
lean_object* v_es_645_; size_t v___x_646_; size_t v___x_647_; lean_object* v_j_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_es_645_ = lean_ctor_get(v_x_640_, 0);
v___x_646_ = ((size_t)31ULL);
v___x_647_ = lean_usize_land(v_x_641_, v___x_646_);
v_j_648_ = lean_usize_to_nat(v___x_647_);
v___x_649_ = lean_array_get_size(v_es_645_);
v___x_650_ = lean_nat_dec_lt(v_j_648_, v___x_649_);
if (v___x_650_ == 0)
{
lean_dec(v_j_648_);
lean_dec(v_x_644_);
lean_dec_ref(v_x_643_);
return v_x_640_;
}
else
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_689_; 
lean_inc_ref(v_es_645_);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_640_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v_x_640_, 0);
lean_dec(v_unused_690_);
v___x_652_ = v_x_640_;
v_isShared_653_ = v_isSharedCheck_689_;
goto v_resetjp_651_;
}
else
{
lean_dec(v_x_640_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_689_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_v_654_; lean_object* v___x_655_; lean_object* v_xs_x27_656_; lean_object* v___y_658_; 
v_v_654_ = lean_array_fget(v_es_645_, v_j_648_);
v___x_655_ = lean_box(0);
v_xs_x27_656_ = lean_array_fset(v_es_645_, v_j_648_, v___x_655_);
switch(lean_obj_tag(v_v_654_))
{
case 0:
{
lean_object* v_key_663_; lean_object* v_val_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_674_; 
v_key_663_ = lean_ctor_get(v_v_654_, 0);
v_val_664_ = lean_ctor_get(v_v_654_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_v_654_);
if (v_isSharedCheck_674_ == 0)
{
v___x_666_ = v_v_654_;
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_val_664_);
lean_inc(v_key_663_);
lean_dec(v_v_654_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
uint8_t v___x_668_; 
v___x_668_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_643_, v_key_663_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_del_object(v___x_666_);
v___x_669_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_663_, v_val_664_, v_x_643_, v_x_644_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
v___y_658_ = v___x_670_;
goto v___jp_657_;
}
else
{
lean_object* v___x_672_; 
lean_dec(v_val_664_);
lean_dec(v_key_663_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v_x_644_);
lean_ctor_set(v___x_666_, 0, v_x_643_);
v___x_672_ = v___x_666_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_x_643_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_x_644_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
v___y_658_ = v___x_672_;
goto v___jp_657_;
}
}
}
}
case 1:
{
lean_object* v_node_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_687_; 
v_node_675_ = lean_ctor_get(v_v_654_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_v_654_);
if (v_isSharedCheck_687_ == 0)
{
v___x_677_ = v_v_654_;
v_isShared_678_ = v_isSharedCheck_687_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_node_675_);
lean_dec(v_v_654_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_687_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
size_t v___x_679_; size_t v___x_680_; size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_679_ = ((size_t)5ULL);
v___x_680_ = lean_usize_shift_right(v_x_641_, v___x_679_);
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_x_642_, v___x_681_);
v___x_683_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_node_675_, v___x_680_, v___x_682_, v_x_643_, v_x_644_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_683_);
v___x_685_ = v___x_677_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
v___y_658_ = v___x_685_;
goto v___jp_657_;
}
}
}
default: 
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_x_643_);
lean_ctor_set(v___x_688_, 1, v_x_644_);
v___y_658_ = v___x_688_;
goto v___jp_657_;
}
}
v___jp_657_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_array_fset(v_xs_x27_656_, v_j_648_, v___y_658_);
lean_dec(v_j_648_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_659_);
v___x_661_ = v___x_652_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
else
{
lean_object* v_ks_691_; lean_object* v_vs_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_712_; 
v_ks_691_ = lean_ctor_get(v_x_640_, 0);
v_vs_692_ = lean_ctor_get(v_x_640_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_x_640_);
if (v_isSharedCheck_712_ == 0)
{
v___x_694_ = v_x_640_;
v_isShared_695_ = v_isSharedCheck_712_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_vs_692_);
lean_inc(v_ks_691_);
lean_dec(v_x_640_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_712_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_ks_691_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_vs_692_);
v___x_697_ = v_reuseFailAlloc_711_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v_newNode_698_; uint8_t v___y_700_; size_t v___x_706_; uint8_t v___x_707_; 
v_newNode_698_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(v___x_697_, v_x_643_, v_x_644_);
v___x_706_ = ((size_t)7ULL);
v___x_707_ = lean_usize_dec_le(v___x_706_, v_x_642_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_708_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_698_);
v___x_709_ = lean_unsigned_to_nat(4u);
v___x_710_ = lean_nat_dec_lt(v___x_708_, v___x_709_);
lean_dec(v___x_708_);
v___y_700_ = v___x_710_;
goto v___jp_699_;
}
else
{
v___y_700_ = v___x_707_;
goto v___jp_699_;
}
v___jp_699_:
{
if (v___y_700_ == 0)
{
lean_object* v_ks_701_; lean_object* v_vs_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_ks_701_ = lean_ctor_get(v_newNode_698_, 0);
lean_inc_ref(v_ks_701_);
v_vs_702_ = lean_ctor_get(v_newNode_698_, 1);
lean_inc_ref(v_vs_702_);
lean_dec_ref(v_newNode_698_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0);
v___x_705_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_x_642_, v_ks_701_, v_vs_702_, v___x_703_, v___x_704_);
lean_dec_ref(v_vs_702_);
lean_dec_ref(v_ks_701_);
return v___x_705_;
}
else
{
return v_newNode_698_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_713_, lean_object* v_keys_714_, lean_object* v_vals_715_, lean_object* v_i_716_, lean_object* v_entries_717_){
_start:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_array_get_size(v_keys_714_);
v___x_719_ = lean_nat_dec_lt(v_i_716_, v___x_718_);
if (v___x_719_ == 0)
{
lean_dec(v_i_716_);
return v_entries_717_;
}
else
{
lean_object* v_k_720_; lean_object* v_v_721_; uint64_t v___x_722_; size_t v_h_723_; size_t v___x_724_; lean_object* v___x_725_; size_t v___x_726_; size_t v___x_727_; size_t v___x_728_; size_t v_h_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_k_720_ = lean_array_fget_borrowed(v_keys_714_, v_i_716_);
v_v_721_ = lean_array_fget_borrowed(v_vals_715_, v_i_716_);
v___x_722_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_720_);
v_h_723_ = lean_uint64_to_usize(v___x_722_);
v___x_724_ = ((size_t)5ULL);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_sub(v_depth_713_, v___x_726_);
v___x_728_ = lean_usize_mul(v___x_724_, v___x_727_);
v_h_729_ = lean_usize_shift_right(v_h_723_, v___x_728_);
v___x_730_ = lean_nat_add(v_i_716_, v___x_725_);
lean_dec(v_i_716_);
lean_inc(v_v_721_);
lean_inc(v_k_720_);
v___x_731_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_entries_717_, v_h_729_, v_depth_713_, v_k_720_, v_v_721_);
v_i_716_ = v___x_730_;
v_entries_717_ = v___x_731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_733_, lean_object* v_keys_734_, lean_object* v_vals_735_, lean_object* v_i_736_, lean_object* v_entries_737_){
_start:
{
size_t v_depth_boxed_738_; lean_object* v_res_739_; 
v_depth_boxed_738_ = lean_unbox_usize(v_depth_733_);
lean_dec(v_depth_733_);
v_res_739_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_738_, v_keys_734_, v_vals_735_, v_i_736_, v_entries_737_);
lean_dec_ref(v_vals_735_);
lean_dec_ref(v_keys_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
size_t v_x_5531__boxed_745_; size_t v_x_5532__boxed_746_; lean_object* v_res_747_; 
v_x_5531__boxed_745_ = lean_unbox_usize(v_x_741_);
lean_dec(v_x_741_);
v_x_5532__boxed_746_ = lean_unbox_usize(v_x_742_);
lean_dec(v_x_742_);
v_res_747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_740_, v_x_5531__boxed_745_, v_x_5532__boxed_746_, v_x_743_, v_x_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
uint64_t v___x_751_; size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v___x_751_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_749_);
v___x_752_ = lean_uint64_to_usize(v___x_751_);
v___x_753_ = ((size_t)1ULL);
v___x_754_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_748_, v___x_752_, v___x_753_, v_x_749_, v_x_750_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0(lean_object* v_type_755_, lean_object* v_a_756_, lean_object* v_s_757_){
_start:
{
lean_object* v_structs_758_; lean_object* v_typeIdOf_759_; lean_object* v_exprToStructId_760_; lean_object* v_termMap_761_; lean_object* v_termMapInv_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_770_; 
v_structs_758_ = lean_ctor_get(v_s_757_, 0);
v_typeIdOf_759_ = lean_ctor_get(v_s_757_, 1);
v_exprToStructId_760_ = lean_ctor_get(v_s_757_, 2);
v_termMap_761_ = lean_ctor_get(v_s_757_, 3);
v_termMapInv_762_ = lean_ctor_get(v_s_757_, 4);
v_isSharedCheck_770_ = !lean_is_exclusive(v_s_757_);
if (v_isSharedCheck_770_ == 0)
{
v___x_764_ = v_s_757_;
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_termMapInv_762_);
lean_inc(v_termMap_761_);
lean_inc(v_exprToStructId_760_);
lean_inc(v_typeIdOf_759_);
lean_inc(v_structs_758_);
lean_dec(v_s_757_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(v_typeIdOf_759_, v_type_755_, v_a_756_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_structs_758_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_exprToStructId_760_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v_termMap_761_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_termMapInv_762_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_771_, lean_object* v_vals_772_, lean_object* v_i_773_, lean_object* v_k_774_){
_start:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_array_get_size(v_keys_771_);
v___x_776_ = lean_nat_dec_lt(v_i_773_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_dec(v_i_773_);
v___x_777_ = lean_box(0);
return v___x_777_;
}
else
{
lean_object* v_k_x27_778_; uint8_t v___x_779_; 
v_k_x27_778_ = lean_array_fget_borrowed(v_keys_771_, v_i_773_);
v___x_779_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_774_, v_k_x27_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_i_773_, v___x_780_);
lean_dec(v_i_773_);
v_i_773_ = v___x_781_;
goto _start;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_array_fget_borrowed(v_vals_772_, v_i_773_);
lean_dec(v_i_773_);
lean_inc(v___x_783_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_785_, lean_object* v_vals_786_, lean_object* v_i_787_, lean_object* v_k_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_785_, v_vals_786_, v_i_787_, v_k_788_);
lean_dec_ref(v_k_788_);
lean_dec_ref(v_vals_786_);
lean_dec_ref(v_keys_785_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_790_, size_t v_x_791_, lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_790_) == 0)
{
lean_object* v_es_793_; lean_object* v___x_794_; size_t v___x_795_; size_t v___x_796_; lean_object* v_j_797_; lean_object* v___x_798_; 
v_es_793_ = lean_ctor_get(v_x_790_, 0);
v___x_794_ = lean_box(2);
v___x_795_ = ((size_t)31ULL);
v___x_796_ = lean_usize_land(v_x_791_, v___x_795_);
v_j_797_ = lean_usize_to_nat(v___x_796_);
v___x_798_ = lean_array_get_borrowed(v___x_794_, v_es_793_, v_j_797_);
lean_dec(v_j_797_);
switch(lean_obj_tag(v___x_798_))
{
case 0:
{
lean_object* v_key_799_; lean_object* v_val_800_; uint8_t v___x_801_; 
v_key_799_ = lean_ctor_get(v___x_798_, 0);
v_val_800_ = lean_ctor_get(v___x_798_, 1);
v___x_801_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_792_, v_key_799_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
v___x_802_ = lean_box(0);
return v___x_802_;
}
else
{
lean_object* v___x_803_; 
lean_inc(v_val_800_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_val_800_);
return v___x_803_;
}
}
case 1:
{
lean_object* v_node_804_; size_t v___x_805_; size_t v___x_806_; 
v_node_804_ = lean_ctor_get(v___x_798_, 0);
v___x_805_ = ((size_t)5ULL);
v___x_806_ = lean_usize_shift_right(v_x_791_, v___x_805_);
v_x_790_ = v_node_804_;
v_x_791_ = v___x_806_;
goto _start;
}
default: 
{
lean_object* v___x_808_; 
v___x_808_ = lean_box(0);
return v___x_808_;
}
}
}
else
{
lean_object* v_ks_809_; lean_object* v_vs_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_ks_809_ = lean_ctor_get(v_x_790_, 0);
v_vs_810_ = lean_ctor_get(v_x_790_, 1);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_809_, v_vs_810_, v___x_811_, v_x_792_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
size_t v_x_5737__boxed_816_; lean_object* v_res_817_; 
v_x_5737__boxed_816_ = lean_unbox_usize(v_x_814_);
lean_dec(v_x_814_);
v_res_817_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_813_, v_x_5737__boxed_816_, v_x_815_);
lean_dec_ref(v_x_815_);
lean_dec_ref(v_x_813_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
uint64_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
v___x_820_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_819_);
v___x_821_ = lean_uint64_to_usize(v___x_820_);
v___x_822_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_818_, v___x_821_, v_x_819_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_x_823_, v_x_824_);
lean_dec_ref(v_x_824_);
lean_dec_ref(v_x_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f(lean_object* v_type_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_829_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_889_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_889_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_889_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_889_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
uint8_t v_order_843_; 
v_order_843_ = lean_ctor_get_uint8(v_a_839_, sizeof(void*)*13 + 27);
lean_dec(v_a_839_);
if (v_order_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_846_; 
lean_dec_ref(v_type_826_);
v___x_844_ = lean_box(0);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_844_);
v___x_846_ = v___x_841_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v___x_848_; 
lean_del_object(v___x_841_);
v___x_848_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_827_, v_a_835_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_880_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_880_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_880_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_880_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_typeIdOf_853_; lean_object* v___x_854_; 
v_typeIdOf_853_ = lean_ctor_get(v_a_849_, 1);
lean_inc_ref(v_typeIdOf_853_);
lean_dec(v_a_849_);
v___x_854_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_typeIdOf_853_, v_type_826_);
lean_dec_ref(v_typeIdOf_853_);
if (lean_obj_tag(v___x_854_) == 1)
{
lean_object* v_val_855_; lean_object* v___x_857_; 
lean_dec_ref(v_type_826_);
v_val_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v___x_854_, 1);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v_val_855_);
v___x_857_ = v___x_851_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_val_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
lean_object* v___x_859_; 
lean_dec(v___x_854_);
lean_del_object(v___x_851_);
lean_inc_ref(v_type_826_);
v___x_859_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(v_type_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_n(v_a_860_, 2);
lean_dec_ref_known(v___x_859_, 1);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_861_, 0, v_type_826_);
lean_closure_set(v___f_861_, 1, v_a_860_);
v___x_862_ = l_Lean_Meta_Grind_Order_orderExt;
v___x_863_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_862_, v___f_861_, v_a_827_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_871_);
v___x_865_ = v___x_863_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_863_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v_a_860_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_860_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_860_);
v_a_872_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_863_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_863_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_dec_ref(v_type_826_);
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v_type_826_);
v_a_881_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_848_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_848_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_type_826_);
v_a_890_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_838_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_838_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_getStructId_x3f___boxed(lean_object* v_type_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Meta_Grind_Order_getStructId_x3f(v_type_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec(v_a_899_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(lean_object* v_00_u03b2_911_, lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_x_912_, v_x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_915_, lean_object* v_x_916_, lean_object* v_x_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(v_00_u03b2_915_, v_x_916_, v_x_917_);
lean_dec_ref(v_x_917_);
lean_dec_ref(v_x_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1(lean_object* v_00_u03b2_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(v_x_920_, v_x_921_, v_x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_924_, lean_object* v_x_925_, size_t v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_925_, v_x_926_, v_x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
size_t v_x_5933__boxed_933_; lean_object* v_res_934_; 
v_x_5933__boxed_933_ = lean_unbox_usize(v_x_931_);
lean_dec(v_x_931_);
v_res_934_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(v_00_u03b2_929_, v_x_930_, v_x_5933__boxed_933_, v_x_932_);
lean_dec_ref(v_x_932_);
lean_dec_ref(v_x_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(lean_object* v_00_u03b2_935_, lean_object* v_x_936_, size_t v_x_937_, size_t v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_936_, v_x_937_, v_x_938_, v_x_939_, v_x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_942_, lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
size_t v_x_5944__boxed_948_; size_t v_x_5945__boxed_949_; lean_object* v_res_950_; 
v_x_5944__boxed_948_ = lean_unbox_usize(v_x_944_);
lean_dec(v_x_944_);
v_x_5945__boxed_949_ = lean_unbox_usize(v_x_945_);
lean_dec(v_x_945_);
v_res_950_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(v_00_u03b2_942_, v_x_943_, v_x_5944__boxed_948_, v_x_5945__boxed_949_, v_x_946_, v_x_947_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_951_, lean_object* v_keys_952_, lean_object* v_vals_953_, lean_object* v_heq_954_, lean_object* v_i_955_, lean_object* v_k_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_952_, v_vals_953_, v_i_955_, v_k_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_958_, lean_object* v_keys_959_, lean_object* v_vals_960_, lean_object* v_heq_961_, lean_object* v_i_962_, lean_object* v_k_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_958_, v_keys_959_, v_vals_960_, v_heq_961_, v_i_962_, v_k_963_);
lean_dec_ref(v_k_963_);
lean_dec_ref(v_vals_960_);
lean_dec_ref(v_keys_959_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_965_, lean_object* v_n_966_, lean_object* v_k_967_, lean_object* v_v_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(v_n_966_, v_k_967_, v_v_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_970_, size_t v_depth_971_, lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_heq_974_, lean_object* v_i_975_, lean_object* v_entries_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_971_, v_keys_972_, v_vals_973_, v_i_975_, v_entries_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_978_, lean_object* v_depth_979_, lean_object* v_keys_980_, lean_object* v_vals_981_, lean_object* v_heq_982_, lean_object* v_i_983_, lean_object* v_entries_984_){
_start:
{
size_t v_depth_boxed_985_; lean_object* v_res_986_; 
v_depth_boxed_985_ = lean_unbox_usize(v_depth_979_);
lean_dec(v_depth_979_);
v_res_986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_978_, v_depth_boxed_985_, v_keys_980_, v_vals_981_, v_heq_982_, v_i_983_, v_entries_984_);
lean_dec_ref(v_vals_981_);
lean_dec_ref(v_keys_980_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_987_, lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_988_, v_x_989_, v_x_990_, v_x_991_);
return v___x_992_;
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
