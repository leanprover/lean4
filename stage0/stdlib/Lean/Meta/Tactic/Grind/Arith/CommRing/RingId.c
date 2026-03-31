// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM import Lean.Meta.Tactic.Grind.Arith.Insts
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "NoNatZeroDivisors available: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "new ring: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(184, 238, 182, 216, 107, 45, 243, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "`grind` unexpected failure, failure to initialize ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0(lean_object* v_00_u03b2_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(lean_object* v___x_6_, lean_object* v_s_7_){
_start:
{
lean_object* v_rings_8_; lean_object* v_typeIdOf_9_; lean_object* v_exprToRingId_10_; lean_object* v_semirings_11_; lean_object* v_stypeIdOf_12_; lean_object* v_exprToSemiringId_13_; lean_object* v_ncRings_14_; lean_object* v_exprToNCRingId_15_; lean_object* v_nctypeIdOf_16_; lean_object* v_ncSemirings_17_; lean_object* v_exprToNCSemiringId_18_; lean_object* v_ncstypeIdOf_19_; lean_object* v_steps_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_28_; 
v_rings_8_ = lean_ctor_get(v_s_7_, 0);
v_typeIdOf_9_ = lean_ctor_get(v_s_7_, 1);
v_exprToRingId_10_ = lean_ctor_get(v_s_7_, 2);
v_semirings_11_ = lean_ctor_get(v_s_7_, 3);
v_stypeIdOf_12_ = lean_ctor_get(v_s_7_, 4);
v_exprToSemiringId_13_ = lean_ctor_get(v_s_7_, 5);
v_ncRings_14_ = lean_ctor_get(v_s_7_, 6);
v_exprToNCRingId_15_ = lean_ctor_get(v_s_7_, 7);
v_nctypeIdOf_16_ = lean_ctor_get(v_s_7_, 8);
v_ncSemirings_17_ = lean_ctor_get(v_s_7_, 9);
v_exprToNCSemiringId_18_ = lean_ctor_get(v_s_7_, 10);
v_ncstypeIdOf_19_ = lean_ctor_get(v_s_7_, 11);
v_steps_20_ = lean_ctor_get(v_s_7_, 12);
v_isSharedCheck_28_ = !lean_is_exclusive(v_s_7_);
if (v_isSharedCheck_28_ == 0)
{
v___x_22_ = v_s_7_;
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_steps_20_);
lean_inc(v_ncstypeIdOf_19_);
lean_inc(v_exprToNCSemiringId_18_);
lean_inc(v_ncSemirings_17_);
lean_inc(v_nctypeIdOf_16_);
lean_inc(v_exprToNCRingId_15_);
lean_inc(v_ncRings_14_);
lean_inc(v_exprToSemiringId_13_);
lean_inc(v_stypeIdOf_12_);
lean_inc(v_semirings_11_);
lean_inc(v_exprToRingId_10_);
lean_inc(v_typeIdOf_9_);
lean_inc(v_rings_8_);
lean_dec(v_s_7_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_24_ = lean_array_push(v_rings_8_, v___x_6_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_24_);
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_typeIdOf_9_);
lean_ctor_set(v_reuseFailAlloc_27_, 2, v_exprToRingId_10_);
lean_ctor_set(v_reuseFailAlloc_27_, 3, v_semirings_11_);
lean_ctor_set(v_reuseFailAlloc_27_, 4, v_stypeIdOf_12_);
lean_ctor_set(v_reuseFailAlloc_27_, 5, v_exprToSemiringId_13_);
lean_ctor_set(v_reuseFailAlloc_27_, 6, v_ncRings_14_);
lean_ctor_set(v_reuseFailAlloc_27_, 7, v_exprToNCRingId_15_);
lean_ctor_set(v_reuseFailAlloc_27_, 8, v_nctypeIdOf_16_);
lean_ctor_set(v_reuseFailAlloc_27_, 9, v_ncSemirings_17_);
lean_ctor_set(v_reuseFailAlloc_27_, 10, v_exprToNCSemiringId_18_);
lean_ctor_set(v_reuseFailAlloc_27_, 11, v_ncstypeIdOf_19_);
lean_ctor_set(v_reuseFailAlloc_27_, 12, v_steps_20_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(lean_object* v_msgData_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; lean_object* v_env_36_; lean_object* v___x_37_; lean_object* v_mctx_38_; lean_object* v_lctx_39_; lean_object* v_options_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_35_ = lean_st_ref_get(v___y_33_);
v_env_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc_ref(v_env_36_);
lean_dec(v___x_35_);
v___x_37_ = lean_st_ref_get(v___y_31_);
v_mctx_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc_ref(v_mctx_38_);
lean_dec(v___x_37_);
v_lctx_39_ = lean_ctor_get(v___y_30_, 2);
v_options_40_ = lean_ctor_get(v___y_32_, 2);
lean_inc_ref(v_options_40_);
lean_inc_ref(v_lctx_39_);
v___x_41_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_41_, 0, v_env_36_);
lean_ctor_set(v___x_41_, 1, v_mctx_38_);
lean_ctor_set(v___x_41_, 2, v_lctx_39_);
lean_ctor_set(v___x_41_, 3, v_options_40_);
v___x_42_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v_msgData_29_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1___boxed(lean_object* v_msgData_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msgData_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_50_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_51_; double v___x_52_; 
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_float_of_nat(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(lean_object* v_cls_56_, lean_object* v_msg_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_ref_63_; lean_object* v___x_64_; lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_109_; 
v_ref_63_ = lean_ctor_get(v___y_60_, 5);
v___x_64_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_109_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_109_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_109_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v_traceState_70_; lean_object* v_env_71_; lean_object* v_nextMacroScope_72_; lean_object* v_ngen_73_; lean_object* v_auxDeclNGen_74_; lean_object* v_cache_75_; lean_object* v_messages_76_; lean_object* v_infoState_77_; lean_object* v_snapshotTasks_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_108_; 
v___x_69_ = lean_st_ref_take(v___y_61_);
v_traceState_70_ = lean_ctor_get(v___x_69_, 4);
v_env_71_ = lean_ctor_get(v___x_69_, 0);
v_nextMacroScope_72_ = lean_ctor_get(v___x_69_, 1);
v_ngen_73_ = lean_ctor_get(v___x_69_, 2);
v_auxDeclNGen_74_ = lean_ctor_get(v___x_69_, 3);
v_cache_75_ = lean_ctor_get(v___x_69_, 5);
v_messages_76_ = lean_ctor_get(v___x_69_, 6);
v_infoState_77_ = lean_ctor_get(v___x_69_, 7);
v_snapshotTasks_78_ = lean_ctor_get(v___x_69_, 8);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_108_ == 0)
{
v___x_80_ = v___x_69_;
v_isShared_81_ = v_isSharedCheck_108_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_snapshotTasks_78_);
lean_inc(v_infoState_77_);
lean_inc(v_messages_76_);
lean_inc(v_cache_75_);
lean_inc(v_traceState_70_);
lean_inc(v_auxDeclNGen_74_);
lean_inc(v_ngen_73_);
lean_inc(v_nextMacroScope_72_);
lean_inc(v_env_71_);
lean_dec(v___x_69_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_108_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint64_t v_tid_82_; lean_object* v_traces_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_107_; 
v_tid_82_ = lean_ctor_get_uint64(v_traceState_70_, sizeof(void*)*1);
v_traces_83_ = lean_ctor_get(v_traceState_70_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v_traceState_70_);
if (v_isSharedCheck_107_ == 0)
{
v___x_85_ = v_traceState_70_;
v_isShared_86_ = v_isSharedCheck_107_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_traces_83_);
lean_dec(v_traceState_70_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_107_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; double v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_87_ = lean_box(0);
v___x_88_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0);
v___x_89_ = 0;
v___x_90_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1));
v___x_91_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_91_, 0, v_cls_56_);
lean_ctor_set(v___x_91_, 1, v___x_87_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
lean_ctor_set_float(v___x_91_, sizeof(void*)*3, v___x_88_);
lean_ctor_set_float(v___x_91_, sizeof(void*)*3 + 8, v___x_88_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*3 + 16, v___x_89_);
v___x_92_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2));
v___x_93_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v_a_65_);
lean_ctor_set(v___x_93_, 2, v___x_92_);
lean_inc(v_ref_63_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_ref_63_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = l_Lean_PersistentArray_push___redArg(v_traces_83_, v___x_94_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_95_);
v___x_97_ = v___x_85_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_95_);
lean_ctor_set_uint64(v_reuseFailAlloc_106_, sizeof(void*)*1, v_tid_82_);
v___x_97_ = v_reuseFailAlloc_106_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_99_; 
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 4, v___x_97_);
v___x_99_ = v___x_80_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_env_71_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_nextMacroScope_72_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v_ngen_73_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v_auxDeclNGen_74_);
lean_ctor_set(v_reuseFailAlloc_105_, 4, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_105_, 5, v_cache_75_);
lean_ctor_set(v_reuseFailAlloc_105_, 6, v_messages_76_);
lean_ctor_set(v_reuseFailAlloc_105_, 7, v_infoState_77_);
lean_ctor_set(v_reuseFailAlloc_105_, 8, v_snapshotTasks_78_);
v___x_99_ = v_reuseFailAlloc_105_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_100_ = lean_st_ref_set(v___y_61_, v___x_99_);
v___x_101_ = lean_box(0);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_101_);
v___x_103_ = v___x_67_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_cls_110_, lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_110_, v_msg_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_unsigned_to_nat(32u);
v___x_150_ = lean_mk_empty_array_with_capacity(v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14(void){
_start:
{
size_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_152_ = ((size_t)5ULL);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_unsigned_to_nat(32u);
v___x_155_ = lean_mk_empty_array_with_capacity(v___x_154_);
v___x_156_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13);
v___x_157_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
lean_ctor_set(v___x_157_, 2, v___x_153_);
lean_ctor_set(v___x_157_, 3, v___x_153_);
lean_ctor_set_usize(v___x_157_, 4, v___x_152_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0(lean_box(0));
return v___x_161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20));
v___x_171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22));
v___x_172_ = l_Lean_Name_append(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24));
v___x_175_ = l_Lean_stringToMessageData(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(lean_object* v_type_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; 
lean_inc_ref(v_type_181_);
v___x_193_ = l_Lean_Meta_getDecLevel(v_type_181_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc_n(v_a_194_, 2);
lean_dec_ref(v___x_193_);
v___x_195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3));
v___x_196_ = lean_box(0);
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v_a_194_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
lean_inc_ref(v___x_197_);
v___x_198_ = l_Lean_mkConst(v___x_195_, v___x_197_);
lean_inc_ref(v_type_181_);
v___x_199_ = l_Lean_Expr_app___override(v___x_198_, v_type_181_);
v___x_200_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_199_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_390_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_390_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_390_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_390_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
if (lean_obj_tag(v_a_201_) == 1)
{
lean_object* v_val_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_385_; 
lean_del_object(v___x_203_);
v_val_205_ = lean_ctor_get(v_a_201_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_a_201_);
if (v_isSharedCheck_385_ == 0)
{
v___x_207_ = v_a_201_;
v_isShared_208_ = v_isSharedCheck_385_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_val_205_);
lean_dec(v_a_201_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_385_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_options_212_; lean_object* v_inheritedTraceOptions_213_; uint8_t v_hasTrace_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___x_285_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; 
v___x_209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5));
lean_inc_ref_n(v___x_197_, 3);
v___x_210_ = l_Lean_mkConst(v___x_209_, v___x_197_);
lean_inc(v_val_205_);
lean_inc_ref_n(v_type_181_, 3);
v___x_211_ = l_Lean_mkAppB(v___x_210_, v_type_181_, v_val_205_);
v_options_212_ = lean_ctor_get(v_a_190_, 2);
v_inheritedTraceOptions_213_ = lean_ctor_get(v_a_190_, 13);
v_hasTrace_214_ = lean_ctor_get_uint8(v_options_212_, sizeof(void*)*1);
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8));
v___x_216_ = l_Lean_mkConst(v___x_215_, v___x_197_);
lean_inc_ref(v___x_211_);
v___x_217_ = l_Lean_mkAppB(v___x_216_, v_type_181_, v___x_211_);
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10));
v___x_219_ = l_Lean_mkConst(v___x_218_, v___x_197_);
lean_inc_ref(v___x_217_);
v___x_220_ = l_Lean_mkAppB(v___x_219_, v_type_181_, v___x_217_);
v___x_285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20));
if (v_hasTrace_214_ == 0)
{
v___y_314_ = v_a_182_;
v___y_315_ = v_a_183_;
v___y_316_ = v_a_184_;
v___y_317_ = v_a_185_;
v___y_318_ = v_a_186_;
v___y_319_ = v_a_187_;
v___y_320_ = v_a_188_;
v___y_321_ = v_a_189_;
v___y_322_ = v_a_190_;
v___y_323_ = v_a_191_;
goto v___jp_313_;
}
else
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23);
v___x_363_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_213_, v_options_212_, v___x_362_);
if (v___x_363_ == 0)
{
v___y_314_ = v_a_182_;
v___y_315_ = v_a_183_;
v___y_316_ = v_a_184_;
v___y_317_ = v_a_185_;
v___y_318_ = v_a_186_;
v___y_319_ = v_a_187_;
v___y_320_ = v_a_188_;
v___y_321_ = v_a_189_;
v___y_322_ = v_a_190_;
v___y_323_ = v_a_191_;
goto v___jp_313_;
}
else
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_Grind_updateLastTag(v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec_ref(v___x_364_);
v___x_365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
lean_inc_ref(v_type_181_);
v___x_366_ = l_Lean_MessageData_ofExpr(v_type_181_);
v___x_367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_285_, v___x_367_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_dec_ref(v___x_368_);
v___y_314_ = v_a_182_;
v___y_315_ = v_a_183_;
v___y_316_ = v_a_184_;
v___y_317_ = v_a_185_;
v___y_318_ = v_a_186_;
v___y_319_ = v_a_187_;
v___y_320_ = v_a_188_;
v___y_321_ = v_a_189_;
v___y_322_ = v_a_190_;
v___y_323_ = v_a_191_;
goto v___jp_313_;
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v___x_220_);
lean_dec_ref(v___x_217_);
lean_dec_ref(v___x_211_);
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
lean_dec_ref(v___x_197_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v___x_220_);
lean_dec_ref(v___x_217_);
lean_dec_ref(v___x_211_);
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
lean_dec_ref(v___x_197_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v_a_377_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_364_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_364_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
v___jp_221_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12));
v___x_230_ = l_Lean_mkConst(v___x_229_, v___x_197_);
lean_inc_ref(v_type_181_);
v___x_231_ = l_Lean_Expr_app___override(v___x_230_, v_type_181_);
v___x_232_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_231_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_234_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref(v___x_232_);
v___x_234_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_224_, v___y_227_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v_rings_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref(v___x_234_);
v_rings_236_ = lean_ctor_get(v_a_235_, 0);
lean_inc_ref(v_rings_236_);
lean_dec(v_a_235_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_array_get_size(v_rings_236_);
lean_dec_ref(v_rings_236_);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14);
v___x_241_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16);
v___x_242_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_242_, 0, v___x_238_);
lean_ctor_set(v___x_242_, 1, v_type_181_);
lean_ctor_set(v___x_242_, 2, v_a_194_);
lean_ctor_set(v___x_242_, 3, v___x_211_);
lean_ctor_set(v___x_242_, 4, v___x_217_);
lean_ctor_set(v___x_242_, 5, v___y_223_);
lean_ctor_set(v___x_242_, 6, v___x_237_);
lean_ctor_set(v___x_242_, 7, v___x_237_);
lean_ctor_set(v___x_242_, 8, v___x_237_);
lean_ctor_set(v___x_242_, 9, v___x_237_);
lean_ctor_set(v___x_242_, 10, v___x_237_);
lean_ctor_set(v___x_242_, 11, v___x_237_);
lean_ctor_set(v___x_242_, 12, v___x_237_);
lean_ctor_set(v___x_242_, 13, v___x_237_);
lean_ctor_set(v___x_242_, 14, v___x_240_);
lean_ctor_set(v___x_242_, 15, v___x_241_);
lean_ctor_set(v___x_242_, 16, v___x_241_);
v___x_243_ = lean_box(1);
v___x_244_ = 0;
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17);
v___x_246_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v___x_246_, 0, v___x_242_);
lean_ctor_set(v___x_246_, 1, v___x_237_);
lean_ctor_set(v___x_246_, 2, v___x_237_);
lean_ctor_set(v___x_246_, 3, v___x_220_);
lean_ctor_set(v___x_246_, 4, v_val_205_);
lean_ctor_set(v___x_246_, 5, v___y_222_);
lean_ctor_set(v___x_246_, 6, v_a_233_);
lean_ctor_set(v___x_246_, 7, v___x_240_);
lean_ctor_set(v___x_246_, 8, v___x_239_);
lean_ctor_set(v___x_246_, 9, v___x_239_);
lean_ctor_set(v___x_246_, 10, v___x_243_);
lean_ctor_set(v___x_246_, 11, v___x_196_);
lean_ctor_set(v___x_246_, 12, v___x_240_);
lean_ctor_set(v___x_246_, 13, v___x_245_);
lean_ctor_set(v___x_246_, 14, v___x_237_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*15, v___x_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*15 + 1, v___x_244_);
v___f_247_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_247_, 0, v___x_246_);
v___x_248_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_249_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_248_, v___f_247_, v___y_224_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_259_; 
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_259_ == 0)
{
lean_object* v_unused_260_; 
v_unused_260_ = lean_ctor_get(v___x_249_, 0);
lean_dec(v_unused_260_);
v___x_251_ = v___x_249_;
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
else
{
lean_dec(v___x_249_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_238_);
v___x_254_ = v___x_207_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_238_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_254_);
v___x_256_ = v___x_251_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_del_object(v___x_207_);
v_a_261_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_249_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_249_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_233_);
lean_dec(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___x_220_);
lean_dec_ref(v___x_217_);
lean_dec_ref(v___x_211_);
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v_a_269_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_234_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_234_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___x_220_);
lean_dec_ref(v___x_217_);
lean_dec_ref(v___x_211_);
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v_a_277_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_232_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_232_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
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
v___jp_286_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_inc_ref(v___y_300_);
v___x_301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_301_, 0, v___y_300_);
v___x_302_ = l_Lean_MessageData_ofFormat(v___x_301_);
lean_inc_ref(v___y_295_);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v___y_295_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_285_, v___x_303_, v___y_290_, v___y_287_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_dec_ref(v___x_304_);
v___y_222_ = v___y_299_;
v___y_223_ = v___y_298_;
v___y_224_ = v___y_293_;
v___y_225_ = v___y_290_;
v___y_226_ = v___y_287_;
v___y_227_ = v___y_291_;
v___y_228_ = v___y_292_;
goto v___jp_221_;
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___x_220_);
lean_dec_ref(v___x_217_);
lean_dec_ref(v___x_211_);
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
lean_dec_ref(v___x_197_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
v___jp_313_:
{
lean_object* v___x_324_; 
lean_inc_ref(v___x_217_);
lean_inc_ref(v_type_181_);
lean_inc(v_a_194_);
v___x_324_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_194_, v_type_181_, v___x_217_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref(v___x_324_);
lean_inc_ref(v_type_181_);
lean_inc(v_a_194_);
v___x_326_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_a_194_, v_type_181_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_options_327_; uint8_t v_hasTrace_328_; 
v_options_327_ = lean_ctor_get(v___y_322_, 2);
v_hasTrace_328_ = lean_ctor_get_uint8(v_options_327_, sizeof(void*)*1);
if (v_hasTrace_328_ == 0)
{
lean_object* v_a_329_; 
v_a_329_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_329_);
lean_dec_ref(v___x_326_);
v___y_222_ = v_a_329_;
v___y_223_ = v_a_325_;
v___y_224_ = v___y_314_;
v___y_225_ = v___y_320_;
v___y_226_ = v___y_321_;
v___y_227_ = v___y_322_;
v___y_228_ = v___y_323_;
goto v___jp_221_;
}
else
{
lean_object* v_a_330_; lean_object* v_inheritedTraceOptions_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_a_330_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_330_);
lean_dec_ref(v___x_326_);
v_inheritedTraceOptions_331_ = lean_ctor_get(v___y_322_, 13);
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23);
v___x_333_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_331_, v_options_327_, v___x_332_);
if (v___x_333_ == 0)
{
v___y_222_ = v_a_330_;
v___y_223_ = v_a_325_;
v___y_224_ = v___y_314_;
v___y_225_ = v___y_320_;
v___y_226_ = v___y_321_;
v___y_227_ = v___y_322_;
v___y_228_ = v___y_323_;
goto v___jp_221_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Grind_updateLastTag(v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v___x_335_; 
lean_dec_ref(v___x_334_);
v___x_335_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25);
if (lean_obj_tag(v_a_330_) == 0)
{
lean_object* v___x_336_; 
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26));
v___y_287_ = v___y_321_;
v___y_288_ = v___y_318_;
v___y_289_ = v___y_316_;
v___y_290_ = v___y_320_;
v___y_291_ = v___y_322_;
v___y_292_ = v___y_323_;
v___y_293_ = v___y_314_;
v___y_294_ = v___y_317_;
v___y_295_ = v___x_335_;
v___y_296_ = v___y_319_;
v___y_297_ = v___y_315_;
v___y_298_ = v_a_325_;
v___y_299_ = v_a_330_;
v___y_300_ = v___x_336_;
goto v___jp_286_;
}
else
{
lean_object* v___x_337_; 
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27));
v___y_287_ = v___y_321_;
v___y_288_ = v___y_318_;
v___y_289_ = v___y_316_;
v___y_290_ = v___y_320_;
v___y_291_ = v___y_322_;
v___y_292_ = v___y_323_;
v___y_293_ = v___y_314_;
v___y_294_ = v___y_317_;
v___y_295_ = v___x_335_;
v___y_296_ = v___y_319_;
v___y_297_ = v___y_315_;
v___y_298_ = v_a_325_;
v___y_299_ = v_a_330_;
v___y_300_ = v___x_337_;
goto v___jp_286_;
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_a_330_);
lean_dec(v_a_325_);
lean_dec_ref(v___x_220_);
lean_dec_ref(v___x_217_);
lean_dec_ref(v___x_211_);
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
lean_dec_ref(v___x_197_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v_a_338_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_334_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
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
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_a_325_);
lean_dec_ref(v___x_220_);
lean_dec_ref(v___x_217_);
lean_dec_ref(v___x_211_);
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
lean_dec_ref(v___x_197_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v_a_346_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_326_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_326_);
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
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref(v___x_220_);
lean_dec_ref(v___x_217_);
lean_dec_ref(v___x_211_);
lean_del_object(v___x_207_);
lean_dec(v_val_205_);
lean_dec_ref(v___x_197_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v_a_354_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_324_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_324_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec(v_a_201_);
lean_dec_ref(v___x_197_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v___x_386_ = lean_box(0);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_386_);
v___x_388_ = v___x_203_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v___x_197_);
lean_dec(v_a_194_);
lean_dec_ref(v_type_181_);
v_a_391_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_200_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_200_);
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
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v_type_181_);
v_a_399_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_193_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_193_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___boxed(lean_object* v_type_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec(v_a_408_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(lean_object* v_cls_420_, lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_420_, v_msg_421_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___boxed(lean_object* v_cls_434_, lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(v_cls_434_, v_msg_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec(v___y_436_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_ks_452_; lean_object* v_vs_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_477_; 
v_ks_452_ = lean_ctor_get(v_x_448_, 0);
v_vs_453_ = lean_ctor_get(v_x_448_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_477_ == 0)
{
v___x_455_ = v_x_448_;
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_vs_453_);
lean_inc(v_ks_452_);
lean_dec(v_x_448_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_array_get_size(v_ks_452_);
v___x_458_ = lean_nat_dec_lt(v_x_449_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
lean_dec(v_x_449_);
v___x_459_ = lean_array_push(v_ks_452_, v_x_450_);
v___x_460_ = lean_array_push(v_vs_453_, v_x_451_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_460_);
lean_ctor_set(v___x_455_, 0, v___x_459_);
v___x_462_ = v___x_455_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
else
{
lean_object* v_k_x27_464_; uint8_t v___x_465_; 
v_k_x27_464_ = lean_array_fget_borrowed(v_ks_452_, v_x_449_);
v___x_465_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_450_, v_k_x27_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_467_; 
if (v_isShared_456_ == 0)
{
v___x_467_ = v___x_455_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_ks_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_vs_453_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_x_449_, v___x_468_);
lean_dec(v_x_449_);
v_x_448_ = v___x_467_;
v_x_449_ = v___x_469_;
goto _start;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_array_fset(v_ks_452_, v_x_449_, v_x_450_);
v___x_473_ = lean_array_fset(v_vs_453_, v_x_449_, v_x_451_);
lean_dec(v_x_449_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_473_);
lean_ctor_set(v___x_455_, 0, v___x_472_);
v___x_475_ = v___x_455_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_478_, lean_object* v_k_479_, lean_object* v_v_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_478_, v___x_481_, v_k_479_, v_v_480_);
return v___x_482_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; 
v___x_483_ = ((size_t)5ULL);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_shift_left(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_486_; size_t v___x_487_; size_t v___x_488_; 
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0);
v___x_488_ = lean_usize_sub(v___x_487_, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(lean_object* v_x_490_, size_t v_x_491_, size_t v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v_es_495_; size_t v___x_496_; size_t v___x_497_; size_t v___x_498_; size_t v___x_499_; lean_object* v_j_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_es_495_ = lean_ctor_get(v_x_490_, 0);
v___x_496_ = ((size_t)5ULL);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
v___x_499_ = lean_usize_land(v_x_491_, v___x_498_);
v_j_500_ = lean_usize_to_nat(v___x_499_);
v___x_501_ = lean_array_get_size(v_es_495_);
v___x_502_ = lean_nat_dec_lt(v_j_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_dec(v_j_500_);
lean_dec(v_x_494_);
lean_dec_ref(v_x_493_);
return v_x_490_;
}
else
{
lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_539_; 
lean_inc_ref(v_es_495_);
v_isSharedCheck_539_ = !lean_is_exclusive(v_x_490_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v_x_490_, 0);
lean_dec(v_unused_540_);
v___x_504_ = v_x_490_;
v_isShared_505_ = v_isSharedCheck_539_;
goto v_resetjp_503_;
}
else
{
lean_dec(v_x_490_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_539_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_v_506_; lean_object* v___x_507_; lean_object* v_xs_x27_508_; lean_object* v___y_510_; 
v_v_506_ = lean_array_fget(v_es_495_, v_j_500_);
v___x_507_ = lean_box(0);
v_xs_x27_508_ = lean_array_fset(v_es_495_, v_j_500_, v___x_507_);
switch(lean_obj_tag(v_v_506_))
{
case 0:
{
lean_object* v_key_515_; lean_object* v_val_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_526_; 
v_key_515_ = lean_ctor_get(v_v_506_, 0);
v_val_516_ = lean_ctor_get(v_v_506_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v_v_506_);
if (v_isSharedCheck_526_ == 0)
{
v___x_518_ = v_v_506_;
v_isShared_519_ = v_isSharedCheck_526_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_val_516_);
lean_inc(v_key_515_);
lean_dec(v_v_506_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_526_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
uint8_t v___x_520_; 
v___x_520_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_493_, v_key_515_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_del_object(v___x_518_);
v___x_521_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_515_, v_val_516_, v_x_493_, v_x_494_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___y_510_ = v___x_522_;
goto v___jp_509_;
}
else
{
lean_object* v___x_524_; 
lean_dec(v_val_516_);
lean_dec(v_key_515_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v_x_494_);
lean_ctor_set(v___x_518_, 0, v_x_493_);
v___x_524_ = v___x_518_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_x_493_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_x_494_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
v___y_510_ = v___x_524_;
goto v___jp_509_;
}
}
}
}
case 1:
{
lean_object* v_node_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_537_; 
v_node_527_ = lean_ctor_get(v_v_506_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_v_506_);
if (v_isSharedCheck_537_ == 0)
{
v___x_529_ = v_v_506_;
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_node_527_);
lean_dec(v_v_506_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_531_ = lean_usize_shift_right(v_x_491_, v___x_496_);
v___x_532_ = lean_usize_add(v_x_492_, v___x_497_);
v___x_533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_node_527_, v___x_531_, v___x_532_, v_x_493_, v_x_494_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_533_);
v___x_535_ = v___x_529_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
v___y_510_ = v___x_535_;
goto v___jp_509_;
}
}
}
default: 
{
lean_object* v___x_538_; 
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v_x_493_);
lean_ctor_set(v___x_538_, 1, v_x_494_);
v___y_510_ = v___x_538_;
goto v___jp_509_;
}
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_array_fset(v_xs_x27_508_, v_j_500_, v___y_510_);
lean_dec(v_j_500_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_511_);
v___x_513_ = v___x_504_;
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
}
else
{
lean_object* v_ks_541_; lean_object* v_vs_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_562_; 
v_ks_541_ = lean_ctor_get(v_x_490_, 0);
v_vs_542_ = lean_ctor_get(v_x_490_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_x_490_);
if (v_isSharedCheck_562_ == 0)
{
v___x_544_ = v_x_490_;
v_isShared_545_ = v_isSharedCheck_562_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_vs_542_);
lean_inc(v_ks_541_);
lean_dec(v_x_490_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_562_;
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
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_ks_541_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_vs_542_);
v___x_547_ = v_reuseFailAlloc_561_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v_newNode_548_; uint8_t v___y_550_; size_t v___x_556_; uint8_t v___x_557_; 
v_newNode_548_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v___x_547_, v_x_493_, v_x_494_);
v___x_556_ = ((size_t)7ULL);
v___x_557_ = lean_usize_dec_le(v___x_556_, v_x_492_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_558_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_548_);
v___x_559_ = lean_unsigned_to_nat(4u);
v___x_560_ = lean_nat_dec_lt(v___x_558_, v___x_559_);
lean_dec(v___x_558_);
v___y_550_ = v___x_560_;
goto v___jp_549_;
}
else
{
v___y_550_ = v___x_557_;
goto v___jp_549_;
}
v___jp_549_:
{
if (v___y_550_ == 0)
{
lean_object* v_ks_551_; lean_object* v_vs_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_ks_551_ = lean_ctor_get(v_newNode_548_, 0);
lean_inc_ref(v_ks_551_);
v_vs_552_ = lean_ctor_get(v_newNode_548_, 1);
lean_inc_ref(v_vs_552_);
lean_dec_ref(v_newNode_548_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2);
v___x_555_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_x_492_, v_ks_551_, v_vs_552_, v___x_553_, v___x_554_);
lean_dec_ref(v_vs_552_);
lean_dec_ref(v_ks_551_);
return v___x_555_;
}
else
{
return v_newNode_548_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_563_, lean_object* v_keys_564_, lean_object* v_vals_565_, lean_object* v_i_566_, lean_object* v_entries_567_){
_start:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_get_size(v_keys_564_);
v___x_569_ = lean_nat_dec_lt(v_i_566_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec(v_i_566_);
return v_entries_567_;
}
else
{
lean_object* v_k_570_; lean_object* v_v_571_; uint64_t v___x_572_; size_t v_h_573_; size_t v___x_574_; lean_object* v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v_h_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_k_570_ = lean_array_fget_borrowed(v_keys_564_, v_i_566_);
v_v_571_ = lean_array_fget_borrowed(v_vals_565_, v_i_566_);
v___x_572_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_570_);
v_h_573_ = lean_uint64_to_usize(v___x_572_);
v___x_574_ = ((size_t)5ULL);
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_sub(v_depth_563_, v___x_576_);
v___x_578_ = lean_usize_mul(v___x_574_, v___x_577_);
v_h_579_ = lean_usize_shift_right(v_h_573_, v___x_578_);
v___x_580_ = lean_nat_add(v_i_566_, v___x_575_);
lean_dec(v_i_566_);
lean_inc(v_v_571_);
lean_inc(v_k_570_);
v___x_581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_entries_567_, v_h_579_, v_depth_563_, v_k_570_, v_v_571_);
v_i_566_ = v___x_580_;
v_entries_567_ = v___x_581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_583_, lean_object* v_keys_584_, lean_object* v_vals_585_, lean_object* v_i_586_, lean_object* v_entries_587_){
_start:
{
size_t v_depth_boxed_588_; lean_object* v_res_589_; 
v_depth_boxed_588_ = lean_unbox_usize(v_depth_583_);
lean_dec(v_depth_583_);
v_res_589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_588_, v_keys_584_, v_vals_585_, v_i_586_, v_entries_587_);
lean_dec_ref(v_vals_585_);
lean_dec_ref(v_keys_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
size_t v_x_3646__boxed_595_; size_t v_x_3647__boxed_596_; lean_object* v_res_597_; 
v_x_3646__boxed_595_ = lean_unbox_usize(v_x_591_);
lean_dec(v_x_591_);
v_x_3647__boxed_596_ = lean_unbox_usize(v_x_592_);
lean_dec(v_x_592_);
v_res_597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_590_, v_x_3646__boxed_595_, v_x_3647__boxed_596_, v_x_593_, v_x_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
uint64_t v___x_601_; size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; 
v___x_601_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_599_);
v___x_602_ = lean_uint64_to_usize(v___x_601_);
v___x_603_ = ((size_t)1ULL);
v___x_604_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_598_, v___x_602_, v___x_603_, v_x_599_, v_x_600_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(lean_object* v_type_605_, lean_object* v_a_606_, lean_object* v_s_607_){
_start:
{
lean_object* v_rings_608_; lean_object* v_typeIdOf_609_; lean_object* v_exprToRingId_610_; lean_object* v_semirings_611_; lean_object* v_stypeIdOf_612_; lean_object* v_exprToSemiringId_613_; lean_object* v_ncRings_614_; lean_object* v_exprToNCRingId_615_; lean_object* v_nctypeIdOf_616_; lean_object* v_ncSemirings_617_; lean_object* v_exprToNCSemiringId_618_; lean_object* v_ncstypeIdOf_619_; lean_object* v_steps_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_628_; 
v_rings_608_ = lean_ctor_get(v_s_607_, 0);
v_typeIdOf_609_ = lean_ctor_get(v_s_607_, 1);
v_exprToRingId_610_ = lean_ctor_get(v_s_607_, 2);
v_semirings_611_ = lean_ctor_get(v_s_607_, 3);
v_stypeIdOf_612_ = lean_ctor_get(v_s_607_, 4);
v_exprToSemiringId_613_ = lean_ctor_get(v_s_607_, 5);
v_ncRings_614_ = lean_ctor_get(v_s_607_, 6);
v_exprToNCRingId_615_ = lean_ctor_get(v_s_607_, 7);
v_nctypeIdOf_616_ = lean_ctor_get(v_s_607_, 8);
v_ncSemirings_617_ = lean_ctor_get(v_s_607_, 9);
v_exprToNCSemiringId_618_ = lean_ctor_get(v_s_607_, 10);
v_ncstypeIdOf_619_ = lean_ctor_get(v_s_607_, 11);
v_steps_620_ = lean_ctor_get(v_s_607_, 12);
v_isSharedCheck_628_ = !lean_is_exclusive(v_s_607_);
if (v_isSharedCheck_628_ == 0)
{
v___x_622_ = v_s_607_;
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_steps_620_);
lean_inc(v_ncstypeIdOf_619_);
lean_inc(v_exprToNCSemiringId_618_);
lean_inc(v_ncSemirings_617_);
lean_inc(v_nctypeIdOf_616_);
lean_inc(v_exprToNCRingId_615_);
lean_inc(v_ncRings_614_);
lean_inc(v_exprToSemiringId_613_);
lean_inc(v_stypeIdOf_612_);
lean_inc(v_semirings_611_);
lean_inc(v_exprToRingId_610_);
lean_inc(v_typeIdOf_609_);
lean_inc(v_rings_608_);
lean_dec(v_s_607_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_624_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_typeIdOf_609_, v_type_605_, v_a_606_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_624_);
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_rings_608_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_exprToRingId_610_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_semirings_611_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_stypeIdOf_612_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v_exprToSemiringId_613_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_ncRings_614_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v_exprToNCRingId_615_);
lean_ctor_set(v_reuseFailAlloc_627_, 8, v_nctypeIdOf_616_);
lean_ctor_set(v_reuseFailAlloc_627_, 9, v_ncSemirings_617_);
lean_ctor_set(v_reuseFailAlloc_627_, 10, v_exprToNCSemiringId_618_);
lean_ctor_set(v_reuseFailAlloc_627_, 11, v_ncstypeIdOf_619_);
lean_ctor_set(v_reuseFailAlloc_627_, 12, v_steps_620_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_629_, lean_object* v_vals_630_, lean_object* v_i_631_, lean_object* v_k_632_){
_start:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_array_get_size(v_keys_629_);
v___x_634_ = lean_nat_dec_lt(v_i_631_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec(v_i_631_);
v___x_635_ = lean_box(0);
return v___x_635_;
}
else
{
lean_object* v_k_x27_636_; uint8_t v___x_637_; 
v_k_x27_636_ = lean_array_fget_borrowed(v_keys_629_, v_i_631_);
v___x_637_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_632_, v_k_x27_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_i_631_, v___x_638_);
lean_dec(v_i_631_);
v_i_631_ = v___x_639_;
goto _start;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_array_fget_borrowed(v_vals_630_, v_i_631_);
lean_dec(v_i_631_);
lean_inc(v___x_641_);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_643_, lean_object* v_vals_644_, lean_object* v_i_645_, lean_object* v_k_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_643_, v_vals_644_, v_i_645_, v_k_646_);
lean_dec_ref(v_k_646_);
lean_dec_ref(v_vals_644_);
lean_dec_ref(v_keys_643_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_648_, size_t v_x_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
lean_object* v_es_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_672_; 
v_es_651_ = lean_ctor_get(v_x_648_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_672_ == 0)
{
v___x_653_ = v_x_648_;
v_isShared_654_ = v_isSharedCheck_672_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_es_651_);
lean_dec(v_x_648_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_672_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; lean_object* v_j_659_; lean_object* v___x_660_; 
v___x_655_ = lean_box(2);
v___x_656_ = ((size_t)5ULL);
v___x_657_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
v___x_658_ = lean_usize_land(v_x_649_, v___x_657_);
v_j_659_ = lean_usize_to_nat(v___x_658_);
v___x_660_ = lean_array_get(v___x_655_, v_es_651_, v_j_659_);
lean_dec(v_j_659_);
lean_dec_ref(v_es_651_);
switch(lean_obj_tag(v___x_660_))
{
case 0:
{
lean_object* v_key_661_; lean_object* v_val_662_; uint8_t v___x_663_; 
v_key_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_key_661_);
v_val_662_ = lean_ctor_get(v___x_660_, 1);
lean_inc(v_val_662_);
lean_dec_ref(v___x_660_);
v___x_663_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_650_, v_key_661_);
lean_dec(v_key_661_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec(v_val_662_);
lean_del_object(v___x_653_);
v___x_664_ = lean_box(0);
return v___x_664_;
}
else
{
lean_object* v___x_666_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 1);
lean_ctor_set(v___x_653_, 0, v_val_662_);
v___x_666_ = v___x_653_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_val_662_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
case 1:
{
lean_object* v_node_668_; size_t v___x_669_; 
lean_del_object(v___x_653_);
v_node_668_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_node_668_);
lean_dec_ref(v___x_660_);
v___x_669_ = lean_usize_shift_right(v_x_649_, v___x_656_);
v_x_648_ = v_node_668_;
v_x_649_ = v___x_669_;
goto _start;
}
default: 
{
lean_object* v___x_671_; 
lean_del_object(v___x_653_);
v___x_671_ = lean_box(0);
return v___x_671_;
}
}
}
}
else
{
lean_object* v_ks_673_; lean_object* v_vs_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_ks_673_ = lean_ctor_get(v_x_648_, 0);
lean_inc_ref(v_ks_673_);
v_vs_674_ = lean_ctor_get(v_x_648_, 1);
lean_inc_ref(v_vs_674_);
lean_dec_ref(v_x_648_);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_673_, v_vs_674_, v___x_675_, v_x_650_);
lean_dec_ref(v_vs_674_);
lean_dec_ref(v_ks_673_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
size_t v_x_3864__boxed_680_; lean_object* v_res_681_; 
v_x_3864__boxed_680_ = lean_unbox_usize(v_x_678_);
lean_dec(v_x_678_);
v_res_681_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_677_, v_x_3864__boxed_680_, v_x_679_);
lean_dec_ref(v_x_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
uint64_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
v___x_684_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_683_);
v___x_685_ = lean_uint64_to_usize(v___x_684_);
v___x_686_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_682_, v___x_685_, v_x_683_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_687_, v_x_688_);
lean_dec_ref(v_x_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object* v_type_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_691_, v_a_699_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_734_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_734_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_734_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_734_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_typeIdOf_707_; lean_object* v___x_708_; 
v_typeIdOf_707_ = lean_ctor_get(v_a_703_, 1);
lean_inc_ref(v_typeIdOf_707_);
lean_dec(v_a_703_);
v___x_708_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_typeIdOf_707_, v_type_690_);
if (lean_obj_tag(v___x_708_) == 1)
{
lean_object* v_val_709_; lean_object* v___x_711_; 
lean_dec_ref(v_type_690_);
v_val_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_val_709_);
lean_dec_ref(v___x_708_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v_val_709_);
v___x_711_ = v___x_705_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_val_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
else
{
lean_object* v___x_713_; 
lean_dec(v___x_708_);
lean_del_object(v___x_705_);
lean_inc_ref(v_type_690_);
v___x_713_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc_n(v_a_714_, 2);
lean_dec_ref(v___x_713_);
v___f_715_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_715_, 0, v_type_690_);
lean_closure_set(v___f_715_, 1, v_a_714_);
v___x_716_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_717_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_716_, v___f_715_, v_a_691_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_725_);
v___x_719_ = v___x_717_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_dec(v___x_717_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v_a_714_);
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_714_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec(v_a_714_);
v_a_726_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_717_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_717_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_dec_ref(v_type_690_);
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v_type_690_);
v_a_735_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_702_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_702_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___boxed(lean_object* v_type_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec(v_a_744_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_757_, v_x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(v_00_u03b2_760_, v_x_761_, v_x_762_);
lean_dec_ref(v_x_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(lean_object* v_00_u03b2_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_x_765_, v_x_766_, v_x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_769_, lean_object* v_x_770_, size_t v_x_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_770_, v_x_771_, v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
size_t v_x_4038__boxed_778_; lean_object* v_res_779_; 
v_x_4038__boxed_778_ = lean_unbox_usize(v_x_776_);
lean_dec(v_x_776_);
v_res_779_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(v_00_u03b2_774_, v_x_775_, v_x_4038__boxed_778_, v_x_777_);
lean_dec_ref(v_x_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(lean_object* v_00_u03b2_780_, lean_object* v_x_781_, size_t v_x_782_, size_t v_x_783_, lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_781_, v_x_782_, v_x_783_, v_x_784_, v_x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
size_t v_x_4049__boxed_793_; size_t v_x_4050__boxed_794_; lean_object* v_res_795_; 
v_x_4049__boxed_793_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_x_4050__boxed_794_ = lean_unbox_usize(v_x_790_);
lean_dec(v_x_790_);
v_res_795_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(v_00_u03b2_787_, v_x_788_, v_x_4049__boxed_793_, v_x_4050__boxed_794_, v_x_791_, v_x_792_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_796_, lean_object* v_keys_797_, lean_object* v_vals_798_, lean_object* v_heq_799_, lean_object* v_i_800_, lean_object* v_k_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_797_, v_vals_798_, v_i_800_, v_k_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_803_, lean_object* v_keys_804_, lean_object* v_vals_805_, lean_object* v_heq_806_, lean_object* v_i_807_, lean_object* v_k_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_803_, v_keys_804_, v_vals_805_, v_heq_806_, v_i_807_, v_k_808_);
lean_dec_ref(v_k_808_);
lean_dec_ref(v_vals_805_);
lean_dec_ref(v_keys_804_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_810_, lean_object* v_n_811_, lean_object* v_k_812_, lean_object* v_v_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v_n_811_, v_k_812_, v_v_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_815_, size_t v_depth_816_, lean_object* v_keys_817_, lean_object* v_vals_818_, lean_object* v_heq_819_, lean_object* v_i_820_, lean_object* v_entries_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_816_, v_keys_817_, v_vals_818_, v_i_820_, v_entries_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_823_, lean_object* v_depth_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_heq_827_, lean_object* v_i_828_, lean_object* v_entries_829_){
_start:
{
size_t v_depth_boxed_830_; lean_object* v_res_831_; 
v_depth_boxed_830_ = lean_unbox_usize(v_depth_824_);
lean_dec(v_depth_824_);
v_res_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_823_, v_depth_boxed_830_, v_keys_825_, v_vals_826_, v_heq_827_, v_i_828_, v_entries_829_);
lean_dec_ref(v_vals_826_);
lean_dec_ref(v_keys_825_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_832_, lean_object* v_x_833_, lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_833_, v_x_834_, v_x_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(lean_object* v___x_838_, lean_object* v_s_839_){
_start:
{
lean_object* v_rings_840_; lean_object* v_typeIdOf_841_; lean_object* v_exprToRingId_842_; lean_object* v_semirings_843_; lean_object* v_stypeIdOf_844_; lean_object* v_exprToSemiringId_845_; lean_object* v_ncRings_846_; lean_object* v_exprToNCRingId_847_; lean_object* v_nctypeIdOf_848_; lean_object* v_ncSemirings_849_; lean_object* v_exprToNCSemiringId_850_; lean_object* v_ncstypeIdOf_851_; lean_object* v_steps_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_rings_840_ = lean_ctor_get(v_s_839_, 0);
v_typeIdOf_841_ = lean_ctor_get(v_s_839_, 1);
v_exprToRingId_842_ = lean_ctor_get(v_s_839_, 2);
v_semirings_843_ = lean_ctor_get(v_s_839_, 3);
v_stypeIdOf_844_ = lean_ctor_get(v_s_839_, 4);
v_exprToSemiringId_845_ = lean_ctor_get(v_s_839_, 5);
v_ncRings_846_ = lean_ctor_get(v_s_839_, 6);
v_exprToNCRingId_847_ = lean_ctor_get(v_s_839_, 7);
v_nctypeIdOf_848_ = lean_ctor_get(v_s_839_, 8);
v_ncSemirings_849_ = lean_ctor_get(v_s_839_, 9);
v_exprToNCSemiringId_850_ = lean_ctor_get(v_s_839_, 10);
v_ncstypeIdOf_851_ = lean_ctor_get(v_s_839_, 11);
v_steps_852_ = lean_ctor_get(v_s_839_, 12);
v_isSharedCheck_860_ = !lean_is_exclusive(v_s_839_);
if (v_isSharedCheck_860_ == 0)
{
v___x_854_ = v_s_839_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_steps_852_);
lean_inc(v_ncstypeIdOf_851_);
lean_inc(v_exprToNCSemiringId_850_);
lean_inc(v_ncSemirings_849_);
lean_inc(v_nctypeIdOf_848_);
lean_inc(v_exprToNCRingId_847_);
lean_inc(v_ncRings_846_);
lean_inc(v_exprToSemiringId_845_);
lean_inc(v_stypeIdOf_844_);
lean_inc(v_semirings_843_);
lean_inc(v_exprToRingId_842_);
lean_inc(v_typeIdOf_841_);
lean_inc(v_rings_840_);
lean_dec(v_s_839_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_array_push(v_ncRings_846_, v___x_838_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 6, v___x_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_rings_840_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_typeIdOf_841_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_exprToRingId_842_);
lean_ctor_set(v_reuseFailAlloc_859_, 3, v_semirings_843_);
lean_ctor_set(v_reuseFailAlloc_859_, 4, v_stypeIdOf_844_);
lean_ctor_set(v_reuseFailAlloc_859_, 5, v_exprToSemiringId_845_);
lean_ctor_set(v_reuseFailAlloc_859_, 6, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_859_, 7, v_exprToNCRingId_847_);
lean_ctor_set(v_reuseFailAlloc_859_, 8, v_nctypeIdOf_848_);
lean_ctor_set(v_reuseFailAlloc_859_, 9, v_ncSemirings_849_);
lean_ctor_set(v_reuseFailAlloc_859_, 10, v_exprToNCSemiringId_850_);
lean_ctor_set(v_reuseFailAlloc_859_, 11, v_ncstypeIdOf_851_);
lean_ctor_set(v_reuseFailAlloc_859_, 12, v_steps_852_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(lean_object* v_type_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___x_877_; 
lean_inc_ref(v_type_865_);
v___x_877_ = l_Lean_Meta_getDecLevel(v_type_865_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc_n(v_a_878_, 2);
lean_dec_ref(v___x_877_);
v___x_879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0));
v___x_880_ = lean_box(0);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v_a_878_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
lean_inc_ref(v___x_881_);
v___x_882_ = l_Lean_mkConst(v___x_879_, v___x_881_);
lean_inc_ref(v_type_865_);
v___x_883_ = l_Lean_Expr_app___override(v___x_882_, v_type_865_);
v___x_884_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_883_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_987_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_987_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_987_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_987_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
if (lean_obj_tag(v_a_885_) == 1)
{
lean_object* v_options_889_; lean_object* v_val_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_982_; 
lean_del_object(v___x_887_);
v_options_889_ = lean_ctor_get(v_a_874_, 2);
v_val_890_ = lean_ctor_get(v_a_885_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_a_885_);
if (v_isSharedCheck_982_ == 0)
{
v___x_892_ = v_a_885_;
v_isShared_893_ = v_isSharedCheck_982_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_val_890_);
lean_dec(v_a_885_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_982_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_inheritedTraceOptions_894_; uint8_t v_hasTrace_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; 
v_inheritedTraceOptions_894_ = lean_ctor_get(v_a_874_, 13);
v_hasTrace_895_ = lean_ctor_get_uint8(v_options_889_, sizeof(void*)*1);
v___x_896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8));
v___x_897_ = l_Lean_mkConst(v___x_896_, v___x_881_);
lean_inc(v_val_890_);
lean_inc_ref(v_type_865_);
v___x_898_ = l_Lean_mkAppB(v___x_897_, v_type_865_, v_val_890_);
if (v_hasTrace_895_ == 0)
{
v___y_900_ = v_a_866_;
v___y_901_ = v_a_867_;
v___y_902_ = v_a_868_;
v___y_903_ = v_a_869_;
v___y_904_ = v_a_870_;
v___y_905_ = v_a_871_;
v___y_906_ = v_a_872_;
v___y_907_ = v_a_873_;
v___y_908_ = v_a_874_;
v___y_909_ = v_a_875_;
goto v___jp_899_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20));
v___x_959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23);
v___x_960_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_894_, v_options_889_, v___x_959_);
if (v___x_960_ == 0)
{
v___y_900_ = v_a_866_;
v___y_901_ = v_a_867_;
v___y_902_ = v_a_868_;
v___y_903_ = v_a_869_;
v___y_904_ = v_a_870_;
v___y_905_ = v_a_871_;
v___y_906_ = v_a_872_;
v___y_907_ = v_a_873_;
v___y_908_ = v_a_874_;
v___y_909_ = v_a_875_;
goto v___jp_899_;
}
else
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_Grind_updateLastTag(v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec_ref(v___x_961_);
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
lean_inc_ref(v_type_865_);
v___x_963_ = l_Lean_MessageData_ofExpr(v_type_865_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_958_, v___x_964_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_dec_ref(v___x_965_);
v___y_900_ = v_a_866_;
v___y_901_ = v_a_867_;
v___y_902_ = v_a_868_;
v___y_903_ = v_a_869_;
v___y_904_ = v_a_870_;
v___y_905_ = v_a_871_;
v___y_906_ = v_a_872_;
v___y_907_ = v_a_873_;
v___y_908_ = v_a_874_;
v___y_909_ = v_a_875_;
goto v___jp_899_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec_ref(v___x_898_);
lean_del_object(v___x_892_);
lean_dec(v_val_890_);
lean_dec(v_a_878_);
lean_dec_ref(v_type_865_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v___x_898_);
lean_del_object(v___x_892_);
lean_dec(v_val_890_);
lean_dec(v_a_878_);
lean_dec_ref(v_type_865_);
v_a_974_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_961_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_961_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
v___jp_899_:
{
lean_object* v___x_910_; 
lean_inc_ref(v___x_898_);
lean_inc_ref(v_type_865_);
lean_inc(v_a_878_);
v___x_910_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_878_, v_type_865_, v___x_898_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref(v___x_910_);
v___x_912_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_900_, v___y_908_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v_ncRings_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___f_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref(v___x_912_);
v_ncRings_914_ = lean_ctor_get(v_a_913_, 6);
lean_inc_ref(v_ncRings_914_);
lean_dec(v_a_913_);
v___x_915_ = lean_array_get_size(v_ncRings_914_);
lean_dec_ref(v_ncRings_914_);
v___x_916_ = lean_box(0);
v___x_917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14);
v___x_918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16);
v___x_919_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_919_, 0, v___x_915_);
lean_ctor_set(v___x_919_, 1, v_type_865_);
lean_ctor_set(v___x_919_, 2, v_a_878_);
lean_ctor_set(v___x_919_, 3, v_val_890_);
lean_ctor_set(v___x_919_, 4, v___x_898_);
lean_ctor_set(v___x_919_, 5, v_a_911_);
lean_ctor_set(v___x_919_, 6, v___x_916_);
lean_ctor_set(v___x_919_, 7, v___x_916_);
lean_ctor_set(v___x_919_, 8, v___x_916_);
lean_ctor_set(v___x_919_, 9, v___x_916_);
lean_ctor_set(v___x_919_, 10, v___x_916_);
lean_ctor_set(v___x_919_, 11, v___x_916_);
lean_ctor_set(v___x_919_, 12, v___x_916_);
lean_ctor_set(v___x_919_, 13, v___x_916_);
lean_ctor_set(v___x_919_, 14, v___x_917_);
lean_ctor_set(v___x_919_, 15, v___x_918_);
lean_ctor_set(v___x_919_, 16, v___x_918_);
v___f_920_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_920_, 0, v___x_919_);
v___x_921_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_922_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_921_, v___f_920_, v___y_900_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_932_; 
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v___x_922_, 0);
lean_dec(v_unused_933_);
v___x_924_ = v___x_922_;
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
else
{
lean_dec(v___x_922_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_915_);
v___x_927_ = v___x_892_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_915_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_927_);
v___x_929_ = v___x_924_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_del_object(v___x_892_);
v_a_934_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_922_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_922_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_a_911_);
lean_dec_ref(v___x_898_);
lean_del_object(v___x_892_);
lean_dec(v_val_890_);
lean_dec(v_a_878_);
lean_dec_ref(v_type_865_);
v_a_942_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_912_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_912_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___x_898_);
lean_del_object(v___x_892_);
lean_dec(v_val_890_);
lean_dec(v_a_878_);
lean_dec_ref(v_type_865_);
v_a_950_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_910_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_910_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_985_; 
lean_dec(v_a_885_);
lean_dec_ref(v___x_881_);
lean_dec(v_a_878_);
lean_dec_ref(v_type_865_);
v___x_983_ = lean_box(0);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_983_);
v___x_985_ = v___x_887_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___x_881_);
lean_dec(v_a_878_);
lean_dec_ref(v_type_865_);
v_a_988_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_884_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_884_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v_type_865_);
v_a_996_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_877_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_877_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___boxed(lean_object* v_type_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec(v_a_1005_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(lean_object* v_type_1017_, lean_object* v_a_1018_, lean_object* v_s_1019_){
_start:
{
lean_object* v_rings_1020_; lean_object* v_typeIdOf_1021_; lean_object* v_exprToRingId_1022_; lean_object* v_semirings_1023_; lean_object* v_stypeIdOf_1024_; lean_object* v_exprToSemiringId_1025_; lean_object* v_ncRings_1026_; lean_object* v_exprToNCRingId_1027_; lean_object* v_nctypeIdOf_1028_; lean_object* v_ncSemirings_1029_; lean_object* v_exprToNCSemiringId_1030_; lean_object* v_ncstypeIdOf_1031_; lean_object* v_steps_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_rings_1020_ = lean_ctor_get(v_s_1019_, 0);
v_typeIdOf_1021_ = lean_ctor_get(v_s_1019_, 1);
v_exprToRingId_1022_ = lean_ctor_get(v_s_1019_, 2);
v_semirings_1023_ = lean_ctor_get(v_s_1019_, 3);
v_stypeIdOf_1024_ = lean_ctor_get(v_s_1019_, 4);
v_exprToSemiringId_1025_ = lean_ctor_get(v_s_1019_, 5);
v_ncRings_1026_ = lean_ctor_get(v_s_1019_, 6);
v_exprToNCRingId_1027_ = lean_ctor_get(v_s_1019_, 7);
v_nctypeIdOf_1028_ = lean_ctor_get(v_s_1019_, 8);
v_ncSemirings_1029_ = lean_ctor_get(v_s_1019_, 9);
v_exprToNCSemiringId_1030_ = lean_ctor_get(v_s_1019_, 10);
v_ncstypeIdOf_1031_ = lean_ctor_get(v_s_1019_, 11);
v_steps_1032_ = lean_ctor_get(v_s_1019_, 12);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_s_1019_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1034_ = v_s_1019_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_steps_1032_);
lean_inc(v_ncstypeIdOf_1031_);
lean_inc(v_exprToNCSemiringId_1030_);
lean_inc(v_ncSemirings_1029_);
lean_inc(v_nctypeIdOf_1028_);
lean_inc(v_exprToNCRingId_1027_);
lean_inc(v_ncRings_1026_);
lean_inc(v_exprToSemiringId_1025_);
lean_inc(v_stypeIdOf_1024_);
lean_inc(v_semirings_1023_);
lean_inc(v_exprToRingId_1022_);
lean_inc(v_typeIdOf_1021_);
lean_inc(v_rings_1020_);
lean_dec(v_s_1019_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_nctypeIdOf_1028_, v_type_1017_, v_a_1018_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 8, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_rings_1020_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_typeIdOf_1021_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_exprToRingId_1022_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_semirings_1023_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_stypeIdOf_1024_);
lean_ctor_set(v_reuseFailAlloc_1039_, 5, v_exprToSemiringId_1025_);
lean_ctor_set(v_reuseFailAlloc_1039_, 6, v_ncRings_1026_);
lean_ctor_set(v_reuseFailAlloc_1039_, 7, v_exprToNCRingId_1027_);
lean_ctor_set(v_reuseFailAlloc_1039_, 8, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 9, v_ncSemirings_1029_);
lean_ctor_set(v_reuseFailAlloc_1039_, 10, v_exprToNCSemiringId_1030_);
lean_ctor_set(v_reuseFailAlloc_1039_, 11, v_ncstypeIdOf_1031_);
lean_ctor_set(v_reuseFailAlloc_1039_, 12, v_steps_1032_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object* v_type_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1042_, v_a_1050_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1085_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1085_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1085_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_nctypeIdOf_1058_; lean_object* v___x_1059_; 
v_nctypeIdOf_1058_ = lean_ctor_get(v_a_1054_, 8);
lean_inc_ref(v_nctypeIdOf_1058_);
lean_dec(v_a_1054_);
v___x_1059_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_nctypeIdOf_1058_, v_type_1041_);
if (lean_obj_tag(v___x_1059_) == 1)
{
lean_object* v_val_1060_; lean_object* v___x_1062_; 
lean_dec_ref(v_type_1041_);
v_val_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_val_1060_);
lean_dec_ref(v___x_1059_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v_val_1060_);
v___x_1062_ = v___x_1056_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_val_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v___x_1064_; 
lean_dec(v___x_1059_);
lean_del_object(v___x_1056_);
lean_inc_ref(v_type_1041_);
v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___f_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_n(v_a_1065_, 2);
lean_dec_ref(v___x_1064_);
v___f_1066_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1066_, 0, v_type_1041_);
lean_closure_set(v___f_1066_, 1, v_a_1065_);
v___x_1067_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1068_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1067_, v___f_1066_, v_a_1042_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___x_1068_, 0);
lean_dec(v_unused_1076_);
v___x_1070_ = v___x_1068_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_dec(v___x_1068_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v_a_1065_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1065_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec(v_a_1065_);
v_a_1077_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1068_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1068_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_dec_ref(v_type_1041_);
return v___x_1064_;
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v_type_1041_);
v_a_1086_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1053_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1053_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___boxed(lean_object* v_type_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec(v_a_1095_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(lean_object* v_semiringId_1107_, lean_object* v_s_1108_){
_start:
{
lean_object* v_toRing_1109_; lean_object* v_invFn_x3f_1110_; lean_object* v_commSemiringInst_1111_; lean_object* v_commRingInst_1112_; lean_object* v_noZeroDivInst_x3f_1113_; lean_object* v_fieldInst_x3f_1114_; lean_object* v_denoteEntries_1115_; lean_object* v_nextId_1116_; lean_object* v_steps_1117_; lean_object* v_queue_1118_; lean_object* v_basis_1119_; lean_object* v_diseqs_1120_; uint8_t v_recheck_1121_; lean_object* v_invSet_1122_; lean_object* v_numEq0_x3f_1123_; uint8_t v_numEq0Updated_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1132_; 
v_toRing_1109_ = lean_ctor_get(v_s_1108_, 0);
v_invFn_x3f_1110_ = lean_ctor_get(v_s_1108_, 1);
v_commSemiringInst_1111_ = lean_ctor_get(v_s_1108_, 3);
v_commRingInst_1112_ = lean_ctor_get(v_s_1108_, 4);
v_noZeroDivInst_x3f_1113_ = lean_ctor_get(v_s_1108_, 5);
v_fieldInst_x3f_1114_ = lean_ctor_get(v_s_1108_, 6);
v_denoteEntries_1115_ = lean_ctor_get(v_s_1108_, 7);
v_nextId_1116_ = lean_ctor_get(v_s_1108_, 8);
v_steps_1117_ = lean_ctor_get(v_s_1108_, 9);
v_queue_1118_ = lean_ctor_get(v_s_1108_, 10);
v_basis_1119_ = lean_ctor_get(v_s_1108_, 11);
v_diseqs_1120_ = lean_ctor_get(v_s_1108_, 12);
v_recheck_1121_ = lean_ctor_get_uint8(v_s_1108_, sizeof(void*)*15);
v_invSet_1122_ = lean_ctor_get(v_s_1108_, 13);
v_numEq0_x3f_1123_ = lean_ctor_get(v_s_1108_, 14);
v_numEq0Updated_1124_ = lean_ctor_get_uint8(v_s_1108_, sizeof(void*)*15 + 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_s_1108_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v_s_1108_, 2);
lean_dec(v_unused_1133_);
v___x_1126_ = v_s_1108_;
v_isShared_1127_ = v_isSharedCheck_1132_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_numEq0_x3f_1123_);
lean_inc(v_invSet_1122_);
lean_inc(v_diseqs_1120_);
lean_inc(v_basis_1119_);
lean_inc(v_queue_1118_);
lean_inc(v_steps_1117_);
lean_inc(v_nextId_1116_);
lean_inc(v_denoteEntries_1115_);
lean_inc(v_fieldInst_x3f_1114_);
lean_inc(v_noZeroDivInst_x3f_1113_);
lean_inc(v_commRingInst_1112_);
lean_inc(v_commSemiringInst_1111_);
lean_inc(v_invFn_x3f_1110_);
lean_inc(v_toRing_1109_);
lean_dec(v_s_1108_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1132_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_semiringId_1107_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 2, v___x_1128_);
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_toRing_1109_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_invFn_x3f_1110_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_commSemiringInst_1111_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_commRingInst_1112_);
lean_ctor_set(v_reuseFailAlloc_1131_, 5, v_noZeroDivInst_x3f_1113_);
lean_ctor_set(v_reuseFailAlloc_1131_, 6, v_fieldInst_x3f_1114_);
lean_ctor_set(v_reuseFailAlloc_1131_, 7, v_denoteEntries_1115_);
lean_ctor_set(v_reuseFailAlloc_1131_, 8, v_nextId_1116_);
lean_ctor_set(v_reuseFailAlloc_1131_, 9, v_steps_1117_);
lean_ctor_set(v_reuseFailAlloc_1131_, 10, v_queue_1118_);
lean_ctor_set(v_reuseFailAlloc_1131_, 11, v_basis_1119_);
lean_ctor_set(v_reuseFailAlloc_1131_, 12, v_diseqs_1120_);
lean_ctor_set(v_reuseFailAlloc_1131_, 13, v_invSet_1122_);
lean_ctor_set(v_reuseFailAlloc_1131_, 14, v_numEq0_x3f_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1131_, sizeof(void*)*15, v_recheck_1121_);
lean_ctor_set_uint8(v_reuseFailAlloc_1131_, sizeof(void*)*15 + 1, v_numEq0Updated_1124_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(lean_object* v_ringId_1134_, lean_object* v_semiringId_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___f_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___f_1138_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1138_, 0, v_semiringId_1135_);
v___x_1139_ = 0;
v___x_1140_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1140_, 0, v_ringId_1134_);
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*1, v___x_1139_);
v___x_1141_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1138_, v___x_1140_, v_a_1136_);
lean_dec_ref(v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(lean_object* v_ringId_1142_, lean_object* v_semiringId_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_1142_, v_semiringId_1143_, v_a_1144_);
lean_dec(v_a_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(lean_object* v_ringId_1147_, lean_object* v_semiringId_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_1147_, v_semiringId_1148_, v_a_1149_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(lean_object* v_ringId_1161_, lean_object* v_semiringId_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(v_ringId_1161_, v_semiringId_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec(v_a_1163_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(lean_object* v___x_1175_, lean_object* v_s_1176_){
_start:
{
lean_object* v_rings_1177_; lean_object* v_typeIdOf_1178_; lean_object* v_exprToRingId_1179_; lean_object* v_semirings_1180_; lean_object* v_stypeIdOf_1181_; lean_object* v_exprToSemiringId_1182_; lean_object* v_ncRings_1183_; lean_object* v_exprToNCRingId_1184_; lean_object* v_nctypeIdOf_1185_; lean_object* v_ncSemirings_1186_; lean_object* v_exprToNCSemiringId_1187_; lean_object* v_ncstypeIdOf_1188_; lean_object* v_steps_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1197_; 
v_rings_1177_ = lean_ctor_get(v_s_1176_, 0);
v_typeIdOf_1178_ = lean_ctor_get(v_s_1176_, 1);
v_exprToRingId_1179_ = lean_ctor_get(v_s_1176_, 2);
v_semirings_1180_ = lean_ctor_get(v_s_1176_, 3);
v_stypeIdOf_1181_ = lean_ctor_get(v_s_1176_, 4);
v_exprToSemiringId_1182_ = lean_ctor_get(v_s_1176_, 5);
v_ncRings_1183_ = lean_ctor_get(v_s_1176_, 6);
v_exprToNCRingId_1184_ = lean_ctor_get(v_s_1176_, 7);
v_nctypeIdOf_1185_ = lean_ctor_get(v_s_1176_, 8);
v_ncSemirings_1186_ = lean_ctor_get(v_s_1176_, 9);
v_exprToNCSemiringId_1187_ = lean_ctor_get(v_s_1176_, 10);
v_ncstypeIdOf_1188_ = lean_ctor_get(v_s_1176_, 11);
v_steps_1189_ = lean_ctor_get(v_s_1176_, 12);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_s_1176_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1191_ = v_s_1176_;
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_steps_1189_);
lean_inc(v_ncstypeIdOf_1188_);
lean_inc(v_exprToNCSemiringId_1187_);
lean_inc(v_ncSemirings_1186_);
lean_inc(v_nctypeIdOf_1185_);
lean_inc(v_exprToNCRingId_1184_);
lean_inc(v_ncRings_1183_);
lean_inc(v_exprToSemiringId_1182_);
lean_inc(v_stypeIdOf_1181_);
lean_inc(v_semirings_1180_);
lean_inc(v_exprToRingId_1179_);
lean_inc(v_typeIdOf_1178_);
lean_inc(v_rings_1177_);
lean_dec(v_s_1176_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1193_ = lean_array_push(v_semirings_1180_, v___x_1175_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 3, v___x_1193_);
v___x_1195_ = v___x_1191_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_rings_1177_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_typeIdOf_1178_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_exprToRingId_1179_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_stypeIdOf_1181_);
lean_ctor_set(v_reuseFailAlloc_1196_, 5, v_exprToSemiringId_1182_);
lean_ctor_set(v_reuseFailAlloc_1196_, 6, v_ncRings_1183_);
lean_ctor_set(v_reuseFailAlloc_1196_, 7, v_exprToNCRingId_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 8, v_nctypeIdOf_1185_);
lean_ctor_set(v_reuseFailAlloc_1196_, 9, v_ncSemirings_1186_);
lean_ctor_set(v_reuseFailAlloc_1196_, 10, v_exprToNCSemiringId_1187_);
lean_ctor_set(v_reuseFailAlloc_1196_, 11, v_ncstypeIdOf_1188_);
lean_ctor_set(v_reuseFailAlloc_1196_, 12, v_steps_1189_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_ref_1204_; lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_ref_1204_ = lean_ctor_get(v___y_1201_, 5);
v___x_1205_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_inc(v_ref_1204_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_ref_1204_);
lean_ctor_set(v___x_1210_, 1, v_a_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 1);
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8));
v___x_1245_ = l_Lean_stringToMessageData(v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(lean_object* v_type_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___x_1258_; 
lean_inc_ref(v_type_1246_);
v___x_1258_ = l_Lean_Meta_getDecLevel(v_type_1246_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc_n(v_a_1259_, 2);
lean_dec_ref(v___x_1258_);
v___x_1260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1));
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_a_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_inc_ref(v___x_1262_);
v___x_1263_ = l_Lean_mkConst(v___x_1260_, v___x_1262_);
lean_inc_ref(v_type_1246_);
v___x_1264_ = l_Lean_Expr_app___override(v___x_1263_, v_type_1246_);
v___x_1265_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1264_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1360_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1360_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1360_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
if (lean_obj_tag(v_a_1266_) == 1)
{
lean_object* v_val_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_del_object(v___x_1268_);
v_val_1270_ = lean_ctor_get(v_a_1266_, 0);
lean_inc_n(v_val_1270_, 2);
lean_dec_ref(v_a_1266_);
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2));
lean_inc_ref(v___x_1262_);
v___x_1272_ = l_Lean_mkConst(v___x_1271_, v___x_1262_);
lean_inc_ref_n(v_type_1246_, 2);
v___x_1273_ = l_Lean_mkAppB(v___x_1272_, v_type_1246_, v_val_1270_);
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5));
v___x_1275_ = l_Lean_mkConst(v___x_1274_, v___x_1262_);
lean_inc_ref(v___x_1273_);
v___x_1276_ = l_Lean_mkAppB(v___x_1275_, v_type_1246_, v___x_1273_);
v___x_1277_ = l_Lean_Meta_Sym_canon(v___x_1276_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1278_, v_a_1252_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc_n(v_a_1280_, 2);
lean_dec_ref(v___x_1279_);
v___x_1281_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_a_1280_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref(v___x_1281_);
if (lean_obj_tag(v_a_1282_) == 1)
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_a_1280_);
v_val_1283_ = lean_ctor_get(v_a_1282_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_a_1282_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1285_ = v_a_1282_;
v_isShared_1286_ = v_isSharedCheck_1335_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v_a_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1335_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1247_, v_a_1255_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_semirings_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref(v___x_1287_);
v_semirings_1289_ = lean_ctor_get(v_a_1288_, 3);
lean_inc_ref(v_semirings_1289_);
lean_dec(v_a_1288_);
v___x_1290_ = lean_array_get_size(v_semirings_1289_);
lean_dec_ref(v_semirings_1289_);
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
v___x_1293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14);
v___x_1294_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1290_);
lean_ctor_set(v___x_1294_, 1, v_type_1246_);
lean_ctor_set(v___x_1294_, 2, v_a_1259_);
lean_ctor_set(v___x_1294_, 3, v___x_1273_);
lean_ctor_set(v___x_1294_, 4, v___x_1291_);
lean_ctor_set(v___x_1294_, 5, v___x_1291_);
lean_ctor_set(v___x_1294_, 6, v___x_1291_);
lean_ctor_set(v___x_1294_, 7, v___x_1291_);
lean_ctor_set(v___x_1294_, 8, v___x_1292_);
lean_ctor_set(v___x_1294_, 9, v___x_1293_);
lean_ctor_set(v___x_1294_, 10, v___x_1292_);
lean_inc(v_val_1283_);
v___x_1295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v_val_1283_);
lean_ctor_set(v___x_1295_, 2, v_val_1270_);
lean_ctor_set(v___x_1295_, 3, v___x_1291_);
lean_ctor_set(v___x_1295_, 4, v___x_1291_);
v___f_1296_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1296_, 0, v___x_1295_);
v___x_1297_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1298_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1297_, v___f_1296_, v_a_1247_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v___x_1299_; 
lean_dec_ref(v___x_1298_);
v___x_1299_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_val_1283_, v___x_1290_, v_a_1247_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1309_; 
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v___x_1299_, 0);
lean_dec(v_unused_1310_);
v___x_1301_ = v___x_1299_;
v_isShared_1302_ = v_isSharedCheck_1309_;
goto v_resetjp_1300_;
}
else
{
lean_dec(v___x_1299_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1309_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1290_);
v___x_1304_ = v___x_1285_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1290_);
v___x_1304_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1304_);
v___x_1306_ = v___x_1301_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_del_object(v___x_1285_);
v_a_1311_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1299_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1299_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_del_object(v___x_1285_);
lean_dec(v_val_1283_);
v_a_1319_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1298_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1298_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_del_object(v___x_1285_);
lean_dec(v_val_1283_);
lean_dec_ref(v___x_1273_);
lean_dec(v_val_1270_);
lean_dec(v_a_1259_);
lean_dec_ref(v_type_1246_);
v_a_1327_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1287_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1287_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec(v_a_1282_);
lean_dec_ref(v___x_1273_);
lean_dec(v_val_1270_);
lean_dec(v_a_1259_);
lean_dec_ref(v_type_1246_);
v___x_1336_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9);
v___x_1337_ = l_Lean_indentExpr(v_a_1280_);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v___x_1338_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
return v___x_1339_;
}
}
else
{
lean_dec(v_a_1280_);
lean_dec_ref(v___x_1273_);
lean_dec(v_val_1270_);
lean_dec(v_a_1259_);
lean_dec_ref(v_type_1246_);
return v___x_1281_;
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec_ref(v___x_1273_);
lean_dec(v_val_1270_);
lean_dec(v_a_1259_);
lean_dec_ref(v_type_1246_);
v_a_1340_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1279_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1279_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec_ref(v___x_1273_);
lean_dec(v_val_1270_);
lean_dec(v_a_1259_);
lean_dec_ref(v_type_1246_);
v_a_1348_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1277_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1277_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_dec(v_a_1266_);
lean_dec_ref(v___x_1262_);
lean_dec(v_a_1259_);
lean_dec_ref(v_type_1246_);
v___x_1356_ = lean_box(0);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1356_);
v___x_1358_ = v___x_1268_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v___x_1262_);
lean_dec(v_a_1259_);
lean_dec_ref(v_type_1246_);
v_a_1361_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1265_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1265_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_type_1246_);
v_a_1369_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1258_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1258_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec(v_a_1378_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_1390_, lean_object* v_msg_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_1391_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(v_00_u03b1_1404_, v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec(v___y_1406_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(lean_object* v_type_1418_, lean_object* v_a_1419_, lean_object* v_s_1420_){
_start:
{
lean_object* v_rings_1421_; lean_object* v_typeIdOf_1422_; lean_object* v_exprToRingId_1423_; lean_object* v_semirings_1424_; lean_object* v_stypeIdOf_1425_; lean_object* v_exprToSemiringId_1426_; lean_object* v_ncRings_1427_; lean_object* v_exprToNCRingId_1428_; lean_object* v_nctypeIdOf_1429_; lean_object* v_ncSemirings_1430_; lean_object* v_exprToNCSemiringId_1431_; lean_object* v_ncstypeIdOf_1432_; lean_object* v_steps_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1441_; 
v_rings_1421_ = lean_ctor_get(v_s_1420_, 0);
v_typeIdOf_1422_ = lean_ctor_get(v_s_1420_, 1);
v_exprToRingId_1423_ = lean_ctor_get(v_s_1420_, 2);
v_semirings_1424_ = lean_ctor_get(v_s_1420_, 3);
v_stypeIdOf_1425_ = lean_ctor_get(v_s_1420_, 4);
v_exprToSemiringId_1426_ = lean_ctor_get(v_s_1420_, 5);
v_ncRings_1427_ = lean_ctor_get(v_s_1420_, 6);
v_exprToNCRingId_1428_ = lean_ctor_get(v_s_1420_, 7);
v_nctypeIdOf_1429_ = lean_ctor_get(v_s_1420_, 8);
v_ncSemirings_1430_ = lean_ctor_get(v_s_1420_, 9);
v_exprToNCSemiringId_1431_ = lean_ctor_get(v_s_1420_, 10);
v_ncstypeIdOf_1432_ = lean_ctor_get(v_s_1420_, 11);
v_steps_1433_ = lean_ctor_get(v_s_1420_, 12);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_s_1420_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1435_ = v_s_1420_;
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_steps_1433_);
lean_inc(v_ncstypeIdOf_1432_);
lean_inc(v_exprToNCSemiringId_1431_);
lean_inc(v_ncSemirings_1430_);
lean_inc(v_nctypeIdOf_1429_);
lean_inc(v_exprToNCRingId_1428_);
lean_inc(v_ncRings_1427_);
lean_inc(v_exprToSemiringId_1426_);
lean_inc(v_stypeIdOf_1425_);
lean_inc(v_semirings_1424_);
lean_inc(v_exprToRingId_1423_);
lean_inc(v_typeIdOf_1422_);
lean_inc(v_rings_1421_);
lean_dec(v_s_1420_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1437_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_stypeIdOf_1425_, v_type_1418_, v_a_1419_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1437_);
v___x_1439_ = v___x_1435_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_rings_1421_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_typeIdOf_1422_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_exprToRingId_1423_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_semirings_1424_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1440_, 5, v_exprToSemiringId_1426_);
lean_ctor_set(v_reuseFailAlloc_1440_, 6, v_ncRings_1427_);
lean_ctor_set(v_reuseFailAlloc_1440_, 7, v_exprToNCRingId_1428_);
lean_ctor_set(v_reuseFailAlloc_1440_, 8, v_nctypeIdOf_1429_);
lean_ctor_set(v_reuseFailAlloc_1440_, 9, v_ncSemirings_1430_);
lean_ctor_set(v_reuseFailAlloc_1440_, 10, v_exprToNCSemiringId_1431_);
lean_ctor_set(v_reuseFailAlloc_1440_, 11, v_ncstypeIdOf_1432_);
lean_ctor_set(v_reuseFailAlloc_1440_, 12, v_steps_1433_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object* v_type_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1443_, v_a_1451_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1486_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1486_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1486_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_stypeIdOf_1459_; lean_object* v___x_1460_; 
v_stypeIdOf_1459_ = lean_ctor_get(v_a_1455_, 4);
lean_inc_ref(v_stypeIdOf_1459_);
lean_dec(v_a_1455_);
v___x_1460_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_stypeIdOf_1459_, v_type_1442_);
if (lean_obj_tag(v___x_1460_) == 1)
{
lean_object* v_val_1461_; lean_object* v___x_1463_; 
lean_dec_ref(v_type_1442_);
v_val_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_val_1461_);
lean_dec_ref(v___x_1460_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v_val_1461_);
v___x_1463_ = v___x_1457_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_val_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
else
{
lean_object* v___x_1465_; 
lean_dec(v___x_1460_);
lean_del_object(v___x_1457_);
lean_inc_ref(v_type_1442_);
v___x_1465_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___f_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc_n(v_a_1466_, 2);
lean_dec_ref(v___x_1465_);
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1467_, 0, v_type_1442_);
lean_closure_set(v___f_1467_, 1, v_a_1466_);
v___x_1468_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1469_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1468_, v___f_1467_, v_a_1443_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v___x_1469_, 0);
lean_dec(v_unused_1477_);
v___x_1471_ = v___x_1469_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v___x_1469_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_a_1466_);
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1466_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_a_1466_);
v_a_1478_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1469_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1469_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_dec_ref(v_type_1442_);
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_type_1442_);
v_a_1487_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1454_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1454_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___boxed(lean_object* v_type_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_type_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec(v_a_1496_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(lean_object* v___x_1508_, lean_object* v_s_1509_){
_start:
{
lean_object* v_rings_1510_; lean_object* v_typeIdOf_1511_; lean_object* v_exprToRingId_1512_; lean_object* v_semirings_1513_; lean_object* v_stypeIdOf_1514_; lean_object* v_exprToSemiringId_1515_; lean_object* v_ncRings_1516_; lean_object* v_exprToNCRingId_1517_; lean_object* v_nctypeIdOf_1518_; lean_object* v_ncSemirings_1519_; lean_object* v_exprToNCSemiringId_1520_; lean_object* v_ncstypeIdOf_1521_; lean_object* v_steps_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1530_; 
v_rings_1510_ = lean_ctor_get(v_s_1509_, 0);
v_typeIdOf_1511_ = lean_ctor_get(v_s_1509_, 1);
v_exprToRingId_1512_ = lean_ctor_get(v_s_1509_, 2);
v_semirings_1513_ = lean_ctor_get(v_s_1509_, 3);
v_stypeIdOf_1514_ = lean_ctor_get(v_s_1509_, 4);
v_exprToSemiringId_1515_ = lean_ctor_get(v_s_1509_, 5);
v_ncRings_1516_ = lean_ctor_get(v_s_1509_, 6);
v_exprToNCRingId_1517_ = lean_ctor_get(v_s_1509_, 7);
v_nctypeIdOf_1518_ = lean_ctor_get(v_s_1509_, 8);
v_ncSemirings_1519_ = lean_ctor_get(v_s_1509_, 9);
v_exprToNCSemiringId_1520_ = lean_ctor_get(v_s_1509_, 10);
v_ncstypeIdOf_1521_ = lean_ctor_get(v_s_1509_, 11);
v_steps_1522_ = lean_ctor_get(v_s_1509_, 12);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_s_1509_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1524_ = v_s_1509_;
v_isShared_1525_ = v_isSharedCheck_1530_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_steps_1522_);
lean_inc(v_ncstypeIdOf_1521_);
lean_inc(v_exprToNCSemiringId_1520_);
lean_inc(v_ncSemirings_1519_);
lean_inc(v_nctypeIdOf_1518_);
lean_inc(v_exprToNCRingId_1517_);
lean_inc(v_ncRings_1516_);
lean_inc(v_exprToSemiringId_1515_);
lean_inc(v_stypeIdOf_1514_);
lean_inc(v_semirings_1513_);
lean_inc(v_exprToRingId_1512_);
lean_inc(v_typeIdOf_1511_);
lean_inc(v_rings_1510_);
lean_dec(v_s_1509_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1530_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = lean_array_push(v_ncSemirings_1519_, v___x_1508_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 9, v___x_1526_);
v___x_1528_ = v___x_1524_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_rings_1510_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_typeIdOf_1511_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_exprToRingId_1512_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_semirings_1513_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_stypeIdOf_1514_);
lean_ctor_set(v_reuseFailAlloc_1529_, 5, v_exprToSemiringId_1515_);
lean_ctor_set(v_reuseFailAlloc_1529_, 6, v_ncRings_1516_);
lean_ctor_set(v_reuseFailAlloc_1529_, 7, v_exprToNCRingId_1517_);
lean_ctor_set(v_reuseFailAlloc_1529_, 8, v_nctypeIdOf_1518_);
lean_ctor_set(v_reuseFailAlloc_1529_, 9, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1529_, 10, v_exprToNCSemiringId_1520_);
lean_ctor_set(v_reuseFailAlloc_1529_, 11, v_ncstypeIdOf_1521_);
lean_ctor_set(v_reuseFailAlloc_1529_, 12, v_steps_1522_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(lean_object* v_type_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1543_; 
lean_inc_ref(v_type_1536_);
v___x_1543_ = l_Lean_Meta_getDecLevel(v_type_1536_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc_n(v_a_1544_, 2);
lean_dec_ref(v___x_1543_);
v___x_1545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1));
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_a_1544_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_mkConst(v___x_1545_, v___x_1547_);
lean_inc_ref(v_type_1536_);
v___x_1549_ = l_Lean_Expr_app___override(v___x_1548_, v_type_1536_);
v___x_1550_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1549_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1602_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1602_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1602_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
if (lean_obj_tag(v_a_1551_) == 1)
{
lean_object* v_val_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1597_; 
lean_del_object(v___x_1553_);
v_val_1555_ = lean_ctor_get(v_a_1551_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_a_1551_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1557_ = v_a_1551_;
v_isShared_1558_ = v_isSharedCheck_1597_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_val_1555_);
lean_dec(v_a_1551_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1597_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1537_, v_a_1540_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v_ncSemirings_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1559_);
v_ncSemirings_1561_ = lean_ctor_get(v_a_1560_, 9);
lean_inc_ref(v_ncSemirings_1561_);
lean_dec(v_a_1560_);
v___x_1562_ = lean_array_get_size(v_ncSemirings_1561_);
lean_dec_ref(v_ncSemirings_1561_);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
v___x_1565_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14);
v___x_1566_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1562_);
lean_ctor_set(v___x_1566_, 1, v_type_1536_);
lean_ctor_set(v___x_1566_, 2, v_a_1544_);
lean_ctor_set(v___x_1566_, 3, v_val_1555_);
lean_ctor_set(v___x_1566_, 4, v___x_1563_);
lean_ctor_set(v___x_1566_, 5, v___x_1563_);
lean_ctor_set(v___x_1566_, 6, v___x_1563_);
lean_ctor_set(v___x_1566_, 7, v___x_1563_);
lean_ctor_set(v___x_1566_, 8, v___x_1564_);
lean_ctor_set(v___x_1566_, 9, v___x_1565_);
lean_ctor_set(v___x_1566_, 10, v___x_1564_);
v___f_1567_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1567_, 0, v___x_1566_);
v___x_1568_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1569_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1568_, v___f_1567_, v_a_1537_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1579_; 
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v___x_1569_, 0);
lean_dec(v_unused_1580_);
v___x_1571_ = v___x_1569_;
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v___x_1569_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1562_);
v___x_1574_ = v___x_1557_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1562_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_del_object(v___x_1557_);
v_a_1581_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1569_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1569_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_del_object(v___x_1557_);
lean_dec(v_val_1555_);
lean_dec(v_a_1544_);
lean_dec_ref(v_type_1536_);
v_a_1589_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1559_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1559_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
lean_dec(v_a_1551_);
lean_dec(v_a_1544_);
lean_dec_ref(v_type_1536_);
v___x_1598_ = lean_box(0);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1598_);
v___x_1600_ = v___x_1553_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_a_1544_);
lean_dec_ref(v_type_1536_);
v_a_1603_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1550_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1550_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_type_1536_);
v_a_1611_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1543_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1543_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___boxed(lean_object* v_type_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(lean_object* v_type_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_1627_, v_a_1628_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(v_type_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec(v_a_1641_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(lean_object* v_type_1653_, lean_object* v_a_1654_, lean_object* v_s_1655_){
_start:
{
lean_object* v_rings_1656_; lean_object* v_typeIdOf_1657_; lean_object* v_exprToRingId_1658_; lean_object* v_semirings_1659_; lean_object* v_stypeIdOf_1660_; lean_object* v_exprToSemiringId_1661_; lean_object* v_ncRings_1662_; lean_object* v_exprToNCRingId_1663_; lean_object* v_nctypeIdOf_1664_; lean_object* v_ncSemirings_1665_; lean_object* v_exprToNCSemiringId_1666_; lean_object* v_ncstypeIdOf_1667_; lean_object* v_steps_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1676_; 
v_rings_1656_ = lean_ctor_get(v_s_1655_, 0);
v_typeIdOf_1657_ = lean_ctor_get(v_s_1655_, 1);
v_exprToRingId_1658_ = lean_ctor_get(v_s_1655_, 2);
v_semirings_1659_ = lean_ctor_get(v_s_1655_, 3);
v_stypeIdOf_1660_ = lean_ctor_get(v_s_1655_, 4);
v_exprToSemiringId_1661_ = lean_ctor_get(v_s_1655_, 5);
v_ncRings_1662_ = lean_ctor_get(v_s_1655_, 6);
v_exprToNCRingId_1663_ = lean_ctor_get(v_s_1655_, 7);
v_nctypeIdOf_1664_ = lean_ctor_get(v_s_1655_, 8);
v_ncSemirings_1665_ = lean_ctor_get(v_s_1655_, 9);
v_exprToNCSemiringId_1666_ = lean_ctor_get(v_s_1655_, 10);
v_ncstypeIdOf_1667_ = lean_ctor_get(v_s_1655_, 11);
v_steps_1668_ = lean_ctor_get(v_s_1655_, 12);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_s_1655_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1670_ = v_s_1655_;
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_steps_1668_);
lean_inc(v_ncstypeIdOf_1667_);
lean_inc(v_exprToNCSemiringId_1666_);
lean_inc(v_ncSemirings_1665_);
lean_inc(v_nctypeIdOf_1664_);
lean_inc(v_exprToNCRingId_1663_);
lean_inc(v_ncRings_1662_);
lean_inc(v_exprToSemiringId_1661_);
lean_inc(v_stypeIdOf_1660_);
lean_inc(v_semirings_1659_);
lean_inc(v_exprToRingId_1658_);
lean_inc(v_typeIdOf_1657_);
lean_inc(v_rings_1656_);
lean_dec(v_s_1655_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_ncstypeIdOf_1667_, v_type_1653_, v_a_1654_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 11, v___x_1672_);
v___x_1674_ = v___x_1670_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_rings_1656_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_typeIdOf_1657_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_exprToRingId_1658_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_semirings_1659_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v_stypeIdOf_1660_);
lean_ctor_set(v_reuseFailAlloc_1675_, 5, v_exprToSemiringId_1661_);
lean_ctor_set(v_reuseFailAlloc_1675_, 6, v_ncRings_1662_);
lean_ctor_set(v_reuseFailAlloc_1675_, 7, v_exprToNCRingId_1663_);
lean_ctor_set(v_reuseFailAlloc_1675_, 8, v_nctypeIdOf_1664_);
lean_ctor_set(v_reuseFailAlloc_1675_, 9, v_ncSemirings_1665_);
lean_ctor_set(v_reuseFailAlloc_1675_, 10, v_exprToNCSemiringId_1666_);
lean_ctor_set(v_reuseFailAlloc_1675_, 11, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1675_, 12, v_steps_1668_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object* v_type_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1678_, v_a_1681_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1716_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1716_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1716_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_ncstypeIdOf_1689_; lean_object* v___x_1690_; 
v_ncstypeIdOf_1689_ = lean_ctor_get(v_a_1685_, 11);
lean_inc_ref(v_ncstypeIdOf_1689_);
lean_dec(v_a_1685_);
v___x_1690_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_ncstypeIdOf_1689_, v_type_1677_);
if (lean_obj_tag(v___x_1690_) == 1)
{
lean_object* v_val_1691_; lean_object* v___x_1693_; 
lean_dec_ref(v_type_1677_);
v_val_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1691_);
lean_dec_ref(v___x_1690_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v_val_1691_);
v___x_1693_ = v___x_1687_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_val_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
else
{
lean_object* v___x_1695_; 
lean_dec(v___x_1690_);
lean_del_object(v___x_1687_);
lean_inc_ref(v_type_1677_);
v___x_1695_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___f_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc_n(v_a_1696_, 2);
lean_dec_ref(v___x_1695_);
v___f_1697_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1697_, 0, v_type_1677_);
lean_closure_set(v___f_1697_, 1, v_a_1696_);
v___x_1698_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1699_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1698_, v___f_1697_, v_a_1678_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; 
v_unused_1707_ = lean_ctor_get(v___x_1699_, 0);
lean_dec(v_unused_1707_);
v___x_1701_ = v___x_1699_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_dec(v___x_1699_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v_a_1696_);
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1696_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_a_1696_);
v_a_1708_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1699_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1699_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
lean_dec_ref(v_type_1677_);
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v_type_1677_);
v_a_1717_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1684_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1684_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___boxed(lean_object* v_type_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(lean_object* v_type_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_1733_, v_a_1734_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___boxed(lean_object* v_type_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(v_type_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec(v_a_1748_);
lean_dec(v_a_1747_);
return v_res_1758_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
}
#ifdef __cplusplus
}
#endif
