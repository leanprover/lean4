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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__1(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "PowIdentity available: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "NoNatZeroDivisors available: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(lean_object* v___x_9_, lean_object* v_____do__lift_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v_options_22_; uint8_t v_hasTrace_23_; 
v_options_22_ = lean_ctor_get(v___y_19_, 2);
v_hasTrace_23_ = lean_ctor_get_uint8(v_options_22_, sizeof(void*)*1);
if (v_hasTrace_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v___x_9_);
v___x_24_ = lean_box(v_hasTrace_23_);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_26_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1));
v___x_27_ = l_Lean_Name_append(v___x_26_, v___x_9_);
v___x_28_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_10_, v_options_22_, v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = lean_box(v___x_28_);
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___boxed(lean_object* v___x_31_, lean_object* v_____do__lift_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_31_, v_____do__lift_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v_____do__lift_32_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__1(lean_object* v___x_45_, lean_object* v_s_46_){
_start:
{
lean_object* v_rings_47_; lean_object* v_typeIdOf_48_; lean_object* v_exprToRingId_49_; lean_object* v_semirings_50_; lean_object* v_stypeIdOf_51_; lean_object* v_exprToSemiringId_52_; lean_object* v_ncRings_53_; lean_object* v_exprToNCRingId_54_; lean_object* v_nctypeIdOf_55_; lean_object* v_ncSemirings_56_; lean_object* v_exprToNCSemiringId_57_; lean_object* v_ncstypeIdOf_58_; lean_object* v_steps_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_67_; 
v_rings_47_ = lean_ctor_get(v_s_46_, 0);
v_typeIdOf_48_ = lean_ctor_get(v_s_46_, 1);
v_exprToRingId_49_ = lean_ctor_get(v_s_46_, 2);
v_semirings_50_ = lean_ctor_get(v_s_46_, 3);
v_stypeIdOf_51_ = lean_ctor_get(v_s_46_, 4);
v_exprToSemiringId_52_ = lean_ctor_get(v_s_46_, 5);
v_ncRings_53_ = lean_ctor_get(v_s_46_, 6);
v_exprToNCRingId_54_ = lean_ctor_get(v_s_46_, 7);
v_nctypeIdOf_55_ = lean_ctor_get(v_s_46_, 8);
v_ncSemirings_56_ = lean_ctor_get(v_s_46_, 9);
v_exprToNCSemiringId_57_ = lean_ctor_get(v_s_46_, 10);
v_ncstypeIdOf_58_ = lean_ctor_get(v_s_46_, 11);
v_steps_59_ = lean_ctor_get(v_s_46_, 12);
v_isSharedCheck_67_ = !lean_is_exclusive(v_s_46_);
if (v_isSharedCheck_67_ == 0)
{
v___x_61_ = v_s_46_;
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_steps_59_);
lean_inc(v_ncstypeIdOf_58_);
lean_inc(v_exprToNCSemiringId_57_);
lean_inc(v_ncSemirings_56_);
lean_inc(v_nctypeIdOf_55_);
lean_inc(v_exprToNCRingId_54_);
lean_inc(v_ncRings_53_);
lean_inc(v_exprToSemiringId_52_);
lean_inc(v_stypeIdOf_51_);
lean_inc(v_semirings_50_);
lean_inc(v_exprToRingId_49_);
lean_inc(v_typeIdOf_48_);
lean_inc(v_rings_47_);
lean_dec(v_s_46_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = lean_array_push(v_rings_47_, v___x_45_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_63_);
v___x_65_ = v___x_61_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_typeIdOf_48_);
lean_ctor_set(v_reuseFailAlloc_66_, 2, v_exprToRingId_49_);
lean_ctor_set(v_reuseFailAlloc_66_, 3, v_semirings_50_);
lean_ctor_set(v_reuseFailAlloc_66_, 4, v_stypeIdOf_51_);
lean_ctor_set(v_reuseFailAlloc_66_, 5, v_exprToSemiringId_52_);
lean_ctor_set(v_reuseFailAlloc_66_, 6, v_ncRings_53_);
lean_ctor_set(v_reuseFailAlloc_66_, 7, v_exprToNCRingId_54_);
lean_ctor_set(v_reuseFailAlloc_66_, 8, v_nctypeIdOf_55_);
lean_ctor_set(v_reuseFailAlloc_66_, 9, v_ncSemirings_56_);
lean_ctor_set(v_reuseFailAlloc_66_, 10, v_exprToNCSemiringId_57_);
lean_ctor_set(v_reuseFailAlloc_66_, 11, v_ncstypeIdOf_58_);
lean_ctor_set(v_reuseFailAlloc_66_, 12, v_steps_59_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(lean_object* v_msgData_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; lean_object* v_env_75_; lean_object* v___x_76_; lean_object* v_mctx_77_; lean_object* v_lctx_78_; lean_object* v_options_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_74_ = lean_st_ref_get(v___y_72_);
v_env_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc_ref(v_env_75_);
lean_dec(v___x_74_);
v___x_76_ = lean_st_ref_get(v___y_70_);
v_mctx_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_mctx_77_);
lean_dec(v___x_76_);
v_lctx_78_ = lean_ctor_get(v___y_69_, 2);
v_options_79_ = lean_ctor_get(v___y_71_, 2);
lean_inc_ref(v_options_79_);
lean_inc_ref(v_lctx_78_);
v___x_80_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_80_, 0, v_env_75_);
lean_ctor_set(v___x_80_, 1, v_mctx_77_);
lean_ctor_set(v___x_80_, 2, v_lctx_78_);
lean_ctor_set(v___x_80_, 3, v_options_79_);
v___x_81_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_msgData_68_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1___boxed(lean_object* v_msgData_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msgData_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_89_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_90_; double v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_float_of_nat(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(lean_object* v_cls_95_, lean_object* v_msg_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_ref_102_; lean_object* v___x_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_148_; 
v_ref_102_ = lean_ctor_get(v___y_99_, 5);
v___x_103_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_148_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_148_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_148_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v_traceState_109_; lean_object* v_env_110_; lean_object* v_nextMacroScope_111_; lean_object* v_ngen_112_; lean_object* v_auxDeclNGen_113_; lean_object* v_cache_114_; lean_object* v_messages_115_; lean_object* v_infoState_116_; lean_object* v_snapshotTasks_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_147_; 
v___x_108_ = lean_st_ref_take(v___y_100_);
v_traceState_109_ = lean_ctor_get(v___x_108_, 4);
v_env_110_ = lean_ctor_get(v___x_108_, 0);
v_nextMacroScope_111_ = lean_ctor_get(v___x_108_, 1);
v_ngen_112_ = lean_ctor_get(v___x_108_, 2);
v_auxDeclNGen_113_ = lean_ctor_get(v___x_108_, 3);
v_cache_114_ = lean_ctor_get(v___x_108_, 5);
v_messages_115_ = lean_ctor_get(v___x_108_, 6);
v_infoState_116_ = lean_ctor_get(v___x_108_, 7);
v_snapshotTasks_117_ = lean_ctor_get(v___x_108_, 8);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_147_ == 0)
{
v___x_119_ = v___x_108_;
v_isShared_120_ = v_isSharedCheck_147_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_snapshotTasks_117_);
lean_inc(v_infoState_116_);
lean_inc(v_messages_115_);
lean_inc(v_cache_114_);
lean_inc(v_traceState_109_);
lean_inc(v_auxDeclNGen_113_);
lean_inc(v_ngen_112_);
lean_inc(v_nextMacroScope_111_);
lean_inc(v_env_110_);
lean_dec(v___x_108_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_147_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
uint64_t v_tid_121_; lean_object* v_traces_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_146_; 
v_tid_121_ = lean_ctor_get_uint64(v_traceState_109_, sizeof(void*)*1);
v_traces_122_ = lean_ctor_get(v_traceState_109_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_traceState_109_);
if (v_isSharedCheck_146_ == 0)
{
v___x_124_ = v_traceState_109_;
v_isShared_125_ = v_isSharedCheck_146_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_traces_122_);
lean_dec(v_traceState_109_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_146_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; double v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0);
v___x_128_ = 0;
v___x_129_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1));
v___x_130_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_130_, 0, v_cls_95_);
lean_ctor_set(v___x_130_, 1, v___x_126_);
lean_ctor_set(v___x_130_, 2, v___x_129_);
lean_ctor_set_float(v___x_130_, sizeof(void*)*3, v___x_127_);
lean_ctor_set_float(v___x_130_, sizeof(void*)*3 + 8, v___x_127_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*3 + 16, v___x_128_);
v___x_131_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2));
v___x_132_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v_a_104_);
lean_ctor_set(v___x_132_, 2, v___x_131_);
lean_inc(v_ref_102_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_ref_102_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = l_Lean_PersistentArray_push___redArg(v_traces_122_, v___x_133_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_134_);
v___x_136_ = v___x_124_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_134_);
lean_ctor_set_uint64(v_reuseFailAlloc_145_, sizeof(void*)*1, v_tid_121_);
v___x_136_ = v_reuseFailAlloc_145_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 4, v___x_136_);
v___x_138_ = v___x_119_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_env_110_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_nextMacroScope_111_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_ngen_112_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v_auxDeclNGen_113_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_144_, 5, v_cache_114_);
lean_ctor_set(v_reuseFailAlloc_144_, 6, v_messages_115_);
lean_ctor_set(v_reuseFailAlloc_144_, 7, v_infoState_116_);
lean_ctor_set(v_reuseFailAlloc_144_, 8, v_snapshotTasks_117_);
v___x_138_ = v_reuseFailAlloc_144_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_139_ = lean_st_ref_set(v___y_100_, v___x_138_);
v___x_140_ = lean_box(0);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_140_);
v___x_142_ = v___x_106_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_cls_149_, lean_object* v_msg_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_149_, v_msg_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_unsigned_to_nat(32u);
v___x_189_ = lean_mk_empty_array_with_capacity(v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15(void){
_start:
{
size_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_191_ = ((size_t)5ULL);
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_unsigned_to_nat(32u);
v___x_194_ = lean_mk_empty_array_with_capacity(v___x_193_);
v___x_195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14);
v___x_196_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
lean_ctor_set(v___x_196_, 2, v___x_192_);
lean_ctor_set(v___x_196_, 3, v___x_192_);
lean_ctor_set_usize(v___x_196_, 4, v___x_191_);
return v___x_196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16(void){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0(lean_box(0));
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6));
v___x_207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1));
v___x_208_ = l_Lean_Name_append(v___x_207_, v___x_206_);
return v___x_208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26));
v___x_216_ = l_Lean_stringToMessageData(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(lean_object* v_type_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; 
lean_inc_ref(v_type_220_);
v___x_232_ = l_Lean_Meta_getDecLevel(v_type_220_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc_n(v_a_233_, 2);
lean_dec_ref(v___x_232_);
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3));
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_236_, 0, v_a_233_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
lean_inc_ref(v___x_236_);
v___x_237_ = l_Lean_mkConst(v___x_234_, v___x_236_);
lean_inc_ref(v_type_220_);
v___x_238_ = l_Lean_Expr_app___override(v___x_237_, v_type_220_);
v___x_239_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_238_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_501_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_501_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_501_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_501_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
if (lean_obj_tag(v_a_240_) == 1)
{
lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_496_; 
lean_del_object(v___x_242_);
v_val_244_ = lean_ctor_get(v_a_240_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_240_);
if (v_isSharedCheck_496_ == 0)
{
v___x_246_ = v_a_240_;
v_isShared_247_ = v_isSharedCheck_496_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v_a_240_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_496_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_inheritedTraceOptions_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_495_; 
v_inheritedTraceOptions_248_ = lean_ctor_get(v_a_229_, 13);
v___x_249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6));
v___x_250_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_249_, v_inheritedTraceOptions_248_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_495_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_495_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_495_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; uint8_t v___x_473_; 
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8));
lean_inc_ref_n(v___x_236_, 3);
v___x_256_ = l_Lean_mkConst(v___x_255_, v___x_236_);
lean_inc(v_val_244_);
lean_inc_ref_n(v_type_220_, 3);
v___x_257_ = l_Lean_mkAppB(v___x_256_, v_type_220_, v_val_244_);
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11));
v___x_259_ = l_Lean_mkConst(v___x_258_, v___x_236_);
lean_inc_ref(v___x_257_);
v___x_260_ = l_Lean_mkAppB(v___x_259_, v_type_220_, v___x_257_);
v___x_261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13));
v___x_262_ = l_Lean_mkConst(v___x_261_, v___x_236_);
lean_inc_ref(v___x_260_);
v___x_263_ = l_Lean_mkAppB(v___x_262_, v_type_220_, v___x_260_);
v___x_473_ = lean_unbox(v_a_251_);
lean_dec(v_a_251_);
if (v___x_473_ == 0)
{
v___y_427_ = v_a_221_;
v___y_428_ = v_a_222_;
v___y_429_ = v_a_223_;
v___y_430_ = v_a_224_;
v___y_431_ = v_a_225_;
v___y_432_ = v_a_226_;
v___y_433_ = v_a_227_;
v___y_434_ = v_a_228_;
v___y_435_ = v_a_229_;
v___y_436_ = v_a_230_;
goto v___jp_426_;
}
else
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Meta_Grind_updateLastTag(v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec_ref(v___x_474_);
v___x_475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
lean_inc_ref(v_type_220_);
v___x_476_ = l_Lean_MessageData_ofExpr(v_type_220_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_249_, v___x_477_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_dec_ref(v___x_478_);
v___y_427_ = v_a_221_;
v___y_428_ = v_a_222_;
v___y_429_ = v_a_223_;
v___y_430_ = v_a_224_;
v___y_431_ = v_a_225_;
v___y_432_ = v_a_226_;
v___y_433_ = v_a_227_;
v___y_434_ = v_a_228_;
v___y_435_ = v_a_229_;
v___y_436_ = v_a_230_;
goto v___jp_426_;
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_253_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec_ref(v___x_236_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_253_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec_ref(v___x_236_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_487_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_474_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_474_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
v___jp_264_:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_rings_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___f_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref(v___x_271_);
v_rings_273_ = lean_ctor_get(v_a_272_, 0);
lean_inc_ref(v_rings_273_);
lean_dec(v_a_272_);
v___x_274_ = lean_box(0);
v___x_275_ = lean_array_get_size(v_rings_273_);
lean_dec_ref(v_rings_273_);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17);
v___x_279_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_279_, 0, v___x_275_);
lean_ctor_set(v___x_279_, 1, v_type_220_);
lean_ctor_set(v___x_279_, 2, v_a_233_);
lean_ctor_set(v___x_279_, 3, v___x_257_);
lean_ctor_set(v___x_279_, 4, v___x_260_);
lean_ctor_set(v___x_279_, 5, v___y_266_);
lean_ctor_set(v___x_279_, 6, v___x_274_);
lean_ctor_set(v___x_279_, 7, v___x_274_);
lean_ctor_set(v___x_279_, 8, v___x_274_);
lean_ctor_set(v___x_279_, 9, v___x_274_);
lean_ctor_set(v___x_279_, 10, v___x_274_);
lean_ctor_set(v___x_279_, 11, v___x_274_);
lean_ctor_set(v___x_279_, 12, v___x_274_);
lean_ctor_set(v___x_279_, 13, v___x_274_);
lean_ctor_set(v___x_279_, 14, v___x_277_);
lean_ctor_set(v___x_279_, 15, v___x_278_);
lean_ctor_set(v___x_279_, 16, v___x_278_);
v___x_280_ = lean_box(1);
v___x_281_ = 0;
v___x_282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18);
v___x_283_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v___x_283_, 0, v___x_279_);
lean_ctor_set(v___x_283_, 1, v___x_274_);
lean_ctor_set(v___x_283_, 2, v___x_274_);
lean_ctor_set(v___x_283_, 3, v___x_263_);
lean_ctor_set(v___x_283_, 4, v_val_244_);
lean_ctor_set(v___x_283_, 5, v___y_268_);
lean_ctor_set(v___x_283_, 6, v___y_267_);
lean_ctor_set(v___x_283_, 7, v___y_265_);
lean_ctor_set(v___x_283_, 8, v___x_277_);
lean_ctor_set(v___x_283_, 9, v___x_276_);
lean_ctor_set(v___x_283_, 10, v___x_276_);
lean_ctor_set(v___x_283_, 11, v___x_280_);
lean_ctor_set(v___x_283_, 12, v___x_235_);
lean_ctor_set(v___x_283_, 13, v___x_277_);
lean_ctor_set(v___x_283_, 14, v___x_282_);
lean_ctor_set(v___x_283_, 15, v___x_276_);
lean_ctor_set(v___x_283_, 16, v___x_274_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*17, v___x_281_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*17 + 1, v___x_281_);
v___f_284_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__1), 2, 1);
lean_closure_set(v___f_284_, 0, v___x_283_);
v___x_285_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_286_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_285_, v___f_284_, v___y_269_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v___x_286_, 0);
lean_dec(v_unused_297_);
v___x_288_ = v___x_286_;
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
else
{
lean_dec(v___x_286_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_275_);
v___x_291_ = v___x_246_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_275_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_293_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_291_);
v___x_293_ = v___x_288_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_del_object(v___x_246_);
v_a_298_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_286_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_286_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v___y_268_);
lean_dec(v___y_267_);
lean_dec(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_306_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_271_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_271_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
v___jp_314_:
{
lean_object* v___x_332_; 
lean_inc_ref(v___y_330_);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 3);
lean_ctor_set(v___x_253_, 0, v___y_330_);
v___x_332_ = v___x_253_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___y_330_);
v___x_332_ = v_reuseFailAlloc_344_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = l_Lean_MessageData_ofFormat(v___x_332_);
lean_inc_ref(v___y_324_);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___y_324_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_249_, v___x_334_, v___y_320_, v___y_322_, v___y_325_, v___y_318_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_dec_ref(v___x_335_);
v___y_265_ = v___y_316_;
v___y_266_ = v___y_326_;
v___y_267_ = v___y_321_;
v___y_268_ = v___y_329_;
v___y_269_ = v___y_315_;
v___y_270_ = v___y_325_;
goto v___jp_264_;
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v___y_329_);
lean_dec(v___y_326_);
lean_dec(v___y_321_);
lean_dec(v___y_316_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
v___jp_345_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20));
v___x_359_ = l_Lean_mkConst(v___x_358_, v___x_236_);
lean_inc_ref(v_type_220_);
v___x_360_ = l_Lean_Expr_app___override(v___x_359_, v_type_220_);
v___x_361_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_360_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
lean_inc_ref(v_type_220_);
lean_inc(v_a_233_);
v___x_363_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(v_a_233_, v_type_220_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_options_364_; uint8_t v_hasTrace_365_; 
v_options_364_ = lean_ctor_get(v___y_356_, 2);
v_hasTrace_365_ = lean_ctor_get_uint8(v_options_364_, sizeof(void*)*1);
if (v_hasTrace_365_ == 0)
{
lean_object* v_a_366_; 
lean_del_object(v___x_253_);
v_a_366_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_366_);
lean_dec_ref(v___x_363_);
v___y_265_ = v_a_366_;
v___y_266_ = v___y_346_;
v___y_267_ = v_a_362_;
v___y_268_ = v___y_347_;
v___y_269_ = v___y_348_;
v___y_270_ = v___y_356_;
goto v___jp_264_;
}
else
{
lean_object* v_a_367_; lean_object* v_inheritedTraceOptions_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_a_367_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_363_);
v_inheritedTraceOptions_368_ = lean_ctor_get(v___y_356_, 13);
v___x_369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21);
v___x_370_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_368_, v_options_364_, v___x_369_);
if (v___x_370_ == 0)
{
lean_del_object(v___x_253_);
v___y_265_ = v_a_367_;
v___y_266_ = v___y_346_;
v___y_267_ = v_a_362_;
v___y_268_ = v___y_347_;
v___y_269_ = v___y_348_;
v___y_270_ = v___y_356_;
goto v___jp_264_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Meta_Grind_updateLastTag(v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v___x_372_; 
lean_dec_ref(v___x_371_);
v___x_372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23);
if (lean_obj_tag(v_a_367_) == 0)
{
lean_object* v___x_373_; 
v___x_373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24));
v___y_315_ = v___y_348_;
v___y_316_ = v_a_367_;
v___y_317_ = v___y_350_;
v___y_318_ = v___y_357_;
v___y_319_ = v___y_349_;
v___y_320_ = v___y_354_;
v___y_321_ = v_a_362_;
v___y_322_ = v___y_355_;
v___y_323_ = v___y_353_;
v___y_324_ = v___x_372_;
v___y_325_ = v___y_356_;
v___y_326_ = v___y_346_;
v___y_327_ = v___y_351_;
v___y_328_ = v___y_352_;
v___y_329_ = v___y_347_;
v___y_330_ = v___x_373_;
goto v___jp_314_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25));
v___y_315_ = v___y_348_;
v___y_316_ = v_a_367_;
v___y_317_ = v___y_350_;
v___y_318_ = v___y_357_;
v___y_319_ = v___y_349_;
v___y_320_ = v___y_354_;
v___y_321_ = v_a_362_;
v___y_322_ = v___y_355_;
v___y_323_ = v___y_353_;
v___y_324_ = v___x_372_;
v___y_325_ = v___y_356_;
v___y_326_ = v___y_346_;
v___y_327_ = v___y_351_;
v___y_328_ = v___y_352_;
v___y_329_ = v___y_347_;
v___y_330_ = v___x_374_;
goto v___jp_314_;
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_a_367_);
lean_dec(v_a_362_);
lean_dec(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_253_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_375_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_371_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_371_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_a_362_);
lean_dec(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_253_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_383_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_363_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_363_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
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
lean_dec(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_253_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_391_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_361_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_361_);
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
v___jp_399_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_inc_ref(v___y_413_);
v___x_414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_414_, 0, v___y_413_);
v___x_415_ = l_Lean_MessageData_ofFormat(v___x_414_);
lean_inc_ref(v___y_403_);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___y_403_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_249_, v___x_416_, v___y_408_, v___y_400_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_dec_ref(v___x_417_);
v___y_346_ = v___y_410_;
v___y_347_ = v___y_412_;
v___y_348_ = v___y_401_;
v___y_349_ = v___y_411_;
v___y_350_ = v___y_407_;
v___y_351_ = v___y_404_;
v___y_352_ = v___y_409_;
v___y_353_ = v___y_402_;
v___y_354_ = v___y_408_;
v___y_355_ = v___y_400_;
v___y_356_ = v___y_405_;
v___y_357_ = v___y_406_;
goto v___jp_345_;
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec(v___y_412_);
lean_dec(v___y_410_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_253_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec_ref(v___x_236_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
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
v___jp_426_:
{
lean_object* v___x_437_; 
lean_inc_ref(v___x_260_);
lean_inc_ref(v_type_220_);
lean_inc(v_a_233_);
v___x_437_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_233_, v_type_220_, v___x_260_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref(v___x_437_);
lean_inc_ref(v_type_220_);
lean_inc(v_a_233_);
v___x_439_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_a_233_, v_type_220_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_inheritedTraceOptions_441_; lean_object* v___x_442_; lean_object* v_a_443_; uint8_t v___x_444_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v___x_439_);
v_inheritedTraceOptions_441_ = lean_ctor_get(v___y_435_, 13);
v___x_442_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_249_, v_inheritedTraceOptions_441_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref(v___x_442_);
v___x_444_ = lean_unbox(v_a_443_);
lean_dec(v_a_443_);
if (v___x_444_ == 0)
{
v___y_346_ = v_a_438_;
v___y_347_ = v_a_440_;
v___y_348_ = v___y_427_;
v___y_349_ = v___y_428_;
v___y_350_ = v___y_429_;
v___y_351_ = v___y_430_;
v___y_352_ = v___y_431_;
v___y_353_ = v___y_432_;
v___y_354_ = v___y_433_;
v___y_355_ = v___y_434_;
v___y_356_ = v___y_435_;
v___y_357_ = v___y_436_;
goto v___jp_345_;
}
else
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Grind_updateLastTag(v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; 
lean_dec_ref(v___x_445_);
v___x_446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27);
if (lean_obj_tag(v_a_440_) == 0)
{
lean_object* v___x_447_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24));
v___y_400_ = v___y_434_;
v___y_401_ = v___y_427_;
v___y_402_ = v___y_432_;
v___y_403_ = v___x_446_;
v___y_404_ = v___y_430_;
v___y_405_ = v___y_435_;
v___y_406_ = v___y_436_;
v___y_407_ = v___y_429_;
v___y_408_ = v___y_433_;
v___y_409_ = v___y_431_;
v___y_410_ = v_a_438_;
v___y_411_ = v___y_428_;
v___y_412_ = v_a_440_;
v___y_413_ = v___x_447_;
goto v___jp_399_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25));
v___y_400_ = v___y_434_;
v___y_401_ = v___y_427_;
v___y_402_ = v___y_432_;
v___y_403_ = v___x_446_;
v___y_404_ = v___y_430_;
v___y_405_ = v___y_435_;
v___y_406_ = v___y_436_;
v___y_407_ = v___y_429_;
v___y_408_ = v___y_433_;
v___y_409_ = v___y_431_;
v___y_410_ = v_a_438_;
v___y_411_ = v___y_428_;
v___y_412_ = v_a_440_;
v___y_413_ = v___x_448_;
goto v___jp_399_;
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_a_440_);
lean_dec(v_a_438_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_253_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec_ref(v___x_236_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_449_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_445_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_445_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
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
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_a_438_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_253_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec_ref(v___x_236_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_457_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_439_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_439_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
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
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_260_);
lean_dec_ref(v___x_257_);
lean_del_object(v___x_253_);
lean_del_object(v___x_246_);
lean_dec(v_val_244_);
lean_dec_ref(v___x_236_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_465_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_437_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_437_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec(v_a_240_);
lean_dec_ref(v___x_236_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v___x_497_ = lean_box(0);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_497_);
v___x_499_ = v___x_242_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
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
lean_dec_ref(v___x_236_);
lean_dec(v_a_233_);
lean_dec_ref(v_type_220_);
v_a_502_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_239_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_239_);
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
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_type_220_);
v_a_510_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_232_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_232_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___boxed(lean_object* v_type_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec(v_a_519_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(lean_object* v_cls_531_, lean_object* v_msg_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_531_, v_msg_532_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___boxed(lean_object* v_cls_545_, lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(v_cls_545_, v_msg_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec(v___y_547_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_ks_563_; lean_object* v_vs_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_588_; 
v_ks_563_ = lean_ctor_get(v_x_559_, 0);
v_vs_564_ = lean_ctor_get(v_x_559_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_588_ == 0)
{
v___x_566_ = v_x_559_;
v_isShared_567_ = v_isSharedCheck_588_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_vs_564_);
lean_inc(v_ks_563_);
lean_dec(v_x_559_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_588_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_get_size(v_ks_563_);
v___x_569_ = lean_nat_dec_lt(v_x_560_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec(v_x_560_);
v___x_570_ = lean_array_push(v_ks_563_, v_x_561_);
v___x_571_ = lean_array_push(v_vs_564_, v_x_562_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v___x_571_);
lean_ctor_set(v___x_566_, 0, v___x_570_);
v___x_573_ = v___x_566_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_object* v_k_x27_575_; uint8_t v___x_576_; 
v_k_x27_575_ = lean_array_fget_borrowed(v_ks_563_, v_x_560_);
v___x_576_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_561_, v_k_x27_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_578_; 
if (v_isShared_567_ == 0)
{
v___x_578_ = v___x_566_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_ks_563_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_vs_564_);
v___x_578_ = v_reuseFailAlloc_582_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_x_560_, v___x_579_);
lean_dec(v_x_560_);
v_x_559_ = v___x_578_;
v_x_560_ = v___x_580_;
goto _start;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_583_ = lean_array_fset(v_ks_563_, v_x_560_, v_x_561_);
v___x_584_ = lean_array_fset(v_vs_564_, v_x_560_, v_x_562_);
lean_dec(v_x_560_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v___x_584_);
lean_ctor_set(v___x_566_, 0, v___x_583_);
v___x_586_ = v___x_566_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_589_, lean_object* v_k_590_, lean_object* v_v_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_589_, v___x_592_, v_k_590_, v_v_591_);
return v___x_593_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_594_; size_t v___x_595_; size_t v___x_596_; 
v___x_594_ = ((size_t)5ULL);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_shift_left(v___x_595_, v___x_594_);
return v___x_596_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; 
v___x_597_ = ((size_t)1ULL);
v___x_598_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0);
v___x_599_ = lean_usize_sub(v___x_598_, v___x_597_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(lean_object* v_x_601_, size_t v_x_602_, size_t v_x_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_601_) == 0)
{
lean_object* v_es_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; lean_object* v_j_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_es_606_ = lean_ctor_get(v_x_601_, 0);
v___x_607_ = ((size_t)5ULL);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
v___x_610_ = lean_usize_land(v_x_602_, v___x_609_);
v_j_611_ = lean_usize_to_nat(v___x_610_);
v___x_612_ = lean_array_get_size(v_es_606_);
v___x_613_ = lean_nat_dec_lt(v_j_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec(v_j_611_);
lean_dec(v_x_605_);
lean_dec_ref(v_x_604_);
return v_x_601_;
}
else
{
lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_650_; 
lean_inc_ref(v_es_606_);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_x_601_, 0);
lean_dec(v_unused_651_);
v___x_615_ = v_x_601_;
v_isShared_616_ = v_isSharedCheck_650_;
goto v_resetjp_614_;
}
else
{
lean_dec(v_x_601_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_650_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_v_617_; lean_object* v___x_618_; lean_object* v_xs_x27_619_; lean_object* v___y_621_; 
v_v_617_ = lean_array_fget(v_es_606_, v_j_611_);
v___x_618_ = lean_box(0);
v_xs_x27_619_ = lean_array_fset(v_es_606_, v_j_611_, v___x_618_);
switch(lean_obj_tag(v_v_617_))
{
case 0:
{
lean_object* v_key_626_; lean_object* v_val_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_637_; 
v_key_626_ = lean_ctor_get(v_v_617_, 0);
v_val_627_ = lean_ctor_get(v_v_617_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_v_617_);
if (v_isSharedCheck_637_ == 0)
{
v___x_629_ = v_v_617_;
v_isShared_630_ = v_isSharedCheck_637_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_val_627_);
lean_inc(v_key_626_);
lean_dec(v_v_617_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_637_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
uint8_t v___x_631_; 
v___x_631_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_604_, v_key_626_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_del_object(v___x_629_);
v___x_632_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_626_, v_val_627_, v_x_604_, v_x_605_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___y_621_ = v___x_633_;
goto v___jp_620_;
}
else
{
lean_object* v___x_635_; 
lean_dec(v_val_627_);
lean_dec(v_key_626_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v_x_605_);
lean_ctor_set(v___x_629_, 0, v_x_604_);
v___x_635_ = v___x_629_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_x_604_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_x_605_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
v___y_621_ = v___x_635_;
goto v___jp_620_;
}
}
}
}
case 1:
{
lean_object* v_node_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_648_; 
v_node_638_ = lean_ctor_get(v_v_617_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_v_617_);
if (v_isSharedCheck_648_ == 0)
{
v___x_640_ = v_v_617_;
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_node_638_);
lean_dec(v_v_617_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_642_ = lean_usize_shift_right(v_x_602_, v___x_607_);
v___x_643_ = lean_usize_add(v_x_603_, v___x_608_);
v___x_644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_node_638_, v___x_642_, v___x_643_, v_x_604_, v_x_605_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_644_);
v___x_646_ = v___x_640_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
v___y_621_ = v___x_646_;
goto v___jp_620_;
}
}
}
default: 
{
lean_object* v___x_649_; 
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v_x_604_);
lean_ctor_set(v___x_649_, 1, v_x_605_);
v___y_621_ = v___x_649_;
goto v___jp_620_;
}
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_array_fset(v_xs_x27_619_, v_j_611_, v___y_621_);
lean_dec(v_j_611_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_622_);
v___x_624_ = v___x_615_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
else
{
lean_object* v_ks_652_; lean_object* v_vs_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_673_; 
v_ks_652_ = lean_ctor_get(v_x_601_, 0);
v_vs_653_ = lean_ctor_get(v_x_601_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_673_ == 0)
{
v___x_655_ = v_x_601_;
v_isShared_656_ = v_isSharedCheck_673_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_vs_653_);
lean_inc(v_ks_652_);
lean_dec(v_x_601_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_673_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_ks_652_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_vs_653_);
v___x_658_ = v_reuseFailAlloc_672_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v_newNode_659_; uint8_t v___y_661_; size_t v___x_667_; uint8_t v___x_668_; 
v_newNode_659_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v___x_658_, v_x_604_, v_x_605_);
v___x_667_ = ((size_t)7ULL);
v___x_668_ = lean_usize_dec_le(v___x_667_, v_x_603_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_659_);
v___x_670_ = lean_unsigned_to_nat(4u);
v___x_671_ = lean_nat_dec_lt(v___x_669_, v___x_670_);
lean_dec(v___x_669_);
v___y_661_ = v___x_671_;
goto v___jp_660_;
}
else
{
v___y_661_ = v___x_668_;
goto v___jp_660_;
}
v___jp_660_:
{
if (v___y_661_ == 0)
{
lean_object* v_ks_662_; lean_object* v_vs_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_ks_662_ = lean_ctor_get(v_newNode_659_, 0);
lean_inc_ref(v_ks_662_);
v_vs_663_ = lean_ctor_get(v_newNode_659_, 1);
lean_inc_ref(v_vs_663_);
lean_dec_ref(v_newNode_659_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2);
v___x_666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_x_603_, v_ks_662_, v_vs_663_, v___x_664_, v___x_665_);
lean_dec_ref(v_vs_663_);
lean_dec_ref(v_ks_662_);
return v___x_666_;
}
else
{
return v_newNode_659_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_674_, lean_object* v_keys_675_, lean_object* v_vals_676_, lean_object* v_i_677_, lean_object* v_entries_678_){
_start:
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_array_get_size(v_keys_675_);
v___x_680_ = lean_nat_dec_lt(v_i_677_, v___x_679_);
if (v___x_680_ == 0)
{
lean_dec(v_i_677_);
return v_entries_678_;
}
else
{
lean_object* v_k_681_; lean_object* v_v_682_; uint64_t v___x_683_; size_t v_h_684_; size_t v___x_685_; lean_object* v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v_h_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_k_681_ = lean_array_fget_borrowed(v_keys_675_, v_i_677_);
v_v_682_ = lean_array_fget_borrowed(v_vals_676_, v_i_677_);
v___x_683_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_681_);
v_h_684_ = lean_uint64_to_usize(v___x_683_);
v___x_685_ = ((size_t)5ULL);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_sub(v_depth_674_, v___x_687_);
v___x_689_ = lean_usize_mul(v___x_685_, v___x_688_);
v_h_690_ = lean_usize_shift_right(v_h_684_, v___x_689_);
v___x_691_ = lean_nat_add(v_i_677_, v___x_686_);
lean_dec(v_i_677_);
lean_inc(v_v_682_);
lean_inc(v_k_681_);
v___x_692_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_entries_678_, v_h_690_, v_depth_674_, v_k_681_, v_v_682_);
v_i_677_ = v___x_691_;
v_entries_678_ = v___x_692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_694_, lean_object* v_keys_695_, lean_object* v_vals_696_, lean_object* v_i_697_, lean_object* v_entries_698_){
_start:
{
size_t v_depth_boxed_699_; lean_object* v_res_700_; 
v_depth_boxed_699_ = lean_unbox_usize(v_depth_694_);
lean_dec(v_depth_694_);
v_res_700_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_699_, v_keys_695_, v_vals_696_, v_i_697_, v_entries_698_);
lean_dec_ref(v_vals_696_);
lean_dec_ref(v_keys_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
size_t v_x_3646__boxed_706_; size_t v_x_3647__boxed_707_; lean_object* v_res_708_; 
v_x_3646__boxed_706_ = lean_unbox_usize(v_x_702_);
lean_dec(v_x_702_);
v_x_3647__boxed_707_ = lean_unbox_usize(v_x_703_);
lean_dec(v_x_703_);
v_res_708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_701_, v_x_3646__boxed_706_, v_x_3647__boxed_707_, v_x_704_, v_x_705_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
uint64_t v___x_712_; size_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; 
v___x_712_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_710_);
v___x_713_ = lean_uint64_to_usize(v___x_712_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_709_, v___x_713_, v___x_714_, v_x_710_, v_x_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(lean_object* v_type_716_, lean_object* v_a_717_, lean_object* v_s_718_){
_start:
{
lean_object* v_rings_719_; lean_object* v_typeIdOf_720_; lean_object* v_exprToRingId_721_; lean_object* v_semirings_722_; lean_object* v_stypeIdOf_723_; lean_object* v_exprToSemiringId_724_; lean_object* v_ncRings_725_; lean_object* v_exprToNCRingId_726_; lean_object* v_nctypeIdOf_727_; lean_object* v_ncSemirings_728_; lean_object* v_exprToNCSemiringId_729_; lean_object* v_ncstypeIdOf_730_; lean_object* v_steps_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_739_; 
v_rings_719_ = lean_ctor_get(v_s_718_, 0);
v_typeIdOf_720_ = lean_ctor_get(v_s_718_, 1);
v_exprToRingId_721_ = lean_ctor_get(v_s_718_, 2);
v_semirings_722_ = lean_ctor_get(v_s_718_, 3);
v_stypeIdOf_723_ = lean_ctor_get(v_s_718_, 4);
v_exprToSemiringId_724_ = lean_ctor_get(v_s_718_, 5);
v_ncRings_725_ = lean_ctor_get(v_s_718_, 6);
v_exprToNCRingId_726_ = lean_ctor_get(v_s_718_, 7);
v_nctypeIdOf_727_ = lean_ctor_get(v_s_718_, 8);
v_ncSemirings_728_ = lean_ctor_get(v_s_718_, 9);
v_exprToNCSemiringId_729_ = lean_ctor_get(v_s_718_, 10);
v_ncstypeIdOf_730_ = lean_ctor_get(v_s_718_, 11);
v_steps_731_ = lean_ctor_get(v_s_718_, 12);
v_isSharedCheck_739_ = !lean_is_exclusive(v_s_718_);
if (v_isSharedCheck_739_ == 0)
{
v___x_733_ = v_s_718_;
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_steps_731_);
lean_inc(v_ncstypeIdOf_730_);
lean_inc(v_exprToNCSemiringId_729_);
lean_inc(v_ncSemirings_728_);
lean_inc(v_nctypeIdOf_727_);
lean_inc(v_exprToNCRingId_726_);
lean_inc(v_ncRings_725_);
lean_inc(v_exprToSemiringId_724_);
lean_inc(v_stypeIdOf_723_);
lean_inc(v_semirings_722_);
lean_inc(v_exprToRingId_721_);
lean_inc(v_typeIdOf_720_);
lean_inc(v_rings_719_);
lean_dec(v_s_718_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_typeIdOf_720_, v_type_716_, v_a_717_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_rings_719_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_exprToRingId_721_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_semirings_722_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_stypeIdOf_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 5, v_exprToSemiringId_724_);
lean_ctor_set(v_reuseFailAlloc_738_, 6, v_ncRings_725_);
lean_ctor_set(v_reuseFailAlloc_738_, 7, v_exprToNCRingId_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 8, v_nctypeIdOf_727_);
lean_ctor_set(v_reuseFailAlloc_738_, 9, v_ncSemirings_728_);
lean_ctor_set(v_reuseFailAlloc_738_, 10, v_exprToNCSemiringId_729_);
lean_ctor_set(v_reuseFailAlloc_738_, 11, v_ncstypeIdOf_730_);
lean_ctor_set(v_reuseFailAlloc_738_, 12, v_steps_731_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_740_, lean_object* v_vals_741_, lean_object* v_i_742_, lean_object* v_k_743_){
_start:
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_array_get_size(v_keys_740_);
v___x_745_ = lean_nat_dec_lt(v_i_742_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec(v_i_742_);
v___x_746_ = lean_box(0);
return v___x_746_;
}
else
{
lean_object* v_k_x27_747_; uint8_t v___x_748_; 
v_k_x27_747_ = lean_array_fget_borrowed(v_keys_740_, v_i_742_);
v___x_748_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_743_, v_k_x27_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_i_742_, v___x_749_);
lean_dec(v_i_742_);
v_i_742_ = v___x_750_;
goto _start;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_array_fget_borrowed(v_vals_741_, v_i_742_);
lean_dec(v_i_742_);
lean_inc(v___x_752_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_754_, lean_object* v_vals_755_, lean_object* v_i_756_, lean_object* v_k_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_754_, v_vals_755_, v_i_756_, v_k_757_);
lean_dec_ref(v_k_757_);
lean_dec_ref(v_vals_755_);
lean_dec_ref(v_keys_754_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_759_, size_t v_x_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_759_) == 0)
{
lean_object* v_es_762_; lean_object* v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v_j_767_; lean_object* v___x_768_; 
v_es_762_ = lean_ctor_get(v_x_759_, 0);
v___x_763_ = lean_box(2);
v___x_764_ = ((size_t)5ULL);
v___x_765_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
v___x_766_ = lean_usize_land(v_x_760_, v___x_765_);
v_j_767_ = lean_usize_to_nat(v___x_766_);
v___x_768_ = lean_array_get_borrowed(v___x_763_, v_es_762_, v_j_767_);
lean_dec(v_j_767_);
switch(lean_obj_tag(v___x_768_))
{
case 0:
{
lean_object* v_key_769_; lean_object* v_val_770_; uint8_t v___x_771_; 
v_key_769_ = lean_ctor_get(v___x_768_, 0);
v_val_770_ = lean_ctor_get(v___x_768_, 1);
v___x_771_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_761_, v_key_769_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
v___x_772_ = lean_box(0);
return v___x_772_;
}
else
{
lean_object* v___x_773_; 
lean_inc(v_val_770_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v_val_770_);
return v___x_773_;
}
}
case 1:
{
lean_object* v_node_774_; size_t v___x_775_; 
v_node_774_ = lean_ctor_get(v___x_768_, 0);
v___x_775_ = lean_usize_shift_right(v_x_760_, v___x_764_);
v_x_759_ = v_node_774_;
v_x_760_ = v___x_775_;
goto _start;
}
default: 
{
lean_object* v___x_777_; 
v___x_777_ = lean_box(0);
return v___x_777_;
}
}
}
else
{
lean_object* v_ks_778_; lean_object* v_vs_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_ks_778_ = lean_ctor_get(v_x_759_, 0);
v_vs_779_ = lean_ctor_get(v_x_759_, 1);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_778_, v_vs_779_, v___x_780_, v_x_761_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
size_t v_x_3864__boxed_785_; lean_object* v_res_786_; 
v_x_3864__boxed_785_ = lean_unbox_usize(v_x_783_);
lean_dec(v_x_783_);
v_res_786_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_782_, v_x_3864__boxed_785_, v_x_784_);
lean_dec_ref(v_x_784_);
lean_dec_ref(v_x_782_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
uint64_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; 
v___x_789_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_788_);
v___x_790_ = lean_uint64_to_usize(v___x_789_);
v___x_791_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_787_, v___x_790_, v_x_788_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_792_, v_x_793_);
lean_dec_ref(v_x_793_);
lean_dec_ref(v_x_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object* v_type_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_796_, v_a_804_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_839_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_839_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_839_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_839_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_typeIdOf_812_; lean_object* v___x_813_; 
v_typeIdOf_812_ = lean_ctor_get(v_a_808_, 1);
lean_inc_ref(v_typeIdOf_812_);
lean_dec(v_a_808_);
v___x_813_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_typeIdOf_812_, v_type_795_);
lean_dec_ref(v_typeIdOf_812_);
if (lean_obj_tag(v___x_813_) == 1)
{
lean_object* v_val_814_; lean_object* v___x_816_; 
lean_dec_ref(v_type_795_);
v_val_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_val_814_);
lean_dec_ref(v___x_813_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v_val_814_);
v___x_816_ = v___x_810_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_val_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
lean_object* v___x_818_; 
lean_dec(v___x_813_);
lean_del_object(v___x_810_);
lean_inc_ref(v_type_795_);
v___x_818_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc_n(v_a_819_, 2);
lean_dec_ref(v___x_818_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_820_, 0, v_type_795_);
lean_closure_set(v___f_820_, 1, v_a_819_);
v___x_821_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_822_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_821_, v___f_820_, v_a_796_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_822_, 0);
lean_dec(v_unused_830_);
v___x_824_ = v___x_822_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_dec(v___x_822_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_a_819_);
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_819_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_a_819_);
v_a_831_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_822_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_822_);
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
else
{
lean_dec_ref(v_type_795_);
return v___x_818_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_type_795_);
v_a_840_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_807_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_807_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___boxed(lean_object* v_type_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec(v_a_849_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(lean_object* v_00_u03b2_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_862_, v_x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(v_00_u03b2_865_, v_x_866_, v_x_867_);
lean_dec_ref(v_x_867_);
lean_dec_ref(v_x_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(lean_object* v_00_u03b2_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_x_870_, v_x_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, size_t v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_875_, v_x_876_, v_x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
size_t v_x_4026__boxed_883_; lean_object* v_res_884_; 
v_x_4026__boxed_883_ = lean_unbox_usize(v_x_881_);
lean_dec(v_x_881_);
v_res_884_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(v_00_u03b2_879_, v_x_880_, v_x_4026__boxed_883_, v_x_882_);
lean_dec_ref(v_x_882_);
lean_dec_ref(v_x_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, size_t v_x_887_, size_t v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_886_, v_x_887_, v_x_888_, v_x_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
size_t v_x_4037__boxed_898_; size_t v_x_4038__boxed_899_; lean_object* v_res_900_; 
v_x_4037__boxed_898_ = lean_unbox_usize(v_x_894_);
lean_dec(v_x_894_);
v_x_4038__boxed_899_ = lean_unbox_usize(v_x_895_);
lean_dec(v_x_895_);
v_res_900_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(v_00_u03b2_892_, v_x_893_, v_x_4037__boxed_898_, v_x_4038__boxed_899_, v_x_896_, v_x_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_901_, lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_heq_904_, lean_object* v_i_905_, lean_object* v_k_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_902_, v_vals_903_, v_i_905_, v_k_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_908_, lean_object* v_keys_909_, lean_object* v_vals_910_, lean_object* v_heq_911_, lean_object* v_i_912_, lean_object* v_k_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_908_, v_keys_909_, v_vals_910_, v_heq_911_, v_i_912_, v_k_913_);
lean_dec_ref(v_k_913_);
lean_dec_ref(v_vals_910_);
lean_dec_ref(v_keys_909_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_915_, lean_object* v_n_916_, lean_object* v_k_917_, lean_object* v_v_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v_n_916_, v_k_917_, v_v_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_920_, size_t v_depth_921_, lean_object* v_keys_922_, lean_object* v_vals_923_, lean_object* v_heq_924_, lean_object* v_i_925_, lean_object* v_entries_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_921_, v_keys_922_, v_vals_923_, v_i_925_, v_entries_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_928_, lean_object* v_depth_929_, lean_object* v_keys_930_, lean_object* v_vals_931_, lean_object* v_heq_932_, lean_object* v_i_933_, lean_object* v_entries_934_){
_start:
{
size_t v_depth_boxed_935_; lean_object* v_res_936_; 
v_depth_boxed_935_ = lean_unbox_usize(v_depth_929_);
lean_dec(v_depth_929_);
v_res_936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_928_, v_depth_boxed_935_, v_keys_930_, v_vals_931_, v_heq_932_, v_i_933_, v_entries_934_);
lean_dec_ref(v_vals_931_);
lean_dec_ref(v_keys_930_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_938_, v_x_939_, v_x_940_, v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(lean_object* v___x_943_, lean_object* v_s_944_){
_start:
{
lean_object* v_rings_945_; lean_object* v_typeIdOf_946_; lean_object* v_exprToRingId_947_; lean_object* v_semirings_948_; lean_object* v_stypeIdOf_949_; lean_object* v_exprToSemiringId_950_; lean_object* v_ncRings_951_; lean_object* v_exprToNCRingId_952_; lean_object* v_nctypeIdOf_953_; lean_object* v_ncSemirings_954_; lean_object* v_exprToNCSemiringId_955_; lean_object* v_ncstypeIdOf_956_; lean_object* v_steps_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
v_rings_945_ = lean_ctor_get(v_s_944_, 0);
v_typeIdOf_946_ = lean_ctor_get(v_s_944_, 1);
v_exprToRingId_947_ = lean_ctor_get(v_s_944_, 2);
v_semirings_948_ = lean_ctor_get(v_s_944_, 3);
v_stypeIdOf_949_ = lean_ctor_get(v_s_944_, 4);
v_exprToSemiringId_950_ = lean_ctor_get(v_s_944_, 5);
v_ncRings_951_ = lean_ctor_get(v_s_944_, 6);
v_exprToNCRingId_952_ = lean_ctor_get(v_s_944_, 7);
v_nctypeIdOf_953_ = lean_ctor_get(v_s_944_, 8);
v_ncSemirings_954_ = lean_ctor_get(v_s_944_, 9);
v_exprToNCSemiringId_955_ = lean_ctor_get(v_s_944_, 10);
v_ncstypeIdOf_956_ = lean_ctor_get(v_s_944_, 11);
v_steps_957_ = lean_ctor_get(v_s_944_, 12);
v_isSharedCheck_965_ = !lean_is_exclusive(v_s_944_);
if (v_isSharedCheck_965_ == 0)
{
v___x_959_ = v_s_944_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_steps_957_);
lean_inc(v_ncstypeIdOf_956_);
lean_inc(v_exprToNCSemiringId_955_);
lean_inc(v_ncSemirings_954_);
lean_inc(v_nctypeIdOf_953_);
lean_inc(v_exprToNCRingId_952_);
lean_inc(v_ncRings_951_);
lean_inc(v_exprToSemiringId_950_);
lean_inc(v_stypeIdOf_949_);
lean_inc(v_semirings_948_);
lean_inc(v_exprToRingId_947_);
lean_inc(v_typeIdOf_946_);
lean_inc(v_rings_945_);
lean_dec(v_s_944_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_array_push(v_ncRings_951_, v___x_943_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 6, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_rings_945_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_typeIdOf_946_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_exprToRingId_947_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_semirings_948_);
lean_ctor_set(v_reuseFailAlloc_964_, 4, v_stypeIdOf_949_);
lean_ctor_set(v_reuseFailAlloc_964_, 5, v_exprToSemiringId_950_);
lean_ctor_set(v_reuseFailAlloc_964_, 6, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_964_, 7, v_exprToNCRingId_952_);
lean_ctor_set(v_reuseFailAlloc_964_, 8, v_nctypeIdOf_953_);
lean_ctor_set(v_reuseFailAlloc_964_, 9, v_ncSemirings_954_);
lean_ctor_set(v_reuseFailAlloc_964_, 10, v_exprToNCSemiringId_955_);
lean_ctor_set(v_reuseFailAlloc_964_, 11, v_ncstypeIdOf_956_);
lean_ctor_set(v_reuseFailAlloc_964_, 12, v_steps_957_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(lean_object* v_type_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_982_; 
lean_inc_ref(v_type_970_);
v___x_982_ = l_Lean_Meta_getDecLevel(v_type_970_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_n(v_a_983_, 2);
lean_dec_ref(v___x_982_);
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0));
v___x_985_ = lean_box(0);
v___x_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_986_, 0, v_a_983_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
lean_inc_ref(v___x_986_);
v___x_987_ = l_Lean_mkConst(v___x_984_, v___x_986_);
lean_inc_ref(v_type_970_);
v___x_988_ = l_Lean_Expr_app___override(v___x_987_, v_type_970_);
v___x_989_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_988_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1092_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1092_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1092_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
if (lean_obj_tag(v_a_990_) == 1)
{
lean_object* v_options_994_; lean_object* v_val_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1087_; 
lean_del_object(v___x_992_);
v_options_994_ = lean_ctor_get(v_a_979_, 2);
v_val_995_ = lean_ctor_get(v_a_990_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_a_990_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_997_ = v_a_990_;
v_isShared_998_ = v_isSharedCheck_1087_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_val_995_);
lean_dec(v_a_990_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1087_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_inheritedTraceOptions_999_; uint8_t v_hasTrace_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; 
v_inheritedTraceOptions_999_ = lean_ctor_get(v_a_979_, 13);
v_hasTrace_1000_ = lean_ctor_get_uint8(v_options_994_, sizeof(void*)*1);
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11));
v___x_1002_ = l_Lean_mkConst(v___x_1001_, v___x_986_);
lean_inc(v_val_995_);
lean_inc_ref(v_type_970_);
v___x_1003_ = l_Lean_mkAppB(v___x_1002_, v_type_970_, v_val_995_);
if (v_hasTrace_1000_ == 0)
{
v___y_1005_ = v_a_971_;
v___y_1006_ = v_a_972_;
v___y_1007_ = v_a_973_;
v___y_1008_ = v_a_974_;
v___y_1009_ = v_a_975_;
v___y_1010_ = v_a_976_;
v___y_1011_ = v_a_977_;
v___y_1012_ = v_a_978_;
v___y_1013_ = v_a_979_;
v___y_1014_ = v_a_980_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6));
v___x_1064_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21);
v___x_1065_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_999_, v_options_994_, v___x_1064_);
if (v___x_1065_ == 0)
{
v___y_1005_ = v_a_971_;
v___y_1006_ = v_a_972_;
v___y_1007_ = v_a_973_;
v___y_1008_ = v_a_974_;
v___y_1009_ = v_a_975_;
v___y_1010_ = v_a_976_;
v___y_1011_ = v_a_977_;
v___y_1012_ = v_a_978_;
v___y_1013_ = v_a_979_;
v___y_1014_ = v_a_980_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_Meta_Grind_updateLastTag(v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec_ref(v___x_1066_);
v___x_1067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
lean_inc_ref(v_type_970_);
v___x_1068_ = l_Lean_MessageData_ofExpr(v_type_970_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_1063_, v___x_1069_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_dec_ref(v___x_1070_);
v___y_1005_ = v_a_971_;
v___y_1006_ = v_a_972_;
v___y_1007_ = v_a_973_;
v___y_1008_ = v_a_974_;
v___y_1009_ = v_a_975_;
v___y_1010_ = v_a_976_;
v___y_1011_ = v_a_977_;
v___y_1012_ = v_a_978_;
v___y_1013_ = v_a_979_;
v___y_1014_ = v_a_980_;
goto v___jp_1004_;
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v___x_1003_);
lean_del_object(v___x_997_);
lean_dec(v_val_995_);
lean_dec(v_a_983_);
lean_dec_ref(v_type_970_);
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v___x_1003_);
lean_del_object(v___x_997_);
lean_dec(v_val_995_);
lean_dec(v_a_983_);
lean_dec_ref(v_type_970_);
v_a_1079_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1066_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1066_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
v___jp_1004_:
{
lean_object* v___x_1015_; 
lean_inc_ref(v___x_1003_);
lean_inc_ref(v_type_970_);
lean_inc(v_a_983_);
v___x_1015_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_983_, v_type_970_, v___x_1003_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref(v___x_1015_);
v___x_1017_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_1005_, v___y_1013_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v_ncRings_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref(v___x_1017_);
v_ncRings_1019_ = lean_ctor_get(v_a_1018_, 6);
lean_inc_ref(v_ncRings_1019_);
lean_dec(v_a_1018_);
v___x_1020_ = lean_array_get_size(v_ncRings_1019_);
lean_dec_ref(v_ncRings_1019_);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
v___x_1023_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17);
v___x_1024_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1020_);
lean_ctor_set(v___x_1024_, 1, v_type_970_);
lean_ctor_set(v___x_1024_, 2, v_a_983_);
lean_ctor_set(v___x_1024_, 3, v_val_995_);
lean_ctor_set(v___x_1024_, 4, v___x_1003_);
lean_ctor_set(v___x_1024_, 5, v_a_1016_);
lean_ctor_set(v___x_1024_, 6, v___x_1021_);
lean_ctor_set(v___x_1024_, 7, v___x_1021_);
lean_ctor_set(v___x_1024_, 8, v___x_1021_);
lean_ctor_set(v___x_1024_, 9, v___x_1021_);
lean_ctor_set(v___x_1024_, 10, v___x_1021_);
lean_ctor_set(v___x_1024_, 11, v___x_1021_);
lean_ctor_set(v___x_1024_, 12, v___x_1021_);
lean_ctor_set(v___x_1024_, 13, v___x_1021_);
lean_ctor_set(v___x_1024_, 14, v___x_1022_);
lean_ctor_set(v___x_1024_, 15, v___x_1023_);
lean_ctor_set(v___x_1024_, 16, v___x_1023_);
v___f_1025_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1025_, 0, v___x_1024_);
v___x_1026_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1027_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1026_, v___f_1025_, v___y_1005_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1037_; 
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_1027_, 0);
lean_dec(v_unused_1038_);
v___x_1029_ = v___x_1027_;
v_isShared_1030_ = v_isSharedCheck_1037_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v___x_1027_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1037_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1020_);
v___x_1032_ = v___x_997_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1020_);
v___x_1032_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1034_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1032_);
v___x_1034_ = v___x_1029_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_del_object(v___x_997_);
v_a_1039_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1027_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1027_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_a_1016_);
lean_dec_ref(v___x_1003_);
lean_del_object(v___x_997_);
lean_dec(v_val_995_);
lean_dec(v_a_983_);
lean_dec_ref(v_type_970_);
v_a_1047_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1017_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1017_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v___x_1003_);
lean_del_object(v___x_997_);
lean_dec(v_val_995_);
lean_dec(v_a_983_);
lean_dec_ref(v_type_970_);
v_a_1055_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1015_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1015_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_dec(v_a_990_);
lean_dec_ref(v___x_986_);
lean_dec(v_a_983_);
lean_dec_ref(v_type_970_);
v___x_1088_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1088_);
v___x_1090_ = v___x_992_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref(v___x_986_);
lean_dec(v_a_983_);
lean_dec_ref(v_type_970_);
v_a_1093_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_989_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_989_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v_type_970_);
v_a_1101_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_982_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_982_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___boxed(lean_object* v_type_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec(v_a_1110_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(lean_object* v_type_1122_, lean_object* v_a_1123_, lean_object* v_s_1124_){
_start:
{
lean_object* v_rings_1125_; lean_object* v_typeIdOf_1126_; lean_object* v_exprToRingId_1127_; lean_object* v_semirings_1128_; lean_object* v_stypeIdOf_1129_; lean_object* v_exprToSemiringId_1130_; lean_object* v_ncRings_1131_; lean_object* v_exprToNCRingId_1132_; lean_object* v_nctypeIdOf_1133_; lean_object* v_ncSemirings_1134_; lean_object* v_exprToNCSemiringId_1135_; lean_object* v_ncstypeIdOf_1136_; lean_object* v_steps_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1145_; 
v_rings_1125_ = lean_ctor_get(v_s_1124_, 0);
v_typeIdOf_1126_ = lean_ctor_get(v_s_1124_, 1);
v_exprToRingId_1127_ = lean_ctor_get(v_s_1124_, 2);
v_semirings_1128_ = lean_ctor_get(v_s_1124_, 3);
v_stypeIdOf_1129_ = lean_ctor_get(v_s_1124_, 4);
v_exprToSemiringId_1130_ = lean_ctor_get(v_s_1124_, 5);
v_ncRings_1131_ = lean_ctor_get(v_s_1124_, 6);
v_exprToNCRingId_1132_ = lean_ctor_get(v_s_1124_, 7);
v_nctypeIdOf_1133_ = lean_ctor_get(v_s_1124_, 8);
v_ncSemirings_1134_ = lean_ctor_get(v_s_1124_, 9);
v_exprToNCSemiringId_1135_ = lean_ctor_get(v_s_1124_, 10);
v_ncstypeIdOf_1136_ = lean_ctor_get(v_s_1124_, 11);
v_steps_1137_ = lean_ctor_get(v_s_1124_, 12);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_s_1124_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1139_ = v_s_1124_;
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_steps_1137_);
lean_inc(v_ncstypeIdOf_1136_);
lean_inc(v_exprToNCSemiringId_1135_);
lean_inc(v_ncSemirings_1134_);
lean_inc(v_nctypeIdOf_1133_);
lean_inc(v_exprToNCRingId_1132_);
lean_inc(v_ncRings_1131_);
lean_inc(v_exprToSemiringId_1130_);
lean_inc(v_stypeIdOf_1129_);
lean_inc(v_semirings_1128_);
lean_inc(v_exprToRingId_1127_);
lean_inc(v_typeIdOf_1126_);
lean_inc(v_rings_1125_);
lean_dec(v_s_1124_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_nctypeIdOf_1133_, v_type_1122_, v_a_1123_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 8, v___x_1141_);
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_rings_1125_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_typeIdOf_1126_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_exprToRingId_1127_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_semirings_1128_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_stypeIdOf_1129_);
lean_ctor_set(v_reuseFailAlloc_1144_, 5, v_exprToSemiringId_1130_);
lean_ctor_set(v_reuseFailAlloc_1144_, 6, v_ncRings_1131_);
lean_ctor_set(v_reuseFailAlloc_1144_, 7, v_exprToNCRingId_1132_);
lean_ctor_set(v_reuseFailAlloc_1144_, 8, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1144_, 9, v_ncSemirings_1134_);
lean_ctor_set(v_reuseFailAlloc_1144_, 10, v_exprToNCSemiringId_1135_);
lean_ctor_set(v_reuseFailAlloc_1144_, 11, v_ncstypeIdOf_1136_);
lean_ctor_set(v_reuseFailAlloc_1144_, 12, v_steps_1137_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object* v_type_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1147_, v_a_1155_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1190_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1190_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1190_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_nctypeIdOf_1163_; lean_object* v___x_1164_; 
v_nctypeIdOf_1163_ = lean_ctor_get(v_a_1159_, 8);
lean_inc_ref(v_nctypeIdOf_1163_);
lean_dec(v_a_1159_);
v___x_1164_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_nctypeIdOf_1163_, v_type_1146_);
lean_dec_ref(v_nctypeIdOf_1163_);
if (lean_obj_tag(v___x_1164_) == 1)
{
lean_object* v_val_1165_; lean_object* v___x_1167_; 
lean_dec_ref(v_type_1146_);
v_val_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_val_1165_);
lean_dec_ref(v___x_1164_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v_val_1165_);
v___x_1167_ = v___x_1161_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_val_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
else
{
lean_object* v___x_1169_; 
lean_dec(v___x_1164_);
lean_del_object(v___x_1161_);
lean_inc_ref(v_type_1146_);
v___x_1169_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc_n(v_a_1170_, 2);
lean_dec_ref(v___x_1169_);
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1171_, 0, v_type_1146_);
lean_closure_set(v___f_1171_, 1, v_a_1170_);
v___x_1172_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1173_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1172_, v___f_1171_, v_a_1147_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v___x_1173_, 0);
lean_dec(v_unused_1181_);
v___x_1175_ = v___x_1173_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_dec(v___x_1173_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v_a_1170_);
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1170_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_a_1170_);
v_a_1182_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1173_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1173_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_dec_ref(v_type_1146_);
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_type_1146_);
v_a_1191_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1158_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1158_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___boxed(lean_object* v_type_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec(v_a_1200_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(lean_object* v_semiringId_1212_, lean_object* v_s_1213_){
_start:
{
lean_object* v_toRing_1214_; lean_object* v_invFn_x3f_1215_; lean_object* v_commSemiringInst_1216_; lean_object* v_commRingInst_1217_; lean_object* v_noZeroDivInst_x3f_1218_; lean_object* v_fieldInst_x3f_1219_; lean_object* v_powIdentityInst_x3f_1220_; lean_object* v_denoteEntries_1221_; lean_object* v_nextId_1222_; lean_object* v_steps_1223_; lean_object* v_queue_1224_; lean_object* v_basis_1225_; lean_object* v_diseqs_1226_; uint8_t v_recheck_1227_; lean_object* v_invSet_1228_; lean_object* v_powIdentityVarCount_1229_; lean_object* v_numEq0_x3f_1230_; uint8_t v_numEq0Updated_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1239_; 
v_toRing_1214_ = lean_ctor_get(v_s_1213_, 0);
v_invFn_x3f_1215_ = lean_ctor_get(v_s_1213_, 1);
v_commSemiringInst_1216_ = lean_ctor_get(v_s_1213_, 3);
v_commRingInst_1217_ = lean_ctor_get(v_s_1213_, 4);
v_noZeroDivInst_x3f_1218_ = lean_ctor_get(v_s_1213_, 5);
v_fieldInst_x3f_1219_ = lean_ctor_get(v_s_1213_, 6);
v_powIdentityInst_x3f_1220_ = lean_ctor_get(v_s_1213_, 7);
v_denoteEntries_1221_ = lean_ctor_get(v_s_1213_, 8);
v_nextId_1222_ = lean_ctor_get(v_s_1213_, 9);
v_steps_1223_ = lean_ctor_get(v_s_1213_, 10);
v_queue_1224_ = lean_ctor_get(v_s_1213_, 11);
v_basis_1225_ = lean_ctor_get(v_s_1213_, 12);
v_diseqs_1226_ = lean_ctor_get(v_s_1213_, 13);
v_recheck_1227_ = lean_ctor_get_uint8(v_s_1213_, sizeof(void*)*17);
v_invSet_1228_ = lean_ctor_get(v_s_1213_, 14);
v_powIdentityVarCount_1229_ = lean_ctor_get(v_s_1213_, 15);
v_numEq0_x3f_1230_ = lean_ctor_get(v_s_1213_, 16);
v_numEq0Updated_1231_ = lean_ctor_get_uint8(v_s_1213_, sizeof(void*)*17 + 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_s_1213_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v_s_1213_, 2);
lean_dec(v_unused_1240_);
v___x_1233_ = v_s_1213_;
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_numEq0_x3f_1230_);
lean_inc(v_powIdentityVarCount_1229_);
lean_inc(v_invSet_1228_);
lean_inc(v_diseqs_1226_);
lean_inc(v_basis_1225_);
lean_inc(v_queue_1224_);
lean_inc(v_steps_1223_);
lean_inc(v_nextId_1222_);
lean_inc(v_denoteEntries_1221_);
lean_inc(v_powIdentityInst_x3f_1220_);
lean_inc(v_fieldInst_x3f_1219_);
lean_inc(v_noZeroDivInst_x3f_1218_);
lean_inc(v_commRingInst_1217_);
lean_inc(v_commSemiringInst_1216_);
lean_inc(v_invFn_x3f_1215_);
lean_inc(v_toRing_1214_);
lean_dec(v_s_1213_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_semiringId_1212_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 2, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_toRing_1214_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_invFn_x3f_1215_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_commSemiringInst_1216_);
lean_ctor_set(v_reuseFailAlloc_1238_, 4, v_commRingInst_1217_);
lean_ctor_set(v_reuseFailAlloc_1238_, 5, v_noZeroDivInst_x3f_1218_);
lean_ctor_set(v_reuseFailAlloc_1238_, 6, v_fieldInst_x3f_1219_);
lean_ctor_set(v_reuseFailAlloc_1238_, 7, v_powIdentityInst_x3f_1220_);
lean_ctor_set(v_reuseFailAlloc_1238_, 8, v_denoteEntries_1221_);
lean_ctor_set(v_reuseFailAlloc_1238_, 9, v_nextId_1222_);
lean_ctor_set(v_reuseFailAlloc_1238_, 10, v_steps_1223_);
lean_ctor_set(v_reuseFailAlloc_1238_, 11, v_queue_1224_);
lean_ctor_set(v_reuseFailAlloc_1238_, 12, v_basis_1225_);
lean_ctor_set(v_reuseFailAlloc_1238_, 13, v_diseqs_1226_);
lean_ctor_set(v_reuseFailAlloc_1238_, 14, v_invSet_1228_);
lean_ctor_set(v_reuseFailAlloc_1238_, 15, v_powIdentityVarCount_1229_);
lean_ctor_set(v_reuseFailAlloc_1238_, 16, v_numEq0_x3f_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*17, v_recheck_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*17 + 1, v_numEq0Updated_1231_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(lean_object* v_ringId_1241_, lean_object* v_semiringId_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___f_1245_; uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___f_1245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1245_, 0, v_semiringId_1242_);
v___x_1246_ = 0;
v___x_1247_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1247_, 0, v_ringId_1241_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*1, v___x_1246_);
v___x_1248_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1245_, v___x_1247_, v_a_1243_);
lean_dec_ref(v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(lean_object* v_ringId_1249_, lean_object* v_semiringId_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_1249_, v_semiringId_1250_, v_a_1251_);
lean_dec(v_a_1251_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(lean_object* v_ringId_1254_, lean_object* v_semiringId_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_1254_, v_semiringId_1255_, v_a_1256_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(lean_object* v_ringId_1268_, lean_object* v_semiringId_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(v_ringId_1268_, v_semiringId_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(lean_object* v___x_1282_, lean_object* v_s_1283_){
_start:
{
lean_object* v_rings_1284_; lean_object* v_typeIdOf_1285_; lean_object* v_exprToRingId_1286_; lean_object* v_semirings_1287_; lean_object* v_stypeIdOf_1288_; lean_object* v_exprToSemiringId_1289_; lean_object* v_ncRings_1290_; lean_object* v_exprToNCRingId_1291_; lean_object* v_nctypeIdOf_1292_; lean_object* v_ncSemirings_1293_; lean_object* v_exprToNCSemiringId_1294_; lean_object* v_ncstypeIdOf_1295_; lean_object* v_steps_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1304_; 
v_rings_1284_ = lean_ctor_get(v_s_1283_, 0);
v_typeIdOf_1285_ = lean_ctor_get(v_s_1283_, 1);
v_exprToRingId_1286_ = lean_ctor_get(v_s_1283_, 2);
v_semirings_1287_ = lean_ctor_get(v_s_1283_, 3);
v_stypeIdOf_1288_ = lean_ctor_get(v_s_1283_, 4);
v_exprToSemiringId_1289_ = lean_ctor_get(v_s_1283_, 5);
v_ncRings_1290_ = lean_ctor_get(v_s_1283_, 6);
v_exprToNCRingId_1291_ = lean_ctor_get(v_s_1283_, 7);
v_nctypeIdOf_1292_ = lean_ctor_get(v_s_1283_, 8);
v_ncSemirings_1293_ = lean_ctor_get(v_s_1283_, 9);
v_exprToNCSemiringId_1294_ = lean_ctor_get(v_s_1283_, 10);
v_ncstypeIdOf_1295_ = lean_ctor_get(v_s_1283_, 11);
v_steps_1296_ = lean_ctor_get(v_s_1283_, 12);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_s_1283_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1298_ = v_s_1283_;
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_steps_1296_);
lean_inc(v_ncstypeIdOf_1295_);
lean_inc(v_exprToNCSemiringId_1294_);
lean_inc(v_ncSemirings_1293_);
lean_inc(v_nctypeIdOf_1292_);
lean_inc(v_exprToNCRingId_1291_);
lean_inc(v_ncRings_1290_);
lean_inc(v_exprToSemiringId_1289_);
lean_inc(v_stypeIdOf_1288_);
lean_inc(v_semirings_1287_);
lean_inc(v_exprToRingId_1286_);
lean_inc(v_typeIdOf_1285_);
lean_inc(v_rings_1284_);
lean_dec(v_s_1283_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1300_ = lean_array_push(v_semirings_1287_, v___x_1282_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 3, v___x_1300_);
v___x_1302_ = v___x_1298_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_rings_1284_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_typeIdOf_1285_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_exprToRingId_1286_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_stypeIdOf_1288_);
lean_ctor_set(v_reuseFailAlloc_1303_, 5, v_exprToSemiringId_1289_);
lean_ctor_set(v_reuseFailAlloc_1303_, 6, v_ncRings_1290_);
lean_ctor_set(v_reuseFailAlloc_1303_, 7, v_exprToNCRingId_1291_);
lean_ctor_set(v_reuseFailAlloc_1303_, 8, v_nctypeIdOf_1292_);
lean_ctor_set(v_reuseFailAlloc_1303_, 9, v_ncSemirings_1293_);
lean_ctor_set(v_reuseFailAlloc_1303_, 10, v_exprToNCSemiringId_1294_);
lean_ctor_set(v_reuseFailAlloc_1303_, 11, v_ncstypeIdOf_1295_);
lean_ctor_set(v_reuseFailAlloc_1303_, 12, v_steps_1296_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_ref_1311_; lean_object* v___x_1312_; lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1321_; 
v_ref_1311_ = lean_ctor_get(v___y_1308_, 5);
v___x_1312_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_inc(v_ref_1311_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v_ref_1311_);
lean_ctor_set(v___x_1317_, 1, v_a_1313_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set_tag(v___x_1315_, 1);
lean_ctor_set(v___x_1315_, 0, v___x_1317_);
v___x_1319_ = v___x_1315_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8));
v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(lean_object* v_type_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___x_1365_; 
lean_inc_ref(v_type_1353_);
v___x_1365_ = l_Lean_Meta_getDecLevel(v_type_1353_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc_n(v_a_1366_, 2);
lean_dec_ref(v___x_1365_);
v___x_1367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1));
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_a_1366_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
lean_inc_ref(v___x_1369_);
v___x_1370_ = l_Lean_mkConst(v___x_1367_, v___x_1369_);
lean_inc_ref(v_type_1353_);
v___x_1371_ = l_Lean_Expr_app___override(v___x_1370_, v_type_1353_);
v___x_1372_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1371_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1467_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1467_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1467_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
if (lean_obj_tag(v_a_1373_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_del_object(v___x_1375_);
v_val_1377_ = lean_ctor_get(v_a_1373_, 0);
lean_inc_n(v_val_1377_, 2);
lean_dec_ref(v_a_1373_);
v___x_1378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2));
lean_inc_ref(v___x_1369_);
v___x_1379_ = l_Lean_mkConst(v___x_1378_, v___x_1369_);
lean_inc_ref_n(v_type_1353_, 2);
v___x_1380_ = l_Lean_mkAppB(v___x_1379_, v_type_1353_, v_val_1377_);
v___x_1381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5));
v___x_1382_ = l_Lean_mkConst(v___x_1381_, v___x_1369_);
lean_inc_ref(v___x_1380_);
v___x_1383_ = l_Lean_mkAppB(v___x_1382_, v_type_1353_, v___x_1380_);
v___x_1384_ = l_Lean_Meta_Sym_canon(v___x_1383_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1385_, v_a_1359_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc_n(v_a_1387_, 2);
lean_dec_ref(v___x_1386_);
v___x_1388_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_a_1387_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref(v___x_1388_);
if (lean_obj_tag(v_a_1389_) == 1)
{
lean_object* v_val_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_a_1387_);
v_val_1390_ = lean_ctor_get(v_a_1389_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_a_1389_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1392_ = v_a_1389_;
v_isShared_1393_ = v_isSharedCheck_1442_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_val_1390_);
lean_dec(v_a_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1442_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1354_, v_a_1362_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v_semirings_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
v_semirings_1396_ = lean_ctor_get(v_a_1395_, 3);
lean_inc_ref(v_semirings_1396_);
lean_dec(v_a_1395_);
v___x_1397_ = lean_array_get_size(v_semirings_1396_);
lean_dec_ref(v_semirings_1396_);
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
v___x_1400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
v___x_1401_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1397_);
lean_ctor_set(v___x_1401_, 1, v_type_1353_);
lean_ctor_set(v___x_1401_, 2, v_a_1366_);
lean_ctor_set(v___x_1401_, 3, v___x_1380_);
lean_ctor_set(v___x_1401_, 4, v___x_1398_);
lean_ctor_set(v___x_1401_, 5, v___x_1398_);
lean_ctor_set(v___x_1401_, 6, v___x_1398_);
lean_ctor_set(v___x_1401_, 7, v___x_1398_);
lean_ctor_set(v___x_1401_, 8, v___x_1399_);
lean_ctor_set(v___x_1401_, 9, v___x_1400_);
lean_ctor_set(v___x_1401_, 10, v___x_1399_);
lean_inc(v_val_1390_);
v___x_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
lean_ctor_set(v___x_1402_, 1, v_val_1390_);
lean_ctor_set(v___x_1402_, 2, v_val_1377_);
lean_ctor_set(v___x_1402_, 3, v___x_1398_);
lean_ctor_set(v___x_1402_, 4, v___x_1398_);
v___f_1403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1403_, 0, v___x_1402_);
v___x_1404_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1405_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1404_, v___f_1403_, v_a_1354_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v___x_1405_);
v___x_1406_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_val_1390_, v___x_1397_, v_a_1354_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1416_; 
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; 
v_unused_1417_ = lean_ctor_get(v___x_1406_, 0);
lean_dec(v_unused_1417_);
v___x_1408_ = v___x_1406_;
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
else
{
lean_dec(v___x_1406_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1397_);
v___x_1411_ = v___x_1392_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1397_);
v___x_1411_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1411_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_del_object(v___x_1392_);
v_a_1418_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1406_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1406_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_del_object(v___x_1392_);
lean_dec(v_val_1390_);
v_a_1426_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1405_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1405_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_del_object(v___x_1392_);
lean_dec(v_val_1390_);
lean_dec_ref(v___x_1380_);
lean_dec(v_val_1377_);
lean_dec(v_a_1366_);
lean_dec_ref(v_type_1353_);
v_a_1434_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1394_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1394_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
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
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec(v_a_1389_);
lean_dec_ref(v___x_1380_);
lean_dec(v_val_1377_);
lean_dec(v_a_1366_);
lean_dec_ref(v_type_1353_);
v___x_1443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9);
v___x_1444_ = l_Lean_indentExpr(v_a_1387_);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v___x_1445_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
return v___x_1446_;
}
}
else
{
lean_dec(v_a_1387_);
lean_dec_ref(v___x_1380_);
lean_dec(v_val_1377_);
lean_dec(v_a_1366_);
lean_dec_ref(v_type_1353_);
return v___x_1388_;
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v___x_1380_);
lean_dec(v_val_1377_);
lean_dec(v_a_1366_);
lean_dec_ref(v_type_1353_);
v_a_1447_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1386_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1386_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref(v___x_1380_);
lean_dec(v_val_1377_);
lean_dec(v_a_1366_);
lean_dec_ref(v_type_1353_);
v_a_1455_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1384_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1384_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
lean_dec(v_a_1373_);
lean_dec_ref(v___x_1369_);
lean_dec(v_a_1366_);
lean_dec_ref(v_type_1353_);
v___x_1463_ = lean_box(0);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1463_);
v___x_1465_ = v___x_1375_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v___x_1369_);
lean_dec(v_a_1366_);
lean_dec_ref(v_type_1353_);
v_a_1468_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1372_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1372_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v_type_1353_);
v_a_1476_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1365_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1365_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec(v_a_1485_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_1497_, lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_1498_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_msg_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(v_00_u03b1_1511_, v_msg_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(lean_object* v_type_1525_, lean_object* v_a_1526_, lean_object* v_s_1527_){
_start:
{
lean_object* v_rings_1528_; lean_object* v_typeIdOf_1529_; lean_object* v_exprToRingId_1530_; lean_object* v_semirings_1531_; lean_object* v_stypeIdOf_1532_; lean_object* v_exprToSemiringId_1533_; lean_object* v_ncRings_1534_; lean_object* v_exprToNCRingId_1535_; lean_object* v_nctypeIdOf_1536_; lean_object* v_ncSemirings_1537_; lean_object* v_exprToNCSemiringId_1538_; lean_object* v_ncstypeIdOf_1539_; lean_object* v_steps_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1548_; 
v_rings_1528_ = lean_ctor_get(v_s_1527_, 0);
v_typeIdOf_1529_ = lean_ctor_get(v_s_1527_, 1);
v_exprToRingId_1530_ = lean_ctor_get(v_s_1527_, 2);
v_semirings_1531_ = lean_ctor_get(v_s_1527_, 3);
v_stypeIdOf_1532_ = lean_ctor_get(v_s_1527_, 4);
v_exprToSemiringId_1533_ = lean_ctor_get(v_s_1527_, 5);
v_ncRings_1534_ = lean_ctor_get(v_s_1527_, 6);
v_exprToNCRingId_1535_ = lean_ctor_get(v_s_1527_, 7);
v_nctypeIdOf_1536_ = lean_ctor_get(v_s_1527_, 8);
v_ncSemirings_1537_ = lean_ctor_get(v_s_1527_, 9);
v_exprToNCSemiringId_1538_ = lean_ctor_get(v_s_1527_, 10);
v_ncstypeIdOf_1539_ = lean_ctor_get(v_s_1527_, 11);
v_steps_1540_ = lean_ctor_get(v_s_1527_, 12);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_s_1527_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1542_ = v_s_1527_;
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_steps_1540_);
lean_inc(v_ncstypeIdOf_1539_);
lean_inc(v_exprToNCSemiringId_1538_);
lean_inc(v_ncSemirings_1537_);
lean_inc(v_nctypeIdOf_1536_);
lean_inc(v_exprToNCRingId_1535_);
lean_inc(v_ncRings_1534_);
lean_inc(v_exprToSemiringId_1533_);
lean_inc(v_stypeIdOf_1532_);
lean_inc(v_semirings_1531_);
lean_inc(v_exprToRingId_1530_);
lean_inc(v_typeIdOf_1529_);
lean_inc(v_rings_1528_);
lean_dec(v_s_1527_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_stypeIdOf_1532_, v_type_1525_, v_a_1526_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 4, v___x_1544_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_rings_1528_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_typeIdOf_1529_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_exprToRingId_1530_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_semirings_1531_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1547_, 5, v_exprToSemiringId_1533_);
lean_ctor_set(v_reuseFailAlloc_1547_, 6, v_ncRings_1534_);
lean_ctor_set(v_reuseFailAlloc_1547_, 7, v_exprToNCRingId_1535_);
lean_ctor_set(v_reuseFailAlloc_1547_, 8, v_nctypeIdOf_1536_);
lean_ctor_set(v_reuseFailAlloc_1547_, 9, v_ncSemirings_1537_);
lean_ctor_set(v_reuseFailAlloc_1547_, 10, v_exprToNCSemiringId_1538_);
lean_ctor_set(v_reuseFailAlloc_1547_, 11, v_ncstypeIdOf_1539_);
lean_ctor_set(v_reuseFailAlloc_1547_, 12, v_steps_1540_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object* v_type_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1550_, v_a_1558_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1593_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1593_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1593_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_stypeIdOf_1566_; lean_object* v___x_1567_; 
v_stypeIdOf_1566_ = lean_ctor_get(v_a_1562_, 4);
lean_inc_ref(v_stypeIdOf_1566_);
lean_dec(v_a_1562_);
v___x_1567_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_stypeIdOf_1566_, v_type_1549_);
lean_dec_ref(v_stypeIdOf_1566_);
if (lean_obj_tag(v___x_1567_) == 1)
{
lean_object* v_val_1568_; lean_object* v___x_1570_; 
lean_dec_ref(v_type_1549_);
v_val_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_val_1568_);
lean_dec_ref(v___x_1567_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v_val_1568_);
v___x_1570_ = v___x_1564_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_val_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
else
{
lean_object* v___x_1572_; 
lean_dec(v___x_1567_);
lean_del_object(v___x_1564_);
lean_inc_ref(v_type_1549_);
v___x_1572_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_n(v_a_1573_, 2);
lean_dec_ref(v___x_1572_);
v___f_1574_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1574_, 0, v_type_1549_);
lean_closure_set(v___f_1574_, 1, v_a_1573_);
v___x_1575_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1576_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1575_, v___f_1574_, v_a_1550_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v___x_1576_, 0);
lean_dec(v_unused_1584_);
v___x_1578_ = v___x_1576_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_dec(v___x_1576_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v_a_1573_);
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1573_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_a_1573_);
v_a_1585_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1576_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1576_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_dec_ref(v_type_1549_);
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v_type_1549_);
v_a_1594_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1561_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1561_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___boxed(lean_object* v_type_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_type_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec(v_a_1603_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(lean_object* v___x_1615_, lean_object* v_s_1616_){
_start:
{
lean_object* v_rings_1617_; lean_object* v_typeIdOf_1618_; lean_object* v_exprToRingId_1619_; lean_object* v_semirings_1620_; lean_object* v_stypeIdOf_1621_; lean_object* v_exprToSemiringId_1622_; lean_object* v_ncRings_1623_; lean_object* v_exprToNCRingId_1624_; lean_object* v_nctypeIdOf_1625_; lean_object* v_ncSemirings_1626_; lean_object* v_exprToNCSemiringId_1627_; lean_object* v_ncstypeIdOf_1628_; lean_object* v_steps_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1637_; 
v_rings_1617_ = lean_ctor_get(v_s_1616_, 0);
v_typeIdOf_1618_ = lean_ctor_get(v_s_1616_, 1);
v_exprToRingId_1619_ = lean_ctor_get(v_s_1616_, 2);
v_semirings_1620_ = lean_ctor_get(v_s_1616_, 3);
v_stypeIdOf_1621_ = lean_ctor_get(v_s_1616_, 4);
v_exprToSemiringId_1622_ = lean_ctor_get(v_s_1616_, 5);
v_ncRings_1623_ = lean_ctor_get(v_s_1616_, 6);
v_exprToNCRingId_1624_ = lean_ctor_get(v_s_1616_, 7);
v_nctypeIdOf_1625_ = lean_ctor_get(v_s_1616_, 8);
v_ncSemirings_1626_ = lean_ctor_get(v_s_1616_, 9);
v_exprToNCSemiringId_1627_ = lean_ctor_get(v_s_1616_, 10);
v_ncstypeIdOf_1628_ = lean_ctor_get(v_s_1616_, 11);
v_steps_1629_ = lean_ctor_get(v_s_1616_, 12);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_s_1616_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1631_ = v_s_1616_;
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_steps_1629_);
lean_inc(v_ncstypeIdOf_1628_);
lean_inc(v_exprToNCSemiringId_1627_);
lean_inc(v_ncSemirings_1626_);
lean_inc(v_nctypeIdOf_1625_);
lean_inc(v_exprToNCRingId_1624_);
lean_inc(v_ncRings_1623_);
lean_inc(v_exprToSemiringId_1622_);
lean_inc(v_stypeIdOf_1621_);
lean_inc(v_semirings_1620_);
lean_inc(v_exprToRingId_1619_);
lean_inc(v_typeIdOf_1618_);
lean_inc(v_rings_1617_);
lean_dec(v_s_1616_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = lean_array_push(v_ncSemirings_1626_, v___x_1615_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 9, v___x_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_rings_1617_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_typeIdOf_1618_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_exprToRingId_1619_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_semirings_1620_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_stypeIdOf_1621_);
lean_ctor_set(v_reuseFailAlloc_1636_, 5, v_exprToSemiringId_1622_);
lean_ctor_set(v_reuseFailAlloc_1636_, 6, v_ncRings_1623_);
lean_ctor_set(v_reuseFailAlloc_1636_, 7, v_exprToNCRingId_1624_);
lean_ctor_set(v_reuseFailAlloc_1636_, 8, v_nctypeIdOf_1625_);
lean_ctor_set(v_reuseFailAlloc_1636_, 9, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1636_, 10, v_exprToNCSemiringId_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 11, v_ncstypeIdOf_1628_);
lean_ctor_set(v_reuseFailAlloc_1636_, 12, v_steps_1629_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(lean_object* v_type_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
lean_inc_ref(v_type_1643_);
v___x_1650_ = l_Lean_Meta_getDecLevel(v_type_1643_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc_n(v_a_1651_, 2);
lean_dec_ref(v___x_1650_);
v___x_1652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1));
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1651_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_mkConst(v___x_1652_, v___x_1654_);
lean_inc_ref(v_type_1643_);
v___x_1656_ = l_Lean_Expr_app___override(v___x_1655_, v_type_1643_);
v___x_1657_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1656_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1709_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1709_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1709_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
if (lean_obj_tag(v_a_1658_) == 1)
{
lean_object* v_val_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1704_; 
lean_del_object(v___x_1660_);
v_val_1662_ = lean_ctor_get(v_a_1658_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_a_1658_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1664_ = v_a_1658_;
v_isShared_1665_ = v_isSharedCheck_1704_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_val_1662_);
lean_dec(v_a_1658_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1704_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1644_, v_a_1647_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v_ncSemirings_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v___x_1666_);
v_ncSemirings_1668_ = lean_ctor_get(v_a_1667_, 9);
lean_inc_ref(v_ncSemirings_1668_);
lean_dec(v_a_1667_);
v___x_1669_ = lean_array_get_size(v_ncSemirings_1668_);
lean_dec_ref(v_ncSemirings_1668_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
v___x_1672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
v___x_1673_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1669_);
lean_ctor_set(v___x_1673_, 1, v_type_1643_);
lean_ctor_set(v___x_1673_, 2, v_a_1651_);
lean_ctor_set(v___x_1673_, 3, v_val_1662_);
lean_ctor_set(v___x_1673_, 4, v___x_1670_);
lean_ctor_set(v___x_1673_, 5, v___x_1670_);
lean_ctor_set(v___x_1673_, 6, v___x_1670_);
lean_ctor_set(v___x_1673_, 7, v___x_1670_);
lean_ctor_set(v___x_1673_, 8, v___x_1671_);
lean_ctor_set(v___x_1673_, 9, v___x_1672_);
lean_ctor_set(v___x_1673_, 10, v___x_1671_);
v___f_1674_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1674_, 0, v___x_1673_);
v___x_1675_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1676_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1675_, v___f_1674_, v_a_1644_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1686_; 
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v___x_1676_, 0);
lean_dec(v_unused_1687_);
v___x_1678_ = v___x_1676_;
v_isShared_1679_ = v_isSharedCheck_1686_;
goto v_resetjp_1677_;
}
else
{
lean_dec(v___x_1676_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1686_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1669_);
v___x_1681_ = v___x_1664_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1669_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_del_object(v___x_1664_);
v_a_1688_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1676_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1676_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_del_object(v___x_1664_);
lean_dec(v_val_1662_);
lean_dec(v_a_1651_);
lean_dec_ref(v_type_1643_);
v_a_1696_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1666_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1666_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_dec(v_a_1658_);
lean_dec(v_a_1651_);
lean_dec_ref(v_type_1643_);
v___x_1705_ = lean_box(0);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1705_);
v___x_1707_ = v___x_1660_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v_a_1651_);
lean_dec_ref(v_type_1643_);
v_a_1710_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1657_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1657_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v_type_1643_);
v_a_1718_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1650_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1650_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___boxed(lean_object* v_type_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(lean_object* v_type_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_1734_, v_a_1735_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(v_type_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec(v_a_1748_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(lean_object* v_type_1760_, lean_object* v_a_1761_, lean_object* v_s_1762_){
_start:
{
lean_object* v_rings_1763_; lean_object* v_typeIdOf_1764_; lean_object* v_exprToRingId_1765_; lean_object* v_semirings_1766_; lean_object* v_stypeIdOf_1767_; lean_object* v_exprToSemiringId_1768_; lean_object* v_ncRings_1769_; lean_object* v_exprToNCRingId_1770_; lean_object* v_nctypeIdOf_1771_; lean_object* v_ncSemirings_1772_; lean_object* v_exprToNCSemiringId_1773_; lean_object* v_ncstypeIdOf_1774_; lean_object* v_steps_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1783_; 
v_rings_1763_ = lean_ctor_get(v_s_1762_, 0);
v_typeIdOf_1764_ = lean_ctor_get(v_s_1762_, 1);
v_exprToRingId_1765_ = lean_ctor_get(v_s_1762_, 2);
v_semirings_1766_ = lean_ctor_get(v_s_1762_, 3);
v_stypeIdOf_1767_ = lean_ctor_get(v_s_1762_, 4);
v_exprToSemiringId_1768_ = lean_ctor_get(v_s_1762_, 5);
v_ncRings_1769_ = lean_ctor_get(v_s_1762_, 6);
v_exprToNCRingId_1770_ = lean_ctor_get(v_s_1762_, 7);
v_nctypeIdOf_1771_ = lean_ctor_get(v_s_1762_, 8);
v_ncSemirings_1772_ = lean_ctor_get(v_s_1762_, 9);
v_exprToNCSemiringId_1773_ = lean_ctor_get(v_s_1762_, 10);
v_ncstypeIdOf_1774_ = lean_ctor_get(v_s_1762_, 11);
v_steps_1775_ = lean_ctor_get(v_s_1762_, 12);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_s_1762_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1777_ = v_s_1762_;
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_steps_1775_);
lean_inc(v_ncstypeIdOf_1774_);
lean_inc(v_exprToNCSemiringId_1773_);
lean_inc(v_ncSemirings_1772_);
lean_inc(v_nctypeIdOf_1771_);
lean_inc(v_exprToNCRingId_1770_);
lean_inc(v_ncRings_1769_);
lean_inc(v_exprToSemiringId_1768_);
lean_inc(v_stypeIdOf_1767_);
lean_inc(v_semirings_1766_);
lean_inc(v_exprToRingId_1765_);
lean_inc(v_typeIdOf_1764_);
lean_inc(v_rings_1763_);
lean_dec(v_s_1762_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_ncstypeIdOf_1774_, v_type_1760_, v_a_1761_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 11, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_rings_1763_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_typeIdOf_1764_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_exprToRingId_1765_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_semirings_1766_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v_stypeIdOf_1767_);
lean_ctor_set(v_reuseFailAlloc_1782_, 5, v_exprToSemiringId_1768_);
lean_ctor_set(v_reuseFailAlloc_1782_, 6, v_ncRings_1769_);
lean_ctor_set(v_reuseFailAlloc_1782_, 7, v_exprToNCRingId_1770_);
lean_ctor_set(v_reuseFailAlloc_1782_, 8, v_nctypeIdOf_1771_);
lean_ctor_set(v_reuseFailAlloc_1782_, 9, v_ncSemirings_1772_);
lean_ctor_set(v_reuseFailAlloc_1782_, 10, v_exprToNCSemiringId_1773_);
lean_ctor_set(v_reuseFailAlloc_1782_, 11, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1782_, 12, v_steps_1775_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object* v_type_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1785_, v_a_1788_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1823_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1823_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1823_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_ncstypeIdOf_1796_; lean_object* v___x_1797_; 
v_ncstypeIdOf_1796_ = lean_ctor_get(v_a_1792_, 11);
lean_inc_ref(v_ncstypeIdOf_1796_);
lean_dec(v_a_1792_);
v___x_1797_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_ncstypeIdOf_1796_, v_type_1784_);
lean_dec_ref(v_ncstypeIdOf_1796_);
if (lean_obj_tag(v___x_1797_) == 1)
{
lean_object* v_val_1798_; lean_object* v___x_1800_; 
lean_dec_ref(v_type_1784_);
v_val_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_val_1798_);
lean_dec_ref(v___x_1797_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v_val_1798_);
v___x_1800_ = v___x_1794_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_val_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
else
{
lean_object* v___x_1802_; 
lean_dec(v___x_1797_);
lean_del_object(v___x_1794_);
lean_inc_ref(v_type_1784_);
v___x_1802_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___f_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc_n(v_a_1803_, 2);
lean_dec_ref(v___x_1802_);
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1804_, 0, v_type_1784_);
lean_closure_set(v___f_1804_, 1, v_a_1803_);
v___x_1805_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1806_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1805_, v___f_1804_, v_a_1785_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1806_, 0);
lean_dec(v_unused_1814_);
v___x_1808_ = v___x_1806_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v___x_1806_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v_a_1803_);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1803_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec(v_a_1803_);
v_a_1815_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1806_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1806_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
else
{
lean_dec_ref(v_type_1784_);
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v_type_1784_);
v_a_1824_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1791_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1791_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___boxed(lean_object* v_type_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(lean_object* v_type_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_1840_, v_a_1841_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___boxed(lean_object* v_type_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(v_type_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec(v_a_1854_);
return v_res_1865_;
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
