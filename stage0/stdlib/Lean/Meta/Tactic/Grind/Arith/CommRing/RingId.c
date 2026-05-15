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
lean_object* v_rings_47_; lean_object* v_typeIdOf_48_; lean_object* v_exprToRingId_49_; lean_object* v_semirings_50_; lean_object* v_stypeIdOf_51_; lean_object* v_exprToSemiringId_52_; lean_object* v_ncRings_53_; lean_object* v_exprToNCRingId_54_; lean_object* v_nctypeIdOf_55_; lean_object* v_ncSemirings_56_; lean_object* v_exprToNCSemiringId_57_; lean_object* v_ncstypeIdOf_58_; lean_object* v_steps_59_; uint8_t v_reportedMaxDegreeIssue_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_68_; 
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
v_reportedMaxDegreeIssue_60_ = lean_ctor_get_uint8(v_s_46_, sizeof(void*)*13);
v_isSharedCheck_68_ = !lean_is_exclusive(v_s_46_);
if (v_isSharedCheck_68_ == 0)
{
v___x_62_ = v_s_46_;
v_isShared_63_ = v_isSharedCheck_68_;
goto v_resetjp_61_;
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
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_68_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_64_ = lean_array_push(v_rings_47_, v___x_45_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_64_);
v___x_66_ = v___x_62_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_typeIdOf_48_);
lean_ctor_set(v_reuseFailAlloc_67_, 2, v_exprToRingId_49_);
lean_ctor_set(v_reuseFailAlloc_67_, 3, v_semirings_50_);
lean_ctor_set(v_reuseFailAlloc_67_, 4, v_stypeIdOf_51_);
lean_ctor_set(v_reuseFailAlloc_67_, 5, v_exprToSemiringId_52_);
lean_ctor_set(v_reuseFailAlloc_67_, 6, v_ncRings_53_);
lean_ctor_set(v_reuseFailAlloc_67_, 7, v_exprToNCRingId_54_);
lean_ctor_set(v_reuseFailAlloc_67_, 8, v_nctypeIdOf_55_);
lean_ctor_set(v_reuseFailAlloc_67_, 9, v_ncSemirings_56_);
lean_ctor_set(v_reuseFailAlloc_67_, 10, v_exprToNCSemiringId_57_);
lean_ctor_set(v_reuseFailAlloc_67_, 11, v_ncstypeIdOf_58_);
lean_ctor_set(v_reuseFailAlloc_67_, 12, v_steps_59_);
lean_ctor_set_uint8(v_reuseFailAlloc_67_, sizeof(void*)*13, v_reportedMaxDegreeIssue_60_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(lean_object* v_msgData_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v_env_76_; lean_object* v___x_77_; lean_object* v_mctx_78_; lean_object* v_lctx_79_; lean_object* v_options_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_75_ = lean_st_ref_get(v___y_73_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_env_76_);
lean_dec(v___x_75_);
v___x_77_ = lean_st_ref_get(v___y_71_);
v_mctx_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref(v_mctx_78_);
lean_dec(v___x_77_);
v_lctx_79_ = lean_ctor_get(v___y_70_, 2);
v_options_80_ = lean_ctor_get(v___y_72_, 2);
lean_inc_ref(v_options_80_);
lean_inc_ref(v_lctx_79_);
v___x_81_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_81_, 0, v_env_76_);
lean_ctor_set(v___x_81_, 1, v_mctx_78_);
lean_ctor_set(v___x_81_, 2, v_lctx_79_);
lean_ctor_set(v___x_81_, 3, v_options_80_);
v___x_82_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_msgData_69_);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1___boxed(lean_object* v_msgData_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msgData_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
return v_res_90_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_91_; double v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_float_of_nat(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(lean_object* v_cls_96_, lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_ref_103_; lean_object* v___x_104_; lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_149_; 
v_ref_103_ = lean_ctor_get(v___y_100_, 5);
v___x_104_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_149_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_149_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_149_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v_traceState_110_; lean_object* v_env_111_; lean_object* v_nextMacroScope_112_; lean_object* v_ngen_113_; lean_object* v_auxDeclNGen_114_; lean_object* v_cache_115_; lean_object* v_messages_116_; lean_object* v_infoState_117_; lean_object* v_snapshotTasks_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_148_; 
v___x_109_ = lean_st_ref_take(v___y_101_);
v_traceState_110_ = lean_ctor_get(v___x_109_, 4);
v_env_111_ = lean_ctor_get(v___x_109_, 0);
v_nextMacroScope_112_ = lean_ctor_get(v___x_109_, 1);
v_ngen_113_ = lean_ctor_get(v___x_109_, 2);
v_auxDeclNGen_114_ = lean_ctor_get(v___x_109_, 3);
v_cache_115_ = lean_ctor_get(v___x_109_, 5);
v_messages_116_ = lean_ctor_get(v___x_109_, 6);
v_infoState_117_ = lean_ctor_get(v___x_109_, 7);
v_snapshotTasks_118_ = lean_ctor_get(v___x_109_, 8);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_148_ == 0)
{
v___x_120_ = v___x_109_;
v_isShared_121_ = v_isSharedCheck_148_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snapshotTasks_118_);
lean_inc(v_infoState_117_);
lean_inc(v_messages_116_);
lean_inc(v_cache_115_);
lean_inc(v_traceState_110_);
lean_inc(v_auxDeclNGen_114_);
lean_inc(v_ngen_113_);
lean_inc(v_nextMacroScope_112_);
lean_inc(v_env_111_);
lean_dec(v___x_109_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_148_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
uint64_t v_tid_122_; lean_object* v_traces_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_147_; 
v_tid_122_ = lean_ctor_get_uint64(v_traceState_110_, sizeof(void*)*1);
v_traces_123_ = lean_ctor_get(v_traceState_110_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_traceState_110_);
if (v_isSharedCheck_147_ == 0)
{
v___x_125_ = v_traceState_110_;
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_traces_123_);
lean_dec(v_traceState_110_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; double v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_127_ = lean_box(0);
v___x_128_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0);
v___x_129_ = 0;
v___x_130_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1));
v___x_131_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_131_, 0, v_cls_96_);
lean_ctor_set(v___x_131_, 1, v___x_127_);
lean_ctor_set(v___x_131_, 2, v___x_130_);
lean_ctor_set_float(v___x_131_, sizeof(void*)*3, v___x_128_);
lean_ctor_set_float(v___x_131_, sizeof(void*)*3 + 8, v___x_128_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*3 + 16, v___x_129_);
v___x_132_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2));
v___x_133_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v_a_105_);
lean_ctor_set(v___x_133_, 2, v___x_132_);
lean_inc(v_ref_103_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_ref_103_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = l_Lean_PersistentArray_push___redArg(v_traces_123_, v___x_134_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_135_);
v___x_137_ = v___x_125_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_135_);
lean_ctor_set_uint64(v_reuseFailAlloc_146_, sizeof(void*)*1, v_tid_122_);
v___x_137_ = v_reuseFailAlloc_146_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_139_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 4, v___x_137_);
v___x_139_ = v___x_120_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_env_111_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_nextMacroScope_112_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_ngen_113_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_auxDeclNGen_114_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_145_, 5, v_cache_115_);
lean_ctor_set(v_reuseFailAlloc_145_, 6, v_messages_116_);
lean_ctor_set(v_reuseFailAlloc_145_, 7, v_infoState_117_);
lean_ctor_set(v_reuseFailAlloc_145_, 8, v_snapshotTasks_118_);
v___x_139_ = v_reuseFailAlloc_145_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_st_ref_set(v___y_101_, v___x_139_);
v___x_141_ = lean_box(0);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_141_);
v___x_143_ = v___x_107_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___boxed(lean_object* v_cls_150_, lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_150_, v_msg_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_unsigned_to_nat(32u);
v___x_190_ = lean_mk_empty_array_with_capacity(v___x_189_);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15(void){
_start:
{
size_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_192_ = ((size_t)5ULL);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_unsigned_to_nat(32u);
v___x_195_ = lean_mk_empty_array_with_capacity(v___x_194_);
v___x_196_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14);
v___x_197_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
lean_ctor_set(v___x_197_, 2, v___x_193_);
lean_ctor_set(v___x_197_, 3, v___x_193_);
lean_ctor_set_usize(v___x_197_, 4, v___x_192_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0(lean_box(0));
return v___x_201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6));
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1));
v___x_209_ = l_Lean_Name_append(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(lean_object* v_type_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; 
lean_inc_ref(v_type_221_);
v___x_233_ = l_Lean_Meta_getDecLevel(v_type_221_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_n(v_a_234_, 2);
lean_dec_ref(v___x_233_);
v___x_235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3));
v___x_236_ = lean_box(0);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v_a_234_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
lean_inc_ref(v___x_237_);
v___x_238_ = l_Lean_mkConst(v___x_235_, v___x_237_);
lean_inc_ref(v_type_221_);
v___x_239_ = l_Lean_Expr_app___override(v___x_238_, v_type_221_);
v___x_240_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_239_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_502_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_502_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_502_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_502_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
if (lean_obj_tag(v_a_241_) == 1)
{
lean_object* v_val_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_497_; 
lean_del_object(v___x_243_);
v_val_245_ = lean_ctor_get(v_a_241_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v_a_241_);
if (v_isSharedCheck_497_ == 0)
{
v___x_247_ = v_a_241_;
v_isShared_248_ = v_isSharedCheck_497_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_val_245_);
lean_dec(v_a_241_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_497_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_inheritedTraceOptions_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_496_; 
v_inheritedTraceOptions_249_ = lean_ctor_get(v_a_230_, 13);
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6));
v___x_251_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_250_, v_inheritedTraceOptions_249_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_496_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_496_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_496_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; uint8_t v___x_474_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8));
lean_inc_ref_n(v___x_237_, 3);
v___x_257_ = l_Lean_mkConst(v___x_256_, v___x_237_);
lean_inc(v_val_245_);
lean_inc_ref_n(v_type_221_, 3);
v___x_258_ = l_Lean_mkAppB(v___x_257_, v_type_221_, v_val_245_);
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11));
v___x_260_ = l_Lean_mkConst(v___x_259_, v___x_237_);
lean_inc_ref(v___x_258_);
v___x_261_ = l_Lean_mkAppB(v___x_260_, v_type_221_, v___x_258_);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13));
v___x_263_ = l_Lean_mkConst(v___x_262_, v___x_237_);
lean_inc_ref(v___x_261_);
v___x_264_ = l_Lean_mkAppB(v___x_263_, v_type_221_, v___x_261_);
v___x_474_ = lean_unbox(v_a_252_);
lean_dec(v_a_252_);
if (v___x_474_ == 0)
{
v___y_428_ = v_a_222_;
v___y_429_ = v_a_223_;
v___y_430_ = v_a_224_;
v___y_431_ = v_a_225_;
v___y_432_ = v_a_226_;
v___y_433_ = v_a_227_;
v___y_434_ = v_a_228_;
v___y_435_ = v_a_229_;
v___y_436_ = v_a_230_;
v___y_437_ = v_a_231_;
goto v___jp_427_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Meta_Grind_updateLastTag(v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v___x_475_);
v___x_476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
lean_inc_ref(v_type_221_);
v___x_477_ = l_Lean_MessageData_ofExpr(v_type_221_);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_250_, v___x_478_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_dec_ref(v___x_479_);
v___y_428_ = v_a_222_;
v___y_429_ = v_a_223_;
v___y_430_ = v_a_224_;
v___y_431_ = v_a_225_;
v___y_432_ = v_a_226_;
v___y_433_ = v_a_227_;
v___y_434_ = v_a_228_;
v___y_435_ = v_a_229_;
v___y_436_ = v_a_230_;
v___y_437_ = v_a_231_;
goto v___jp_427_;
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec_ref(v___x_237_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec_ref(v___x_237_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_488_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_475_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_475_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
v___jp_265_:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v_rings_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v___x_272_);
v_rings_274_ = lean_ctor_get(v_a_273_, 0);
lean_inc_ref(v_rings_274_);
lean_dec(v_a_273_);
v___x_275_ = lean_box(0);
v___x_276_ = lean_array_get_size(v_rings_274_);
lean_dec_ref(v_rings_274_);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
v___x_279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17);
v___x_280_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_280_, 0, v___x_276_);
lean_ctor_set(v___x_280_, 1, v_type_221_);
lean_ctor_set(v___x_280_, 2, v_a_234_);
lean_ctor_set(v___x_280_, 3, v___x_258_);
lean_ctor_set(v___x_280_, 4, v___x_261_);
lean_ctor_set(v___x_280_, 5, v___y_269_);
lean_ctor_set(v___x_280_, 6, v___x_275_);
lean_ctor_set(v___x_280_, 7, v___x_275_);
lean_ctor_set(v___x_280_, 8, v___x_275_);
lean_ctor_set(v___x_280_, 9, v___x_275_);
lean_ctor_set(v___x_280_, 10, v___x_275_);
lean_ctor_set(v___x_280_, 11, v___x_275_);
lean_ctor_set(v___x_280_, 12, v___x_275_);
lean_ctor_set(v___x_280_, 13, v___x_275_);
lean_ctor_set(v___x_280_, 14, v___x_278_);
lean_ctor_set(v___x_280_, 15, v___x_279_);
lean_ctor_set(v___x_280_, 16, v___x_279_);
v___x_281_ = lean_box(1);
v___x_282_ = 0;
v___x_283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18);
v___x_284_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v___x_284_, 0, v___x_280_);
lean_ctor_set(v___x_284_, 1, v___x_275_);
lean_ctor_set(v___x_284_, 2, v___x_275_);
lean_ctor_set(v___x_284_, 3, v___x_264_);
lean_ctor_set(v___x_284_, 4, v_val_245_);
lean_ctor_set(v___x_284_, 5, v___y_266_);
lean_ctor_set(v___x_284_, 6, v___y_268_);
lean_ctor_set(v___x_284_, 7, v___y_267_);
lean_ctor_set(v___x_284_, 8, v___x_278_);
lean_ctor_set(v___x_284_, 9, v___x_277_);
lean_ctor_set(v___x_284_, 10, v___x_277_);
lean_ctor_set(v___x_284_, 11, v___x_281_);
lean_ctor_set(v___x_284_, 12, v___x_236_);
lean_ctor_set(v___x_284_, 13, v___x_278_);
lean_ctor_set(v___x_284_, 14, v___x_283_);
lean_ctor_set(v___x_284_, 15, v___x_277_);
lean_ctor_set(v___x_284_, 16, v___x_275_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*17, v___x_282_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*17 + 1, v___x_282_);
v___f_285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__1), 2, 1);
lean_closure_set(v___f_285_, 0, v___x_284_);
v___x_286_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_287_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_286_, v___f_285_, v___y_270_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_297_; 
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v___x_287_, 0);
lean_dec(v_unused_298_);
v___x_289_ = v___x_287_;
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
else
{
lean_dec(v___x_287_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_276_);
v___x_292_ = v___x_247_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_276_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_294_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
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
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_del_object(v___x_247_);
v_a_299_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_287_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_287_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v___y_269_);
lean_dec(v___y_268_);
lean_dec(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_307_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_272_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_272_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
v___jp_315_:
{
lean_object* v___x_333_; 
lean_inc_ref(v___y_331_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 3);
lean_ctor_set(v___x_254_, 0, v___y_331_);
v___x_333_ = v___x_254_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___y_331_);
v___x_333_ = v_reuseFailAlloc_345_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = l_Lean_MessageData_ofFormat(v___x_333_);
lean_inc_ref(v___y_329_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___y_329_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_250_, v___x_335_, v___y_318_, v___y_321_, v___y_330_, v___y_319_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_dec_ref(v___x_336_);
v___y_266_ = v___y_320_;
v___y_267_ = v___y_327_;
v___y_268_ = v___y_323_;
v___y_269_ = v___y_324_;
v___y_270_ = v___y_325_;
v___y_271_ = v___y_330_;
goto v___jp_265_;
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v___y_327_);
lean_dec(v___y_324_);
lean_dec(v___y_323_);
lean_dec(v___y_320_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
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
}
v___jp_346_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20));
v___x_360_ = l_Lean_mkConst(v___x_359_, v___x_237_);
lean_inc_ref(v_type_221_);
v___x_361_ = l_Lean_Expr_app___override(v___x_360_, v_type_221_);
v___x_362_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_361_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref(v___x_362_);
lean_inc_ref(v_type_221_);
lean_inc(v_a_234_);
v___x_364_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(v_a_234_, v_type_221_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_options_365_; uint8_t v_hasTrace_366_; 
v_options_365_ = lean_ctor_get(v___y_357_, 2);
v_hasTrace_366_ = lean_ctor_get_uint8(v_options_365_, sizeof(void*)*1);
if (v_hasTrace_366_ == 0)
{
lean_object* v_a_367_; 
lean_del_object(v___x_254_);
v_a_367_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_364_);
v___y_266_ = v___y_347_;
v___y_267_ = v_a_367_;
v___y_268_ = v_a_363_;
v___y_269_ = v___y_348_;
v___y_270_ = v___y_349_;
v___y_271_ = v___y_357_;
goto v___jp_265_;
}
else
{
lean_object* v_a_368_; lean_object* v_inheritedTraceOptions_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_a_368_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_368_);
lean_dec_ref(v___x_364_);
v_inheritedTraceOptions_369_ = lean_ctor_get(v___y_357_, 13);
v___x_370_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21);
v___x_371_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_369_, v_options_365_, v___x_370_);
if (v___x_371_ == 0)
{
lean_del_object(v___x_254_);
v___y_266_ = v___y_347_;
v___y_267_ = v_a_368_;
v___y_268_ = v_a_363_;
v___y_269_ = v___y_348_;
v___y_270_ = v___y_349_;
v___y_271_ = v___y_357_;
goto v___jp_265_;
}
else
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Grind_updateLastTag(v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; 
lean_dec_ref(v___x_372_);
v___x_373_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23);
if (lean_obj_tag(v_a_368_) == 0)
{
lean_object* v___x_374_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24));
v___y_316_ = v___y_353_;
v___y_317_ = v___y_352_;
v___y_318_ = v___y_355_;
v___y_319_ = v___y_358_;
v___y_320_ = v___y_347_;
v___y_321_ = v___y_356_;
v___y_322_ = v___y_350_;
v___y_323_ = v_a_363_;
v___y_324_ = v___y_348_;
v___y_325_ = v___y_349_;
v___y_326_ = v___y_354_;
v___y_327_ = v_a_368_;
v___y_328_ = v___y_351_;
v___y_329_ = v___x_373_;
v___y_330_ = v___y_357_;
v___y_331_ = v___x_374_;
goto v___jp_315_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25));
v___y_316_ = v___y_353_;
v___y_317_ = v___y_352_;
v___y_318_ = v___y_355_;
v___y_319_ = v___y_358_;
v___y_320_ = v___y_347_;
v___y_321_ = v___y_356_;
v___y_322_ = v___y_350_;
v___y_323_ = v_a_363_;
v___y_324_ = v___y_348_;
v___y_325_ = v___y_349_;
v___y_326_ = v___y_354_;
v___y_327_ = v_a_368_;
v___y_328_ = v___y_351_;
v___y_329_ = v___x_373_;
v___y_330_ = v___y_357_;
v___y_331_ = v___x_375_;
goto v___jp_315_;
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_a_368_);
lean_dec(v_a_363_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_376_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_372_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_372_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_a_363_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_384_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_364_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_364_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_392_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_362_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_362_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
v___jp_400_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_inc_ref(v___y_414_);
v___x_415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_415_, 0, v___y_414_);
v___x_416_ = l_Lean_MessageData_ofFormat(v___x_415_);
lean_inc_ref(v___y_401_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___y_401_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_250_, v___x_417_, v___y_412_, v___y_409_, v___y_402_, v___y_404_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_dec_ref(v___x_418_);
v___y_347_ = v___y_403_;
v___y_348_ = v___y_408_;
v___y_349_ = v___y_405_;
v___y_350_ = v___y_410_;
v___y_351_ = v___y_407_;
v___y_352_ = v___y_413_;
v___y_353_ = v___y_406_;
v___y_354_ = v___y_411_;
v___y_355_ = v___y_412_;
v___y_356_ = v___y_409_;
v___y_357_ = v___y_402_;
v___y_358_ = v___y_404_;
goto v___jp_346_;
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v___y_408_);
lean_dec(v___y_403_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec_ref(v___x_237_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
v___jp_427_:
{
lean_object* v___x_438_; 
lean_inc_ref(v___x_261_);
lean_inc_ref(v_type_221_);
lean_inc(v_a_234_);
v___x_438_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_234_, v_type_221_, v___x_261_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref(v___x_438_);
lean_inc_ref(v_type_221_);
lean_inc(v_a_234_);
v___x_440_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_a_234_, v_type_221_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_inheritedTraceOptions_442_; lean_object* v___x_443_; lean_object* v_a_444_; uint8_t v___x_445_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref(v___x_440_);
v_inheritedTraceOptions_442_ = lean_ctor_get(v___y_436_, 13);
v___x_443_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_250_, v_inheritedTraceOptions_442_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref(v___x_443_);
v___x_445_ = lean_unbox(v_a_444_);
lean_dec(v_a_444_);
if (v___x_445_ == 0)
{
v___y_347_ = v_a_441_;
v___y_348_ = v_a_439_;
v___y_349_ = v___y_428_;
v___y_350_ = v___y_429_;
v___y_351_ = v___y_430_;
v___y_352_ = v___y_431_;
v___y_353_ = v___y_432_;
v___y_354_ = v___y_433_;
v___y_355_ = v___y_434_;
v___y_356_ = v___y_435_;
v___y_357_ = v___y_436_;
v___y_358_ = v___y_437_;
goto v___jp_346_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_Grind_updateLastTag(v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v___x_447_; 
lean_dec_ref(v___x_446_);
v___x_447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27);
if (lean_obj_tag(v_a_441_) == 0)
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24));
v___y_401_ = v___x_447_;
v___y_402_ = v___y_436_;
v___y_403_ = v_a_441_;
v___y_404_ = v___y_437_;
v___y_405_ = v___y_428_;
v___y_406_ = v___y_432_;
v___y_407_ = v___y_430_;
v___y_408_ = v_a_439_;
v___y_409_ = v___y_435_;
v___y_410_ = v___y_429_;
v___y_411_ = v___y_433_;
v___y_412_ = v___y_434_;
v___y_413_ = v___y_431_;
v___y_414_ = v___x_448_;
goto v___jp_400_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25));
v___y_401_ = v___x_447_;
v___y_402_ = v___y_436_;
v___y_403_ = v_a_441_;
v___y_404_ = v___y_437_;
v___y_405_ = v___y_428_;
v___y_406_ = v___y_432_;
v___y_407_ = v___y_430_;
v___y_408_ = v_a_439_;
v___y_409_ = v___y_435_;
v___y_410_ = v___y_429_;
v___y_411_ = v___y_433_;
v___y_412_ = v___y_434_;
v___y_413_ = v___y_431_;
v___y_414_ = v___x_449_;
goto v___jp_400_;
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_a_441_);
lean_dec(v_a_439_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec_ref(v___x_237_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_450_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_446_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_446_);
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
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec(v_a_439_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec_ref(v___x_237_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_458_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_440_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_440_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_247_);
lean_dec(v_val_245_);
lean_dec_ref(v___x_237_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_466_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_438_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_438_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_dec(v_a_241_);
lean_dec_ref(v___x_237_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v___x_498_ = lean_box(0);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_498_);
v___x_500_ = v___x_243_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec_ref(v___x_237_);
lean_dec(v_a_234_);
lean_dec_ref(v_type_221_);
v_a_503_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_240_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_240_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_type_221_);
v_a_511_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_233_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_233_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___boxed(lean_object* v_type_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec(v_a_520_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(lean_object* v_cls_532_, lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_532_, v_msg_533_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___boxed(lean_object* v_cls_546_, lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(v_cls_546_, v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec(v___y_548_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_ks_564_; lean_object* v_vs_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_589_; 
v_ks_564_ = lean_ctor_get(v_x_560_, 0);
v_vs_565_ = lean_ctor_get(v_x_560_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_x_560_);
if (v_isSharedCheck_589_ == 0)
{
v___x_567_ = v_x_560_;
v_isShared_568_ = v_isSharedCheck_589_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_vs_565_);
lean_inc(v_ks_564_);
lean_dec(v_x_560_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_589_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_array_get_size(v_ks_564_);
v___x_570_ = lean_nat_dec_lt(v_x_561_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
lean_dec(v_x_561_);
v___x_571_ = lean_array_push(v_ks_564_, v_x_562_);
v___x_572_ = lean_array_push(v_vs_565_, v_x_563_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_572_);
lean_ctor_set(v___x_567_, 0, v___x_571_);
v___x_574_ = v___x_567_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
else
{
lean_object* v_k_x27_576_; uint8_t v___x_577_; 
v_k_x27_576_ = lean_array_fget_borrowed(v_ks_564_, v_x_561_);
v___x_577_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_562_, v_k_x27_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_579_; 
if (v_isShared_568_ == 0)
{
v___x_579_ = v___x_567_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_ks_564_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_vs_565_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_add(v_x_561_, v___x_580_);
lean_dec(v_x_561_);
v_x_560_ = v___x_579_;
v_x_561_ = v___x_581_;
goto _start;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_584_ = lean_array_fset(v_ks_564_, v_x_561_, v_x_562_);
v___x_585_ = lean_array_fset(v_vs_565_, v_x_561_, v_x_563_);
lean_dec(v_x_561_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_585_);
lean_ctor_set(v___x_567_, 0, v___x_584_);
v___x_587_ = v___x_567_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_590_, lean_object* v_k_591_, lean_object* v_v_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_590_, v___x_593_, v_k_591_, v_v_592_);
return v___x_594_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; 
v___x_595_ = ((size_t)5ULL);
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_shift_left(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; 
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0);
v___x_600_ = lean_usize_sub(v___x_599_, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(lean_object* v_x_602_, size_t v_x_603_, size_t v_x_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
lean_object* v_es_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v_j_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_es_607_ = lean_ctor_get(v_x_602_, 0);
v___x_608_ = ((size_t)5ULL);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
v___x_611_ = lean_usize_land(v_x_603_, v___x_610_);
v_j_612_ = lean_usize_to_nat(v___x_611_);
v___x_613_ = lean_array_get_size(v_es_607_);
v___x_614_ = lean_nat_dec_lt(v_j_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_dec(v_j_612_);
lean_dec(v_x_606_);
lean_dec_ref(v_x_605_);
return v_x_602_;
}
else
{
lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_651_; 
lean_inc_ref(v_es_607_);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_602_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_x_602_, 0);
lean_dec(v_unused_652_);
v___x_616_ = v_x_602_;
v_isShared_617_ = v_isSharedCheck_651_;
goto v_resetjp_615_;
}
else
{
lean_dec(v_x_602_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_651_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_v_618_; lean_object* v___x_619_; lean_object* v_xs_x27_620_; lean_object* v___y_622_; 
v_v_618_ = lean_array_fget(v_es_607_, v_j_612_);
v___x_619_ = lean_box(0);
v_xs_x27_620_ = lean_array_fset(v_es_607_, v_j_612_, v___x_619_);
switch(lean_obj_tag(v_v_618_))
{
case 0:
{
lean_object* v_key_627_; lean_object* v_val_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_638_; 
v_key_627_ = lean_ctor_get(v_v_618_, 0);
v_val_628_ = lean_ctor_get(v_v_618_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_v_618_);
if (v_isSharedCheck_638_ == 0)
{
v___x_630_ = v_v_618_;
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_val_628_);
lean_inc(v_key_627_);
lean_dec(v_v_618_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
uint8_t v___x_632_; 
v___x_632_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_605_, v_key_627_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_del_object(v___x_630_);
v___x_633_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_627_, v_val_628_, v_x_605_, v_x_606_);
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___y_622_ = v___x_634_;
goto v___jp_621_;
}
else
{
lean_object* v___x_636_; 
lean_dec(v_val_628_);
lean_dec(v_key_627_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v_x_606_);
lean_ctor_set(v___x_630_, 0, v_x_605_);
v___x_636_ = v___x_630_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_x_605_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_x_606_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
v___y_622_ = v___x_636_;
goto v___jp_621_;
}
}
}
}
case 1:
{
lean_object* v_node_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_649_; 
v_node_639_ = lean_ctor_get(v_v_618_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_v_618_);
if (v_isSharedCheck_649_ == 0)
{
v___x_641_ = v_v_618_;
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_node_639_);
lean_dec(v_v_618_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_643_ = lean_usize_shift_right(v_x_603_, v___x_608_);
v___x_644_ = lean_usize_add(v_x_604_, v___x_609_);
v___x_645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_node_639_, v___x_643_, v___x_644_, v_x_605_, v_x_606_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_645_);
v___x_647_ = v___x_641_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v___y_622_ = v___x_647_;
goto v___jp_621_;
}
}
}
default: 
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_x_605_);
lean_ctor_set(v___x_650_, 1, v_x_606_);
v___y_622_ = v___x_650_;
goto v___jp_621_;
}
}
v___jp_621_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_array_fset(v_xs_x27_620_, v_j_612_, v___y_622_);
lean_dec(v_j_612_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_623_);
v___x_625_ = v___x_616_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
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
else
{
lean_object* v_ks_653_; lean_object* v_vs_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_674_; 
v_ks_653_ = lean_ctor_get(v_x_602_, 0);
v_vs_654_ = lean_ctor_get(v_x_602_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_602_);
if (v_isSharedCheck_674_ == 0)
{
v___x_656_ = v_x_602_;
v_isShared_657_ = v_isSharedCheck_674_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_vs_654_);
lean_inc(v_ks_653_);
lean_dec(v_x_602_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_674_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_ks_653_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_vs_654_);
v___x_659_ = v_reuseFailAlloc_673_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v_newNode_660_; uint8_t v___y_662_; size_t v___x_668_; uint8_t v___x_669_; 
v_newNode_660_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v___x_659_, v_x_605_, v_x_606_);
v___x_668_ = ((size_t)7ULL);
v___x_669_ = lean_usize_dec_le(v___x_668_, v_x_604_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_660_);
v___x_671_ = lean_unsigned_to_nat(4u);
v___x_672_ = lean_nat_dec_lt(v___x_670_, v___x_671_);
lean_dec(v___x_670_);
v___y_662_ = v___x_672_;
goto v___jp_661_;
}
else
{
v___y_662_ = v___x_669_;
goto v___jp_661_;
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_object* v_ks_663_; lean_object* v_vs_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_ks_663_ = lean_ctor_get(v_newNode_660_, 0);
lean_inc_ref(v_ks_663_);
v_vs_664_ = lean_ctor_get(v_newNode_660_, 1);
lean_inc_ref(v_vs_664_);
lean_dec_ref(v_newNode_660_);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2);
v___x_667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_x_604_, v_ks_663_, v_vs_664_, v___x_665_, v___x_666_);
lean_dec_ref(v_vs_664_);
lean_dec_ref(v_ks_663_);
return v___x_667_;
}
else
{
return v_newNode_660_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_675_, lean_object* v_keys_676_, lean_object* v_vals_677_, lean_object* v_i_678_, lean_object* v_entries_679_){
_start:
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_array_get_size(v_keys_676_);
v___x_681_ = lean_nat_dec_lt(v_i_678_, v___x_680_);
if (v___x_681_ == 0)
{
lean_dec(v_i_678_);
return v_entries_679_;
}
else
{
lean_object* v_k_682_; lean_object* v_v_683_; uint64_t v___x_684_; size_t v_h_685_; size_t v___x_686_; lean_object* v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v_h_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_k_682_ = lean_array_fget_borrowed(v_keys_676_, v_i_678_);
v_v_683_ = lean_array_fget_borrowed(v_vals_677_, v_i_678_);
v___x_684_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_682_);
v_h_685_ = lean_uint64_to_usize(v___x_684_);
v___x_686_ = ((size_t)5ULL);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_sub(v_depth_675_, v___x_688_);
v___x_690_ = lean_usize_mul(v___x_686_, v___x_689_);
v_h_691_ = lean_usize_shift_right(v_h_685_, v___x_690_);
v___x_692_ = lean_nat_add(v_i_678_, v___x_687_);
lean_dec(v_i_678_);
lean_inc(v_v_683_);
lean_inc(v_k_682_);
v___x_693_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_entries_679_, v_h_691_, v_depth_675_, v_k_682_, v_v_683_);
v_i_678_ = v___x_692_;
v_entries_679_ = v___x_693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_695_, lean_object* v_keys_696_, lean_object* v_vals_697_, lean_object* v_i_698_, lean_object* v_entries_699_){
_start:
{
size_t v_depth_boxed_700_; lean_object* v_res_701_; 
v_depth_boxed_700_ = lean_unbox_usize(v_depth_695_);
lean_dec(v_depth_695_);
v_res_701_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_700_, v_keys_696_, v_vals_697_, v_i_698_, v_entries_699_);
lean_dec_ref(v_vals_697_);
lean_dec_ref(v_keys_696_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
size_t v_x_3692__boxed_707_; size_t v_x_3693__boxed_708_; lean_object* v_res_709_; 
v_x_3692__boxed_707_ = lean_unbox_usize(v_x_703_);
lean_dec(v_x_703_);
v_x_3693__boxed_708_ = lean_unbox_usize(v_x_704_);
lean_dec(v_x_704_);
v_res_709_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_702_, v_x_3692__boxed_707_, v_x_3693__boxed_708_, v_x_705_, v_x_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
uint64_t v___x_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_713_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_711_);
v___x_714_ = lean_uint64_to_usize(v___x_713_);
v___x_715_ = ((size_t)1ULL);
v___x_716_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_710_, v___x_714_, v___x_715_, v_x_711_, v_x_712_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(lean_object* v_type_717_, lean_object* v_a_718_, lean_object* v_s_719_){
_start:
{
lean_object* v_rings_720_; lean_object* v_typeIdOf_721_; lean_object* v_exprToRingId_722_; lean_object* v_semirings_723_; lean_object* v_stypeIdOf_724_; lean_object* v_exprToSemiringId_725_; lean_object* v_ncRings_726_; lean_object* v_exprToNCRingId_727_; lean_object* v_nctypeIdOf_728_; lean_object* v_ncSemirings_729_; lean_object* v_exprToNCSemiringId_730_; lean_object* v_ncstypeIdOf_731_; lean_object* v_steps_732_; uint8_t v_reportedMaxDegreeIssue_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_rings_720_ = lean_ctor_get(v_s_719_, 0);
v_typeIdOf_721_ = lean_ctor_get(v_s_719_, 1);
v_exprToRingId_722_ = lean_ctor_get(v_s_719_, 2);
v_semirings_723_ = lean_ctor_get(v_s_719_, 3);
v_stypeIdOf_724_ = lean_ctor_get(v_s_719_, 4);
v_exprToSemiringId_725_ = lean_ctor_get(v_s_719_, 5);
v_ncRings_726_ = lean_ctor_get(v_s_719_, 6);
v_exprToNCRingId_727_ = lean_ctor_get(v_s_719_, 7);
v_nctypeIdOf_728_ = lean_ctor_get(v_s_719_, 8);
v_ncSemirings_729_ = lean_ctor_get(v_s_719_, 9);
v_exprToNCSemiringId_730_ = lean_ctor_get(v_s_719_, 10);
v_ncstypeIdOf_731_ = lean_ctor_get(v_s_719_, 11);
v_steps_732_ = lean_ctor_get(v_s_719_, 12);
v_reportedMaxDegreeIssue_733_ = lean_ctor_get_uint8(v_s_719_, sizeof(void*)*13);
v_isSharedCheck_741_ = !lean_is_exclusive(v_s_719_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v_s_719_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_steps_732_);
lean_inc(v_ncstypeIdOf_731_);
lean_inc(v_exprToNCSemiringId_730_);
lean_inc(v_ncSemirings_729_);
lean_inc(v_nctypeIdOf_728_);
lean_inc(v_exprToNCRingId_727_);
lean_inc(v_ncRings_726_);
lean_inc(v_exprToSemiringId_725_);
lean_inc(v_stypeIdOf_724_);
lean_inc(v_semirings_723_);
lean_inc(v_exprToRingId_722_);
lean_inc(v_typeIdOf_721_);
lean_inc(v_rings_720_);
lean_dec(v_s_719_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_typeIdOf_721_, v_type_717_, v_a_718_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_rings_720_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_exprToRingId_722_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_semirings_723_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_stypeIdOf_724_);
lean_ctor_set(v_reuseFailAlloc_740_, 5, v_exprToSemiringId_725_);
lean_ctor_set(v_reuseFailAlloc_740_, 6, v_ncRings_726_);
lean_ctor_set(v_reuseFailAlloc_740_, 7, v_exprToNCRingId_727_);
lean_ctor_set(v_reuseFailAlloc_740_, 8, v_nctypeIdOf_728_);
lean_ctor_set(v_reuseFailAlloc_740_, 9, v_ncSemirings_729_);
lean_ctor_set(v_reuseFailAlloc_740_, 10, v_exprToNCSemiringId_730_);
lean_ctor_set(v_reuseFailAlloc_740_, 11, v_ncstypeIdOf_731_);
lean_ctor_set(v_reuseFailAlloc_740_, 12, v_steps_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_740_, sizeof(void*)*13, v_reportedMaxDegreeIssue_733_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_742_, lean_object* v_vals_743_, lean_object* v_i_744_, lean_object* v_k_745_){
_start:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_array_get_size(v_keys_742_);
v___x_747_ = lean_nat_dec_lt(v_i_744_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
lean_dec(v_i_744_);
v___x_748_ = lean_box(0);
return v___x_748_;
}
else
{
lean_object* v_k_x27_749_; uint8_t v___x_750_; 
v_k_x27_749_ = lean_array_fget_borrowed(v_keys_742_, v_i_744_);
v___x_750_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_745_, v_k_x27_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_nat_add(v_i_744_, v___x_751_);
lean_dec(v_i_744_);
v_i_744_ = v___x_752_;
goto _start;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_array_fget_borrowed(v_vals_743_, v_i_744_);
lean_dec(v_i_744_);
lean_inc(v___x_754_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_756_, lean_object* v_vals_757_, lean_object* v_i_758_, lean_object* v_k_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_756_, v_vals_757_, v_i_758_, v_k_759_);
lean_dec_ref(v_k_759_);
lean_dec_ref(v_vals_757_);
lean_dec_ref(v_keys_756_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_761_, size_t v_x_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v_es_764_; lean_object* v___x_765_; size_t v___x_766_; size_t v___x_767_; size_t v___x_768_; lean_object* v_j_769_; lean_object* v___x_770_; 
v_es_764_ = lean_ctor_get(v_x_761_, 0);
v___x_765_ = lean_box(2);
v___x_766_ = ((size_t)5ULL);
v___x_767_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
v___x_768_ = lean_usize_land(v_x_762_, v___x_767_);
v_j_769_ = lean_usize_to_nat(v___x_768_);
v___x_770_ = lean_array_get_borrowed(v___x_765_, v_es_764_, v_j_769_);
lean_dec(v_j_769_);
switch(lean_obj_tag(v___x_770_))
{
case 0:
{
lean_object* v_key_771_; lean_object* v_val_772_; uint8_t v___x_773_; 
v_key_771_ = lean_ctor_get(v___x_770_, 0);
v_val_772_ = lean_ctor_get(v___x_770_, 1);
v___x_773_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_763_, v_key_771_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
v___x_774_ = lean_box(0);
return v___x_774_;
}
else
{
lean_object* v___x_775_; 
lean_inc(v_val_772_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v_val_772_);
return v___x_775_;
}
}
case 1:
{
lean_object* v_node_776_; size_t v___x_777_; 
v_node_776_ = lean_ctor_get(v___x_770_, 0);
v___x_777_ = lean_usize_shift_right(v_x_762_, v___x_766_);
v_x_761_ = v_node_776_;
v_x_762_ = v___x_777_;
goto _start;
}
default: 
{
lean_object* v___x_779_; 
v___x_779_ = lean_box(0);
return v___x_779_;
}
}
}
else
{
lean_object* v_ks_780_; lean_object* v_vs_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_ks_780_ = lean_ctor_get(v_x_761_, 0);
v_vs_781_ = lean_ctor_get(v_x_761_, 1);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_780_, v_vs_781_, v___x_782_, v_x_763_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
size_t v_x_3910__boxed_787_; lean_object* v_res_788_; 
v_x_3910__boxed_787_ = lean_unbox_usize(v_x_785_);
lean_dec(v_x_785_);
v_res_788_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_784_, v_x_3910__boxed_787_, v_x_786_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_784_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
uint64_t v___x_791_; size_t v___x_792_; lean_object* v___x_793_; 
v___x_791_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_790_);
v___x_792_ = lean_uint64_to_usize(v___x_791_);
v___x_793_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_789_, v___x_792_, v_x_790_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_794_, v_x_795_);
lean_dec_ref(v_x_795_);
lean_dec_ref(v_x_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object* v_type_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_798_, v_a_806_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_841_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_841_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_841_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_841_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_typeIdOf_814_; lean_object* v___x_815_; 
v_typeIdOf_814_ = lean_ctor_get(v_a_810_, 1);
lean_inc_ref(v_typeIdOf_814_);
lean_dec(v_a_810_);
v___x_815_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_typeIdOf_814_, v_type_797_);
lean_dec_ref(v_typeIdOf_814_);
if (lean_obj_tag(v___x_815_) == 1)
{
lean_object* v_val_816_; lean_object* v___x_818_; 
lean_dec_ref(v_type_797_);
v_val_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_816_);
lean_dec_ref(v___x_815_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v_val_816_);
v___x_818_ = v___x_812_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_val_816_);
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
lean_dec(v___x_815_);
lean_del_object(v___x_812_);
lean_inc_ref(v_type_797_);
v___x_820_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_n(v_a_821_, 2);
lean_dec_ref(v___x_820_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_822_, 0, v_type_797_);
lean_closure_set(v___f_822_, 1, v_a_821_);
v___x_823_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_824_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_823_, v___f_822_, v_a_798_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v___x_824_, 0);
lean_dec(v_unused_832_);
v___x_826_ = v___x_824_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_dec(v___x_824_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v_a_821_);
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_821_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_a_821_);
v_a_833_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_824_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_824_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_dec_ref(v_type_797_);
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v_type_797_);
v_a_842_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_809_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_809_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___boxed(lean_object* v_type_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec(v_a_851_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(v_00_u03b2_867_, v_x_868_, v_x_869_);
lean_dec_ref(v_x_869_);
lean_dec_ref(v_x_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_x_872_, v_x_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, size_t v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_877_, v_x_878_, v_x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
size_t v_x_4072__boxed_885_; lean_object* v_res_886_; 
v_x_4072__boxed_885_ = lean_unbox_usize(v_x_883_);
lean_dec(v_x_883_);
v_res_886_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(v_00_u03b2_881_, v_x_882_, v_x_4072__boxed_885_, v_x_884_);
lean_dec_ref(v_x_884_);
lean_dec_ref(v_x_882_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, size_t v_x_889_, size_t v_x_890_, lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_888_, v_x_889_, v_x_890_, v_x_891_, v_x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
size_t v_x_4083__boxed_900_; size_t v_x_4084__boxed_901_; lean_object* v_res_902_; 
v_x_4083__boxed_900_ = lean_unbox_usize(v_x_896_);
lean_dec(v_x_896_);
v_x_4084__boxed_901_ = lean_unbox_usize(v_x_897_);
lean_dec(v_x_897_);
v_res_902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(v_00_u03b2_894_, v_x_895_, v_x_4083__boxed_900_, v_x_4084__boxed_901_, v_x_898_, v_x_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_903_, lean_object* v_keys_904_, lean_object* v_vals_905_, lean_object* v_heq_906_, lean_object* v_i_907_, lean_object* v_k_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_904_, v_vals_905_, v_i_907_, v_k_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_910_, lean_object* v_keys_911_, lean_object* v_vals_912_, lean_object* v_heq_913_, lean_object* v_i_914_, lean_object* v_k_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_910_, v_keys_911_, v_vals_912_, v_heq_913_, v_i_914_, v_k_915_);
lean_dec_ref(v_k_915_);
lean_dec_ref(v_vals_912_);
lean_dec_ref(v_keys_911_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_917_, lean_object* v_n_918_, lean_object* v_k_919_, lean_object* v_v_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v_n_918_, v_k_919_, v_v_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_922_, size_t v_depth_923_, lean_object* v_keys_924_, lean_object* v_vals_925_, lean_object* v_heq_926_, lean_object* v_i_927_, lean_object* v_entries_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_923_, v_keys_924_, v_vals_925_, v_i_927_, v_entries_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_930_, lean_object* v_depth_931_, lean_object* v_keys_932_, lean_object* v_vals_933_, lean_object* v_heq_934_, lean_object* v_i_935_, lean_object* v_entries_936_){
_start:
{
size_t v_depth_boxed_937_; lean_object* v_res_938_; 
v_depth_boxed_937_ = lean_unbox_usize(v_depth_931_);
lean_dec(v_depth_931_);
v_res_938_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_930_, v_depth_boxed_937_, v_keys_932_, v_vals_933_, v_heq_934_, v_i_935_, v_entries_936_);
lean_dec_ref(v_vals_933_);
lean_dec_ref(v_keys_932_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_940_, v_x_941_, v_x_942_, v_x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(lean_object* v___x_945_, lean_object* v_s_946_){
_start:
{
lean_object* v_rings_947_; lean_object* v_typeIdOf_948_; lean_object* v_exprToRingId_949_; lean_object* v_semirings_950_; lean_object* v_stypeIdOf_951_; lean_object* v_exprToSemiringId_952_; lean_object* v_ncRings_953_; lean_object* v_exprToNCRingId_954_; lean_object* v_nctypeIdOf_955_; lean_object* v_ncSemirings_956_; lean_object* v_exprToNCSemiringId_957_; lean_object* v_ncstypeIdOf_958_; lean_object* v_steps_959_; uint8_t v_reportedMaxDegreeIssue_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_rings_947_ = lean_ctor_get(v_s_946_, 0);
v_typeIdOf_948_ = lean_ctor_get(v_s_946_, 1);
v_exprToRingId_949_ = lean_ctor_get(v_s_946_, 2);
v_semirings_950_ = lean_ctor_get(v_s_946_, 3);
v_stypeIdOf_951_ = lean_ctor_get(v_s_946_, 4);
v_exprToSemiringId_952_ = lean_ctor_get(v_s_946_, 5);
v_ncRings_953_ = lean_ctor_get(v_s_946_, 6);
v_exprToNCRingId_954_ = lean_ctor_get(v_s_946_, 7);
v_nctypeIdOf_955_ = lean_ctor_get(v_s_946_, 8);
v_ncSemirings_956_ = lean_ctor_get(v_s_946_, 9);
v_exprToNCSemiringId_957_ = lean_ctor_get(v_s_946_, 10);
v_ncstypeIdOf_958_ = lean_ctor_get(v_s_946_, 11);
v_steps_959_ = lean_ctor_get(v_s_946_, 12);
v_reportedMaxDegreeIssue_960_ = lean_ctor_get_uint8(v_s_946_, sizeof(void*)*13);
v_isSharedCheck_968_ = !lean_is_exclusive(v_s_946_);
if (v_isSharedCheck_968_ == 0)
{
v___x_962_ = v_s_946_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_steps_959_);
lean_inc(v_ncstypeIdOf_958_);
lean_inc(v_exprToNCSemiringId_957_);
lean_inc(v_ncSemirings_956_);
lean_inc(v_nctypeIdOf_955_);
lean_inc(v_exprToNCRingId_954_);
lean_inc(v_ncRings_953_);
lean_inc(v_exprToSemiringId_952_);
lean_inc(v_stypeIdOf_951_);
lean_inc(v_semirings_950_);
lean_inc(v_exprToRingId_949_);
lean_inc(v_typeIdOf_948_);
lean_inc(v_rings_947_);
lean_dec(v_s_946_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = lean_array_push(v_ncRings_953_, v___x_945_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 6, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_rings_947_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_typeIdOf_948_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_exprToRingId_949_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_semirings_950_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_stypeIdOf_951_);
lean_ctor_set(v_reuseFailAlloc_967_, 5, v_exprToSemiringId_952_);
lean_ctor_set(v_reuseFailAlloc_967_, 6, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_967_, 7, v_exprToNCRingId_954_);
lean_ctor_set(v_reuseFailAlloc_967_, 8, v_nctypeIdOf_955_);
lean_ctor_set(v_reuseFailAlloc_967_, 9, v_ncSemirings_956_);
lean_ctor_set(v_reuseFailAlloc_967_, 10, v_exprToNCSemiringId_957_);
lean_ctor_set(v_reuseFailAlloc_967_, 11, v_ncstypeIdOf_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 12, v_steps_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*13, v_reportedMaxDegreeIssue_960_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(lean_object* v_type_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; 
lean_inc_ref(v_type_973_);
v___x_985_ = l_Lean_Meta_getDecLevel(v_type_973_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc_n(v_a_986_, 2);
lean_dec_ref(v___x_985_);
v___x_987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0));
v___x_988_ = lean_box(0);
v___x_989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_989_, 0, v_a_986_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
lean_inc_ref(v___x_989_);
v___x_990_ = l_Lean_mkConst(v___x_987_, v___x_989_);
lean_inc_ref(v_type_973_);
v___x_991_ = l_Lean_Expr_app___override(v___x_990_, v_type_973_);
v___x_992_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_991_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1095_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1095_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1095_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
if (lean_obj_tag(v_a_993_) == 1)
{
lean_object* v_options_997_; lean_object* v_val_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1090_; 
lean_del_object(v___x_995_);
v_options_997_ = lean_ctor_get(v_a_982_, 2);
v_val_998_ = lean_ctor_get(v_a_993_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_a_993_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1000_ = v_a_993_;
v_isShared_1001_ = v_isSharedCheck_1090_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_val_998_);
lean_dec(v_a_993_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1090_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_inheritedTraceOptions_1002_; uint8_t v_hasTrace_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; 
v_inheritedTraceOptions_1002_ = lean_ctor_get(v_a_982_, 13);
v_hasTrace_1003_ = lean_ctor_get_uint8(v_options_997_, sizeof(void*)*1);
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11));
v___x_1005_ = l_Lean_mkConst(v___x_1004_, v___x_989_);
lean_inc(v_val_998_);
lean_inc_ref(v_type_973_);
v___x_1006_ = l_Lean_mkAppB(v___x_1005_, v_type_973_, v_val_998_);
if (v_hasTrace_1003_ == 0)
{
v___y_1008_ = v_a_974_;
v___y_1009_ = v_a_975_;
v___y_1010_ = v_a_976_;
v___y_1011_ = v_a_977_;
v___y_1012_ = v_a_978_;
v___y_1013_ = v_a_979_;
v___y_1014_ = v_a_980_;
v___y_1015_ = v_a_981_;
v___y_1016_ = v_a_982_;
v___y_1017_ = v_a_983_;
goto v___jp_1007_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6));
v___x_1067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21);
v___x_1068_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1002_, v_options_997_, v___x_1067_);
if (v___x_1068_ == 0)
{
v___y_1008_ = v_a_974_;
v___y_1009_ = v_a_975_;
v___y_1010_ = v_a_976_;
v___y_1011_ = v_a_977_;
v___y_1012_ = v_a_978_;
v___y_1013_ = v_a_979_;
v___y_1014_ = v_a_980_;
v___y_1015_ = v_a_981_;
v___y_1016_ = v_a_982_;
v___y_1017_ = v_a_983_;
goto v___jp_1007_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Meta_Grind_updateLastTag(v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec_ref(v___x_1069_);
v___x_1070_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
lean_inc_ref(v_type_973_);
v___x_1071_ = l_Lean_MessageData_ofExpr(v_type_973_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_1066_, v___x_1072_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_dec_ref(v___x_1073_);
v___y_1008_ = v_a_974_;
v___y_1009_ = v_a_975_;
v___y_1010_ = v_a_976_;
v___y_1011_ = v_a_977_;
v___y_1012_ = v_a_978_;
v___y_1013_ = v_a_979_;
v___y_1014_ = v_a_980_;
v___y_1015_ = v_a_981_;
v___y_1016_ = v_a_982_;
v___y_1017_ = v_a_983_;
goto v___jp_1007_;
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v___x_1006_);
lean_del_object(v___x_1000_);
lean_dec(v_val_998_);
lean_dec(v_a_986_);
lean_dec_ref(v_type_973_);
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v___x_1006_);
lean_del_object(v___x_1000_);
lean_dec(v_val_998_);
lean_dec(v_a_986_);
lean_dec_ref(v_type_973_);
v_a_1082_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1069_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1069_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
v___jp_1007_:
{
lean_object* v___x_1018_; 
lean_inc_ref(v___x_1006_);
lean_inc_ref(v_type_973_);
lean_inc(v_a_986_);
v___x_1018_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_986_, v_type_973_, v___x_1006_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_1008_, v___y_1016_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v_ncRings_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref(v___x_1020_);
v_ncRings_1022_ = lean_ctor_get(v_a_1021_, 6);
lean_inc_ref(v_ncRings_1022_);
lean_dec(v_a_1021_);
v___x_1023_ = lean_array_get_size(v_ncRings_1022_);
lean_dec_ref(v_ncRings_1022_);
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
v___x_1026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17);
v___x_1027_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1023_);
lean_ctor_set(v___x_1027_, 1, v_type_973_);
lean_ctor_set(v___x_1027_, 2, v_a_986_);
lean_ctor_set(v___x_1027_, 3, v_val_998_);
lean_ctor_set(v___x_1027_, 4, v___x_1006_);
lean_ctor_set(v___x_1027_, 5, v_a_1019_);
lean_ctor_set(v___x_1027_, 6, v___x_1024_);
lean_ctor_set(v___x_1027_, 7, v___x_1024_);
lean_ctor_set(v___x_1027_, 8, v___x_1024_);
lean_ctor_set(v___x_1027_, 9, v___x_1024_);
lean_ctor_set(v___x_1027_, 10, v___x_1024_);
lean_ctor_set(v___x_1027_, 11, v___x_1024_);
lean_ctor_set(v___x_1027_, 12, v___x_1024_);
lean_ctor_set(v___x_1027_, 13, v___x_1024_);
lean_ctor_set(v___x_1027_, 14, v___x_1025_);
lean_ctor_set(v___x_1027_, 15, v___x_1026_);
lean_ctor_set(v___x_1027_, 16, v___x_1026_);
v___f_1028_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
v___x_1029_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1030_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1029_, v___f_1028_, v___y_1008_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1040_; 
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v___x_1030_, 0);
lean_dec(v_unused_1041_);
v___x_1032_ = v___x_1030_;
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
else
{
lean_dec(v___x_1030_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1023_);
v___x_1035_ = v___x_1000_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1023_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1035_);
v___x_1037_ = v___x_1032_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_del_object(v___x_1000_);
v_a_1042_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1030_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1030_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1019_);
lean_dec_ref(v___x_1006_);
lean_del_object(v___x_1000_);
lean_dec(v_val_998_);
lean_dec(v_a_986_);
lean_dec_ref(v_type_973_);
v_a_1050_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1020_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1020_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v___x_1006_);
lean_del_object(v___x_1000_);
lean_dec(v_val_998_);
lean_dec(v_a_986_);
lean_dec_ref(v_type_973_);
v_a_1058_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1018_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1018_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
lean_dec(v_a_993_);
lean_dec_ref(v___x_989_);
lean_dec(v_a_986_);
lean_dec_ref(v_type_973_);
v___x_1091_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1091_);
v___x_1093_ = v___x_995_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v___x_989_);
lean_dec(v_a_986_);
lean_dec_ref(v_type_973_);
v_a_1096_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_992_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_992_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v_type_973_);
v_a_1104_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_985_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_985_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___boxed(lean_object* v_type_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec(v_a_1113_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(lean_object* v_type_1125_, lean_object* v_a_1126_, lean_object* v_s_1127_){
_start:
{
lean_object* v_rings_1128_; lean_object* v_typeIdOf_1129_; lean_object* v_exprToRingId_1130_; lean_object* v_semirings_1131_; lean_object* v_stypeIdOf_1132_; lean_object* v_exprToSemiringId_1133_; lean_object* v_ncRings_1134_; lean_object* v_exprToNCRingId_1135_; lean_object* v_nctypeIdOf_1136_; lean_object* v_ncSemirings_1137_; lean_object* v_exprToNCSemiringId_1138_; lean_object* v_ncstypeIdOf_1139_; lean_object* v_steps_1140_; uint8_t v_reportedMaxDegreeIssue_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1149_; 
v_rings_1128_ = lean_ctor_get(v_s_1127_, 0);
v_typeIdOf_1129_ = lean_ctor_get(v_s_1127_, 1);
v_exprToRingId_1130_ = lean_ctor_get(v_s_1127_, 2);
v_semirings_1131_ = lean_ctor_get(v_s_1127_, 3);
v_stypeIdOf_1132_ = lean_ctor_get(v_s_1127_, 4);
v_exprToSemiringId_1133_ = lean_ctor_get(v_s_1127_, 5);
v_ncRings_1134_ = lean_ctor_get(v_s_1127_, 6);
v_exprToNCRingId_1135_ = lean_ctor_get(v_s_1127_, 7);
v_nctypeIdOf_1136_ = lean_ctor_get(v_s_1127_, 8);
v_ncSemirings_1137_ = lean_ctor_get(v_s_1127_, 9);
v_exprToNCSemiringId_1138_ = lean_ctor_get(v_s_1127_, 10);
v_ncstypeIdOf_1139_ = lean_ctor_get(v_s_1127_, 11);
v_steps_1140_ = lean_ctor_get(v_s_1127_, 12);
v_reportedMaxDegreeIssue_1141_ = lean_ctor_get_uint8(v_s_1127_, sizeof(void*)*13);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_s_1127_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1143_ = v_s_1127_;
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_steps_1140_);
lean_inc(v_ncstypeIdOf_1139_);
lean_inc(v_exprToNCSemiringId_1138_);
lean_inc(v_ncSemirings_1137_);
lean_inc(v_nctypeIdOf_1136_);
lean_inc(v_exprToNCRingId_1135_);
lean_inc(v_ncRings_1134_);
lean_inc(v_exprToSemiringId_1133_);
lean_inc(v_stypeIdOf_1132_);
lean_inc(v_semirings_1131_);
lean_inc(v_exprToRingId_1130_);
lean_inc(v_typeIdOf_1129_);
lean_inc(v_rings_1128_);
lean_dec(v_s_1127_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_nctypeIdOf_1136_, v_type_1125_, v_a_1126_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 8, v___x_1145_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_rings_1128_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_typeIdOf_1129_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_exprToRingId_1130_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_semirings_1131_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_stypeIdOf_1132_);
lean_ctor_set(v_reuseFailAlloc_1148_, 5, v_exprToSemiringId_1133_);
lean_ctor_set(v_reuseFailAlloc_1148_, 6, v_ncRings_1134_);
lean_ctor_set(v_reuseFailAlloc_1148_, 7, v_exprToNCRingId_1135_);
lean_ctor_set(v_reuseFailAlloc_1148_, 8, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1148_, 9, v_ncSemirings_1137_);
lean_ctor_set(v_reuseFailAlloc_1148_, 10, v_exprToNCSemiringId_1138_);
lean_ctor_set(v_reuseFailAlloc_1148_, 11, v_ncstypeIdOf_1139_);
lean_ctor_set(v_reuseFailAlloc_1148_, 12, v_steps_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1148_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1141_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object* v_type_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1151_, v_a_1159_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1194_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1194_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1194_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_nctypeIdOf_1167_; lean_object* v___x_1168_; 
v_nctypeIdOf_1167_ = lean_ctor_get(v_a_1163_, 8);
lean_inc_ref(v_nctypeIdOf_1167_);
lean_dec(v_a_1163_);
v___x_1168_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_nctypeIdOf_1167_, v_type_1150_);
lean_dec_ref(v_nctypeIdOf_1167_);
if (lean_obj_tag(v___x_1168_) == 1)
{
lean_object* v_val_1169_; lean_object* v___x_1171_; 
lean_dec_ref(v_type_1150_);
v_val_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_val_1169_);
lean_dec_ref(v___x_1168_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v_val_1169_);
v___x_1171_ = v___x_1165_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_val_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
else
{
lean_object* v___x_1173_; 
lean_dec(v___x_1168_);
lean_del_object(v___x_1165_);
lean_inc_ref(v_type_1150_);
v___x_1173_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc_n(v_a_1174_, 2);
lean_dec_ref(v___x_1173_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1175_, 0, v_type_1150_);
lean_closure_set(v___f_1175_, 1, v_a_1174_);
v___x_1176_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1177_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1176_, v___f_1175_, v_a_1151_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v___x_1177_, 0);
lean_dec(v_unused_1185_);
v___x_1179_ = v___x_1177_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_dec(v___x_1177_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v_a_1174_);
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1174_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_a_1174_);
v_a_1186_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1177_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1177_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_dec_ref(v_type_1150_);
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref(v_type_1150_);
v_a_1195_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1162_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1162_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___boxed(lean_object* v_type_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec(v_a_1204_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(lean_object* v_semiringId_1216_, lean_object* v_s_1217_){
_start:
{
lean_object* v_toRing_1218_; lean_object* v_invFn_x3f_1219_; lean_object* v_commSemiringInst_1220_; lean_object* v_commRingInst_1221_; lean_object* v_noZeroDivInst_x3f_1222_; lean_object* v_fieldInst_x3f_1223_; lean_object* v_powIdentityInst_x3f_1224_; lean_object* v_denoteEntries_1225_; lean_object* v_nextId_1226_; lean_object* v_steps_1227_; lean_object* v_queue_1228_; lean_object* v_basis_1229_; lean_object* v_diseqs_1230_; uint8_t v_recheck_1231_; lean_object* v_invSet_1232_; lean_object* v_powIdentityVarCount_1233_; lean_object* v_numEq0_x3f_1234_; uint8_t v_numEq0Updated_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1243_; 
v_toRing_1218_ = lean_ctor_get(v_s_1217_, 0);
v_invFn_x3f_1219_ = lean_ctor_get(v_s_1217_, 1);
v_commSemiringInst_1220_ = lean_ctor_get(v_s_1217_, 3);
v_commRingInst_1221_ = lean_ctor_get(v_s_1217_, 4);
v_noZeroDivInst_x3f_1222_ = lean_ctor_get(v_s_1217_, 5);
v_fieldInst_x3f_1223_ = lean_ctor_get(v_s_1217_, 6);
v_powIdentityInst_x3f_1224_ = lean_ctor_get(v_s_1217_, 7);
v_denoteEntries_1225_ = lean_ctor_get(v_s_1217_, 8);
v_nextId_1226_ = lean_ctor_get(v_s_1217_, 9);
v_steps_1227_ = lean_ctor_get(v_s_1217_, 10);
v_queue_1228_ = lean_ctor_get(v_s_1217_, 11);
v_basis_1229_ = lean_ctor_get(v_s_1217_, 12);
v_diseqs_1230_ = lean_ctor_get(v_s_1217_, 13);
v_recheck_1231_ = lean_ctor_get_uint8(v_s_1217_, sizeof(void*)*17);
v_invSet_1232_ = lean_ctor_get(v_s_1217_, 14);
v_powIdentityVarCount_1233_ = lean_ctor_get(v_s_1217_, 15);
v_numEq0_x3f_1234_ = lean_ctor_get(v_s_1217_, 16);
v_numEq0Updated_1235_ = lean_ctor_get_uint8(v_s_1217_, sizeof(void*)*17 + 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_s_1217_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_s_1217_, 2);
lean_dec(v_unused_1244_);
v___x_1237_ = v_s_1217_;
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_numEq0_x3f_1234_);
lean_inc(v_powIdentityVarCount_1233_);
lean_inc(v_invSet_1232_);
lean_inc(v_diseqs_1230_);
lean_inc(v_basis_1229_);
lean_inc(v_queue_1228_);
lean_inc(v_steps_1227_);
lean_inc(v_nextId_1226_);
lean_inc(v_denoteEntries_1225_);
lean_inc(v_powIdentityInst_x3f_1224_);
lean_inc(v_fieldInst_x3f_1223_);
lean_inc(v_noZeroDivInst_x3f_1222_);
lean_inc(v_commRingInst_1221_);
lean_inc(v_commSemiringInst_1220_);
lean_inc(v_invFn_x3f_1219_);
lean_inc(v_toRing_1218_);
lean_dec(v_s_1217_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_semiringId_1216_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 2, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_toRing_1218_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_invFn_x3f_1219_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_commSemiringInst_1220_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_commRingInst_1221_);
lean_ctor_set(v_reuseFailAlloc_1242_, 5, v_noZeroDivInst_x3f_1222_);
lean_ctor_set(v_reuseFailAlloc_1242_, 6, v_fieldInst_x3f_1223_);
lean_ctor_set(v_reuseFailAlloc_1242_, 7, v_powIdentityInst_x3f_1224_);
lean_ctor_set(v_reuseFailAlloc_1242_, 8, v_denoteEntries_1225_);
lean_ctor_set(v_reuseFailAlloc_1242_, 9, v_nextId_1226_);
lean_ctor_set(v_reuseFailAlloc_1242_, 10, v_steps_1227_);
lean_ctor_set(v_reuseFailAlloc_1242_, 11, v_queue_1228_);
lean_ctor_set(v_reuseFailAlloc_1242_, 12, v_basis_1229_);
lean_ctor_set(v_reuseFailAlloc_1242_, 13, v_diseqs_1230_);
lean_ctor_set(v_reuseFailAlloc_1242_, 14, v_invSet_1232_);
lean_ctor_set(v_reuseFailAlloc_1242_, 15, v_powIdentityVarCount_1233_);
lean_ctor_set(v_reuseFailAlloc_1242_, 16, v_numEq0_x3f_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*17, v_recheck_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*17 + 1, v_numEq0Updated_1235_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(lean_object* v_ringId_1245_, lean_object* v_semiringId_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v___f_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___f_1249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1249_, 0, v_semiringId_1246_);
v___x_1250_ = 0;
v___x_1251_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1251_, 0, v_ringId_1245_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*1, v___x_1250_);
v___x_1252_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1249_, v___x_1251_, v_a_1247_);
lean_dec_ref(v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(lean_object* v_ringId_1253_, lean_object* v_semiringId_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_1253_, v_semiringId_1254_, v_a_1255_);
lean_dec(v_a_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(lean_object* v_ringId_1258_, lean_object* v_semiringId_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_1258_, v_semiringId_1259_, v_a_1260_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(lean_object* v_ringId_1272_, lean_object* v_semiringId_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(v_ringId_1272_, v_semiringId_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec(v_a_1274_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(lean_object* v___x_1286_, lean_object* v_s_1287_){
_start:
{
lean_object* v_rings_1288_; lean_object* v_typeIdOf_1289_; lean_object* v_exprToRingId_1290_; lean_object* v_semirings_1291_; lean_object* v_stypeIdOf_1292_; lean_object* v_exprToSemiringId_1293_; lean_object* v_ncRings_1294_; lean_object* v_exprToNCRingId_1295_; lean_object* v_nctypeIdOf_1296_; lean_object* v_ncSemirings_1297_; lean_object* v_exprToNCSemiringId_1298_; lean_object* v_ncstypeIdOf_1299_; lean_object* v_steps_1300_; uint8_t v_reportedMaxDegreeIssue_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1309_; 
v_rings_1288_ = lean_ctor_get(v_s_1287_, 0);
v_typeIdOf_1289_ = lean_ctor_get(v_s_1287_, 1);
v_exprToRingId_1290_ = lean_ctor_get(v_s_1287_, 2);
v_semirings_1291_ = lean_ctor_get(v_s_1287_, 3);
v_stypeIdOf_1292_ = lean_ctor_get(v_s_1287_, 4);
v_exprToSemiringId_1293_ = lean_ctor_get(v_s_1287_, 5);
v_ncRings_1294_ = lean_ctor_get(v_s_1287_, 6);
v_exprToNCRingId_1295_ = lean_ctor_get(v_s_1287_, 7);
v_nctypeIdOf_1296_ = lean_ctor_get(v_s_1287_, 8);
v_ncSemirings_1297_ = lean_ctor_get(v_s_1287_, 9);
v_exprToNCSemiringId_1298_ = lean_ctor_get(v_s_1287_, 10);
v_ncstypeIdOf_1299_ = lean_ctor_get(v_s_1287_, 11);
v_steps_1300_ = lean_ctor_get(v_s_1287_, 12);
v_reportedMaxDegreeIssue_1301_ = lean_ctor_get_uint8(v_s_1287_, sizeof(void*)*13);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_s_1287_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1303_ = v_s_1287_;
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_steps_1300_);
lean_inc(v_ncstypeIdOf_1299_);
lean_inc(v_exprToNCSemiringId_1298_);
lean_inc(v_ncSemirings_1297_);
lean_inc(v_nctypeIdOf_1296_);
lean_inc(v_exprToNCRingId_1295_);
lean_inc(v_ncRings_1294_);
lean_inc(v_exprToSemiringId_1293_);
lean_inc(v_stypeIdOf_1292_);
lean_inc(v_semirings_1291_);
lean_inc(v_exprToRingId_1290_);
lean_inc(v_typeIdOf_1289_);
lean_inc(v_rings_1288_);
lean_dec(v_s_1287_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_array_push(v_semirings_1291_, v___x_1286_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 3, v___x_1305_);
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_rings_1288_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_typeIdOf_1289_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_exprToRingId_1290_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v_stypeIdOf_1292_);
lean_ctor_set(v_reuseFailAlloc_1308_, 5, v_exprToSemiringId_1293_);
lean_ctor_set(v_reuseFailAlloc_1308_, 6, v_ncRings_1294_);
lean_ctor_set(v_reuseFailAlloc_1308_, 7, v_exprToNCRingId_1295_);
lean_ctor_set(v_reuseFailAlloc_1308_, 8, v_nctypeIdOf_1296_);
lean_ctor_set(v_reuseFailAlloc_1308_, 9, v_ncSemirings_1297_);
lean_ctor_set(v_reuseFailAlloc_1308_, 10, v_exprToNCSemiringId_1298_);
lean_ctor_set(v_reuseFailAlloc_1308_, 11, v_ncstypeIdOf_1299_);
lean_ctor_set(v_reuseFailAlloc_1308_, 12, v_steps_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1301_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_ref_1316_; lean_object* v___x_1317_; lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1326_; 
v_ref_1316_ = lean_ctor_get(v___y_1313_, 5);
v___x_1317_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_inc(v_ref_1316_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_ref_1316_);
lean_ctor_set(v___x_1322_, 1, v_a_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 1);
lean_ctor_set(v___x_1320_, 0, v___x_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8));
v___x_1357_ = l_Lean_stringToMessageData(v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(lean_object* v_type_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; 
lean_inc_ref(v_type_1358_);
v___x_1370_ = l_Lean_Meta_getDecLevel(v_type_1358_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_n(v_a_1371_, 2);
lean_dec_ref(v___x_1370_);
v___x_1372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1));
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1371_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
lean_inc_ref(v___x_1374_);
v___x_1375_ = l_Lean_mkConst(v___x_1372_, v___x_1374_);
lean_inc_ref(v_type_1358_);
v___x_1376_ = l_Lean_Expr_app___override(v___x_1375_, v_type_1358_);
v___x_1377_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1376_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1472_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1472_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1472_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
if (lean_obj_tag(v_a_1378_) == 1)
{
lean_object* v_val_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_del_object(v___x_1380_);
v_val_1382_ = lean_ctor_get(v_a_1378_, 0);
lean_inc_n(v_val_1382_, 2);
lean_dec_ref(v_a_1378_);
v___x_1383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2));
lean_inc_ref(v___x_1374_);
v___x_1384_ = l_Lean_mkConst(v___x_1383_, v___x_1374_);
lean_inc_ref_n(v_type_1358_, 2);
v___x_1385_ = l_Lean_mkAppB(v___x_1384_, v_type_1358_, v_val_1382_);
v___x_1386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5));
v___x_1387_ = l_Lean_mkConst(v___x_1386_, v___x_1374_);
lean_inc_ref(v___x_1385_);
v___x_1388_ = l_Lean_mkAppB(v___x_1387_, v_type_1358_, v___x_1385_);
v___x_1389_ = l_Lean_Meta_Sym_canon(v___x_1388_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1390_, v_a_1364_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_n(v_a_1392_, 2);
lean_dec_ref(v___x_1391_);
v___x_1393_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_a_1392_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
if (lean_obj_tag(v_a_1394_) == 1)
{
lean_object* v_val_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_a_1392_);
v_val_1395_ = lean_ctor_get(v_a_1394_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_a_1394_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1397_ = v_a_1394_;
v_isShared_1398_ = v_isSharedCheck_1447_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_val_1395_);
lean_dec(v_a_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1447_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1359_, v_a_1367_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v_semirings_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___f_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref(v___x_1399_);
v_semirings_1401_ = lean_ctor_get(v_a_1400_, 3);
lean_inc_ref(v_semirings_1401_);
lean_dec(v_a_1400_);
v___x_1402_ = lean_array_get_size(v_semirings_1401_);
lean_dec_ref(v_semirings_1401_);
v___x_1403_ = lean_box(0);
v___x_1404_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
v___x_1405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
v___x_1406_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1402_);
lean_ctor_set(v___x_1406_, 1, v_type_1358_);
lean_ctor_set(v___x_1406_, 2, v_a_1371_);
lean_ctor_set(v___x_1406_, 3, v___x_1385_);
lean_ctor_set(v___x_1406_, 4, v___x_1403_);
lean_ctor_set(v___x_1406_, 5, v___x_1403_);
lean_ctor_set(v___x_1406_, 6, v___x_1403_);
lean_ctor_set(v___x_1406_, 7, v___x_1403_);
lean_ctor_set(v___x_1406_, 8, v___x_1404_);
lean_ctor_set(v___x_1406_, 9, v___x_1405_);
lean_ctor_set(v___x_1406_, 10, v___x_1404_);
lean_inc(v_val_1395_);
v___x_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v_val_1395_);
lean_ctor_set(v___x_1407_, 2, v_val_1382_);
lean_ctor_set(v___x_1407_, 3, v___x_1403_);
lean_ctor_set(v___x_1407_, 4, v___x_1403_);
v___f_1408_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1408_, 0, v___x_1407_);
v___x_1409_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1410_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1409_, v___f_1408_, v_a_1359_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1411_; 
lean_dec_ref(v___x_1410_);
v___x_1411_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_val_1395_, v___x_1402_, v_a_1359_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1421_; 
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1411_, 0);
lean_dec(v_unused_1422_);
v___x_1413_ = v___x_1411_;
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
else
{
lean_dec(v___x_1411_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1402_);
v___x_1416_ = v___x_1397_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1402_);
v___x_1416_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1416_);
v___x_1418_ = v___x_1413_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_del_object(v___x_1397_);
v_a_1423_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1411_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1411_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_del_object(v___x_1397_);
lean_dec(v_val_1395_);
v_a_1431_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1410_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1410_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_del_object(v___x_1397_);
lean_dec(v_val_1395_);
lean_dec_ref(v___x_1385_);
lean_dec(v_val_1382_);
lean_dec(v_a_1371_);
lean_dec_ref(v_type_1358_);
v_a_1439_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1399_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1399_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec(v_a_1394_);
lean_dec_ref(v___x_1385_);
lean_dec(v_val_1382_);
lean_dec(v_a_1371_);
lean_dec_ref(v_type_1358_);
v___x_1448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9);
v___x_1449_ = l_Lean_indentExpr(v_a_1392_);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v___x_1450_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
return v___x_1451_;
}
}
else
{
lean_dec(v_a_1392_);
lean_dec_ref(v___x_1385_);
lean_dec(v_val_1382_);
lean_dec(v_a_1371_);
lean_dec_ref(v_type_1358_);
return v___x_1393_;
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref(v___x_1385_);
lean_dec(v_val_1382_);
lean_dec(v_a_1371_);
lean_dec_ref(v_type_1358_);
v_a_1452_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1391_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1391_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v___x_1385_);
lean_dec(v_val_1382_);
lean_dec(v_a_1371_);
lean_dec_ref(v_type_1358_);
v_a_1460_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1389_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1389_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
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
lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec(v_a_1378_);
lean_dec_ref(v___x_1374_);
lean_dec(v_a_1371_);
lean_dec_ref(v_type_1358_);
v___x_1468_ = lean_box(0);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1468_);
v___x_1470_ = v___x_1380_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref(v___x_1374_);
lean_dec(v_a_1371_);
lean_dec_ref(v_type_1358_);
v_a_1473_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1377_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1377_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v_type_1358_);
v_a_1481_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1370_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1370_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec(v_a_1490_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_1502_, lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_1503_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_1516_, lean_object* v_msg_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(v_00_u03b1_1516_, v_msg_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1518_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(lean_object* v_type_1530_, lean_object* v_a_1531_, lean_object* v_s_1532_){
_start:
{
lean_object* v_rings_1533_; lean_object* v_typeIdOf_1534_; lean_object* v_exprToRingId_1535_; lean_object* v_semirings_1536_; lean_object* v_stypeIdOf_1537_; lean_object* v_exprToSemiringId_1538_; lean_object* v_ncRings_1539_; lean_object* v_exprToNCRingId_1540_; lean_object* v_nctypeIdOf_1541_; lean_object* v_ncSemirings_1542_; lean_object* v_exprToNCSemiringId_1543_; lean_object* v_ncstypeIdOf_1544_; lean_object* v_steps_1545_; uint8_t v_reportedMaxDegreeIssue_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1554_; 
v_rings_1533_ = lean_ctor_get(v_s_1532_, 0);
v_typeIdOf_1534_ = lean_ctor_get(v_s_1532_, 1);
v_exprToRingId_1535_ = lean_ctor_get(v_s_1532_, 2);
v_semirings_1536_ = lean_ctor_get(v_s_1532_, 3);
v_stypeIdOf_1537_ = lean_ctor_get(v_s_1532_, 4);
v_exprToSemiringId_1538_ = lean_ctor_get(v_s_1532_, 5);
v_ncRings_1539_ = lean_ctor_get(v_s_1532_, 6);
v_exprToNCRingId_1540_ = lean_ctor_get(v_s_1532_, 7);
v_nctypeIdOf_1541_ = lean_ctor_get(v_s_1532_, 8);
v_ncSemirings_1542_ = lean_ctor_get(v_s_1532_, 9);
v_exprToNCSemiringId_1543_ = lean_ctor_get(v_s_1532_, 10);
v_ncstypeIdOf_1544_ = lean_ctor_get(v_s_1532_, 11);
v_steps_1545_ = lean_ctor_get(v_s_1532_, 12);
v_reportedMaxDegreeIssue_1546_ = lean_ctor_get_uint8(v_s_1532_, sizeof(void*)*13);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_s_1532_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1548_ = v_s_1532_;
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_steps_1545_);
lean_inc(v_ncstypeIdOf_1544_);
lean_inc(v_exprToNCSemiringId_1543_);
lean_inc(v_ncSemirings_1542_);
lean_inc(v_nctypeIdOf_1541_);
lean_inc(v_exprToNCRingId_1540_);
lean_inc(v_ncRings_1539_);
lean_inc(v_exprToSemiringId_1538_);
lean_inc(v_stypeIdOf_1537_);
lean_inc(v_semirings_1536_);
lean_inc(v_exprToRingId_1535_);
lean_inc(v_typeIdOf_1534_);
lean_inc(v_rings_1533_);
lean_dec(v_s_1532_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_stypeIdOf_1537_, v_type_1530_, v_a_1531_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v___x_1550_);
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_rings_1533_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_typeIdOf_1534_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_exprToRingId_1535_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_semirings_1536_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 5, v_exprToSemiringId_1538_);
lean_ctor_set(v_reuseFailAlloc_1553_, 6, v_ncRings_1539_);
lean_ctor_set(v_reuseFailAlloc_1553_, 7, v_exprToNCRingId_1540_);
lean_ctor_set(v_reuseFailAlloc_1553_, 8, v_nctypeIdOf_1541_);
lean_ctor_set(v_reuseFailAlloc_1553_, 9, v_ncSemirings_1542_);
lean_ctor_set(v_reuseFailAlloc_1553_, 10, v_exprToNCSemiringId_1543_);
lean_ctor_set(v_reuseFailAlloc_1553_, 11, v_ncstypeIdOf_1544_);
lean_ctor_set(v_reuseFailAlloc_1553_, 12, v_steps_1545_);
lean_ctor_set_uint8(v_reuseFailAlloc_1553_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1546_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object* v_type_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1556_, v_a_1564_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1599_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1599_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1599_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_stypeIdOf_1572_; lean_object* v___x_1573_; 
v_stypeIdOf_1572_ = lean_ctor_get(v_a_1568_, 4);
lean_inc_ref(v_stypeIdOf_1572_);
lean_dec(v_a_1568_);
v___x_1573_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_stypeIdOf_1572_, v_type_1555_);
lean_dec_ref(v_stypeIdOf_1572_);
if (lean_obj_tag(v___x_1573_) == 1)
{
lean_object* v_val_1574_; lean_object* v___x_1576_; 
lean_dec_ref(v_type_1555_);
v_val_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_val_1574_);
lean_dec_ref(v___x_1573_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_val_1574_);
v___x_1576_ = v___x_1570_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_val_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
else
{
lean_object* v___x_1578_; 
lean_dec(v___x_1573_);
lean_del_object(v___x_1570_);
lean_inc_ref(v_type_1555_);
v___x_1578_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___f_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc_n(v_a_1579_, 2);
lean_dec_ref(v___x_1578_);
v___f_1580_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1580_, 0, v_type_1555_);
lean_closure_set(v___f_1580_, 1, v_a_1579_);
v___x_1581_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1582_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1581_, v___f_1580_, v_a_1556_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v___x_1582_, 0);
lean_dec(v_unused_1590_);
v___x_1584_ = v___x_1582_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v___x_1582_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v_a_1579_);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1579_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_a_1579_);
v_a_1591_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1582_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1582_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_dec_ref(v_type_1555_);
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v_type_1555_);
v_a_1600_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1567_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1567_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___boxed(lean_object* v_type_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_type_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec(v_a_1609_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(lean_object* v___x_1621_, lean_object* v_s_1622_){
_start:
{
lean_object* v_rings_1623_; lean_object* v_typeIdOf_1624_; lean_object* v_exprToRingId_1625_; lean_object* v_semirings_1626_; lean_object* v_stypeIdOf_1627_; lean_object* v_exprToSemiringId_1628_; lean_object* v_ncRings_1629_; lean_object* v_exprToNCRingId_1630_; lean_object* v_nctypeIdOf_1631_; lean_object* v_ncSemirings_1632_; lean_object* v_exprToNCSemiringId_1633_; lean_object* v_ncstypeIdOf_1634_; lean_object* v_steps_1635_; uint8_t v_reportedMaxDegreeIssue_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1644_; 
v_rings_1623_ = lean_ctor_get(v_s_1622_, 0);
v_typeIdOf_1624_ = lean_ctor_get(v_s_1622_, 1);
v_exprToRingId_1625_ = lean_ctor_get(v_s_1622_, 2);
v_semirings_1626_ = lean_ctor_get(v_s_1622_, 3);
v_stypeIdOf_1627_ = lean_ctor_get(v_s_1622_, 4);
v_exprToSemiringId_1628_ = lean_ctor_get(v_s_1622_, 5);
v_ncRings_1629_ = lean_ctor_get(v_s_1622_, 6);
v_exprToNCRingId_1630_ = lean_ctor_get(v_s_1622_, 7);
v_nctypeIdOf_1631_ = lean_ctor_get(v_s_1622_, 8);
v_ncSemirings_1632_ = lean_ctor_get(v_s_1622_, 9);
v_exprToNCSemiringId_1633_ = lean_ctor_get(v_s_1622_, 10);
v_ncstypeIdOf_1634_ = lean_ctor_get(v_s_1622_, 11);
v_steps_1635_ = lean_ctor_get(v_s_1622_, 12);
v_reportedMaxDegreeIssue_1636_ = lean_ctor_get_uint8(v_s_1622_, sizeof(void*)*13);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_s_1622_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1638_ = v_s_1622_;
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_steps_1635_);
lean_inc(v_ncstypeIdOf_1634_);
lean_inc(v_exprToNCSemiringId_1633_);
lean_inc(v_ncSemirings_1632_);
lean_inc(v_nctypeIdOf_1631_);
lean_inc(v_exprToNCRingId_1630_);
lean_inc(v_ncRings_1629_);
lean_inc(v_exprToSemiringId_1628_);
lean_inc(v_stypeIdOf_1627_);
lean_inc(v_semirings_1626_);
lean_inc(v_exprToRingId_1625_);
lean_inc(v_typeIdOf_1624_);
lean_inc(v_rings_1623_);
lean_dec(v_s_1622_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_array_push(v_ncSemirings_1632_, v___x_1621_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 9, v___x_1640_);
v___x_1642_ = v___x_1638_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_rings_1623_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_typeIdOf_1624_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_exprToRingId_1625_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_semirings_1626_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_stypeIdOf_1627_);
lean_ctor_set(v_reuseFailAlloc_1643_, 5, v_exprToSemiringId_1628_);
lean_ctor_set(v_reuseFailAlloc_1643_, 6, v_ncRings_1629_);
lean_ctor_set(v_reuseFailAlloc_1643_, 7, v_exprToNCRingId_1630_);
lean_ctor_set(v_reuseFailAlloc_1643_, 8, v_nctypeIdOf_1631_);
lean_ctor_set(v_reuseFailAlloc_1643_, 9, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1643_, 10, v_exprToNCSemiringId_1633_);
lean_ctor_set(v_reuseFailAlloc_1643_, 11, v_ncstypeIdOf_1634_);
lean_ctor_set(v_reuseFailAlloc_1643_, 12, v_steps_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1636_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(lean_object* v_type_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; 
lean_inc_ref(v_type_1650_);
v___x_1657_ = l_Lean_Meta_getDecLevel(v_type_1650_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc_n(v_a_1658_, 2);
lean_dec_ref(v___x_1657_);
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1));
v___x_1660_ = lean_box(0);
v___x_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1661_, 0, v_a_1658_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = l_Lean_mkConst(v___x_1659_, v___x_1661_);
lean_inc_ref(v_type_1650_);
v___x_1663_ = l_Lean_Expr_app___override(v___x_1662_, v_type_1650_);
v___x_1664_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1663_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1716_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1716_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1716_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
if (lean_obj_tag(v_a_1665_) == 1)
{
lean_object* v_val_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1711_; 
lean_del_object(v___x_1667_);
v_val_1669_ = lean_ctor_get(v_a_1665_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_a_1665_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1671_ = v_a_1665_;
v_isShared_1672_ = v_isSharedCheck_1711_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_val_1669_);
lean_dec(v_a_1665_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1711_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1651_, v_a_1654_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v_ncSemirings_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___f_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref(v___x_1673_);
v_ncSemirings_1675_ = lean_ctor_get(v_a_1674_, 9);
lean_inc_ref(v_ncSemirings_1675_);
lean_dec(v_a_1674_);
v___x_1676_ = lean_array_get_size(v_ncSemirings_1675_);
lean_dec_ref(v_ncSemirings_1675_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
v___x_1679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
v___x_1680_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1676_);
lean_ctor_set(v___x_1680_, 1, v_type_1650_);
lean_ctor_set(v___x_1680_, 2, v_a_1658_);
lean_ctor_set(v___x_1680_, 3, v_val_1669_);
lean_ctor_set(v___x_1680_, 4, v___x_1677_);
lean_ctor_set(v___x_1680_, 5, v___x_1677_);
lean_ctor_set(v___x_1680_, 6, v___x_1677_);
lean_ctor_set(v___x_1680_, 7, v___x_1677_);
lean_ctor_set(v___x_1680_, 8, v___x_1678_);
lean_ctor_set(v___x_1680_, 9, v___x_1679_);
lean_ctor_set(v___x_1680_, 10, v___x_1678_);
v___f_1681_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1681_, 0, v___x_1680_);
v___x_1682_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1683_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1682_, v___f_1681_, v_a_1651_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1693_; 
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v___x_1683_, 0);
lean_dec(v_unused_1694_);
v___x_1685_ = v___x_1683_;
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
else
{
lean_dec(v___x_1683_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1676_);
v___x_1688_ = v___x_1671_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1676_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1688_);
v___x_1690_ = v___x_1685_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_del_object(v___x_1671_);
v_a_1695_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1683_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1683_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_del_object(v___x_1671_);
lean_dec(v_val_1669_);
lean_dec(v_a_1658_);
lean_dec_ref(v_type_1650_);
v_a_1703_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1673_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1673_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
lean_dec(v_a_1665_);
lean_dec(v_a_1658_);
lean_dec_ref(v_type_1650_);
v___x_1712_ = lean_box(0);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1712_);
v___x_1714_ = v___x_1667_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1658_);
lean_dec_ref(v_type_1650_);
v_a_1717_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1664_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1664_);
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
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref(v_type_1650_);
v_a_1725_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1657_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1657_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___boxed(lean_object* v_type_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(lean_object* v_type_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_1741_, v_a_1742_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(v_type_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
lean_dec_ref(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec(v_a_1755_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(lean_object* v_type_1767_, lean_object* v_a_1768_, lean_object* v_s_1769_){
_start:
{
lean_object* v_rings_1770_; lean_object* v_typeIdOf_1771_; lean_object* v_exprToRingId_1772_; lean_object* v_semirings_1773_; lean_object* v_stypeIdOf_1774_; lean_object* v_exprToSemiringId_1775_; lean_object* v_ncRings_1776_; lean_object* v_exprToNCRingId_1777_; lean_object* v_nctypeIdOf_1778_; lean_object* v_ncSemirings_1779_; lean_object* v_exprToNCSemiringId_1780_; lean_object* v_ncstypeIdOf_1781_; lean_object* v_steps_1782_; uint8_t v_reportedMaxDegreeIssue_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1791_; 
v_rings_1770_ = lean_ctor_get(v_s_1769_, 0);
v_typeIdOf_1771_ = lean_ctor_get(v_s_1769_, 1);
v_exprToRingId_1772_ = lean_ctor_get(v_s_1769_, 2);
v_semirings_1773_ = lean_ctor_get(v_s_1769_, 3);
v_stypeIdOf_1774_ = lean_ctor_get(v_s_1769_, 4);
v_exprToSemiringId_1775_ = lean_ctor_get(v_s_1769_, 5);
v_ncRings_1776_ = lean_ctor_get(v_s_1769_, 6);
v_exprToNCRingId_1777_ = lean_ctor_get(v_s_1769_, 7);
v_nctypeIdOf_1778_ = lean_ctor_get(v_s_1769_, 8);
v_ncSemirings_1779_ = lean_ctor_get(v_s_1769_, 9);
v_exprToNCSemiringId_1780_ = lean_ctor_get(v_s_1769_, 10);
v_ncstypeIdOf_1781_ = lean_ctor_get(v_s_1769_, 11);
v_steps_1782_ = lean_ctor_get(v_s_1769_, 12);
v_reportedMaxDegreeIssue_1783_ = lean_ctor_get_uint8(v_s_1769_, sizeof(void*)*13);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_s_1769_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1785_ = v_s_1769_;
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_steps_1782_);
lean_inc(v_ncstypeIdOf_1781_);
lean_inc(v_exprToNCSemiringId_1780_);
lean_inc(v_ncSemirings_1779_);
lean_inc(v_nctypeIdOf_1778_);
lean_inc(v_exprToNCRingId_1777_);
lean_inc(v_ncRings_1776_);
lean_inc(v_exprToSemiringId_1775_);
lean_inc(v_stypeIdOf_1774_);
lean_inc(v_semirings_1773_);
lean_inc(v_exprToRingId_1772_);
lean_inc(v_typeIdOf_1771_);
lean_inc(v_rings_1770_);
lean_dec(v_s_1769_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_ncstypeIdOf_1781_, v_type_1767_, v_a_1768_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 11, v___x_1787_);
v___x_1789_ = v___x_1785_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_rings_1770_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_typeIdOf_1771_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_exprToRingId_1772_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_semirings_1773_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v_stypeIdOf_1774_);
lean_ctor_set(v_reuseFailAlloc_1790_, 5, v_exprToSemiringId_1775_);
lean_ctor_set(v_reuseFailAlloc_1790_, 6, v_ncRings_1776_);
lean_ctor_set(v_reuseFailAlloc_1790_, 7, v_exprToNCRingId_1777_);
lean_ctor_set(v_reuseFailAlloc_1790_, 8, v_nctypeIdOf_1778_);
lean_ctor_set(v_reuseFailAlloc_1790_, 9, v_ncSemirings_1779_);
lean_ctor_set(v_reuseFailAlloc_1790_, 10, v_exprToNCSemiringId_1780_);
lean_ctor_set(v_reuseFailAlloc_1790_, 11, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1790_, 12, v_steps_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1790_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1783_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object* v_type_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1793_, v_a_1796_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1831_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1831_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1831_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_ncstypeIdOf_1804_; lean_object* v___x_1805_; 
v_ncstypeIdOf_1804_ = lean_ctor_get(v_a_1800_, 11);
lean_inc_ref(v_ncstypeIdOf_1804_);
lean_dec(v_a_1800_);
v___x_1805_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_ncstypeIdOf_1804_, v_type_1792_);
lean_dec_ref(v_ncstypeIdOf_1804_);
if (lean_obj_tag(v___x_1805_) == 1)
{
lean_object* v_val_1806_; lean_object* v___x_1808_; 
lean_dec_ref(v_type_1792_);
v_val_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_val_1806_);
lean_dec_ref(v___x_1805_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v_val_1806_);
v___x_1808_ = v___x_1802_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_val_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
else
{
lean_object* v___x_1810_; 
lean_dec(v___x_1805_);
lean_del_object(v___x_1802_);
lean_inc_ref(v_type_1792_);
v___x_1810_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___f_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc_n(v_a_1811_, 2);
lean_dec_ref(v___x_1810_);
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1812_, 0, v_type_1792_);
lean_closure_set(v___f_1812_, 1, v_a_1811_);
v___x_1813_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1814_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1813_, v___f_1812_, v_a_1793_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v___x_1814_, 0);
lean_dec(v_unused_1822_);
v___x_1816_ = v___x_1814_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v___x_1814_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v_a_1811_);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1811_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_a_1811_);
v_a_1823_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1814_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1814_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_dec_ref(v_type_1792_);
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v_type_1792_);
v_a_1832_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1799_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1799_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___boxed(lean_object* v_type_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(lean_object* v_type_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_1848_, v_a_1849_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___boxed(lean_object* v_type_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(v_type_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec(v_a_1862_);
return v_res_1873_;
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
